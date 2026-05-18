using System.Collections.Immutable;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

using Acuminator.Utilities;
using Acuminator.Utilities.DiagnosticSuppression;
using Acuminator.Utilities.Roslyn.Semantic;

using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;

namespace Acuminator.Analyzers.StaticAnalysis.MissingRoleGrantFallback;

/// <summary>
/// PX1122: Detects calls to <c>PXDatabase.Execute</c> that use an
/// <c>INSERT INTO RolesIn[Graph|Member|Cache] SELECT ... FROM RolesIn...</c>
/// pattern without a preceding pre-COUNT check on the source ScreenID and a
/// <c>Rolename='*'</c> direct-write fallback.
///
/// Acumatica customization plugins grant screen-level role access by copying
/// rows from a source (template) ScreenID in the RolesInGraph, RolesInMember,
/// and RolesInCache tables.  If the source ScreenID has zero rows in the target
/// tenant, the INSERT … SELECT silently null-ops and the intended grant never
/// lands.  The new screen is then inaccessible: Acumatica's OData endpoint
/// returns HTTP 404, and the screen does not appear in the access-rights tree.
///
/// The correct pattern does both of the following inside the same method body:
///   1. Pre-counts the source rows:
///        <c>SELECT COUNT(*) FROM RolesInGraph WHERE ScreenID = @source</c>
///   2. Falls back to a direct Rolename='*' write when the count is zero:
///        <c>INSERT INTO RolesInGraph … VALUES (@target, '*', …)</c>  OR
///        <c>... WHERE Rolename = '*'</c>
///
/// Detection is per-call: each unguarded INSERT-SELECT invocation is reported
/// independently.  Comments (<c>--</c> line and <c>/* */</c> block) and string
/// literals (<c>'...'</c>) inside the SQL are stripped before matching so their
/// contents do not produce false positives or false negatives.
///
/// Known limitation:
///   - If the pre-COUNT check and/or the fallback Rolename='*' write are
///     implemented in a separate helper method that is called from the same
///     method body, PX1122 may report a false positive because the heuristic
///     only scans string literals within the immediately enclosing method
///     declaration.  Suppress with an Acuminator comment for this pattern.
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public class MissingRoleGrantFallbackAnalyzer : PXDiagnosticAnalyzer
{
	private const string ExecuteMethodName = "Execute";

	private const string InterpolationHolePlaceholder = " __pxsb_hole__ ";

	/// <summary>
	/// Matches the anti-pattern: INSERT INTO RolesIn* SELECT ... FROM RolesIn*
	/// The [^;]* keeps both clauses within a single SQL statement.
	/// </summary>
	private static readonly Regex RolesInInsertSelectPattern = new(
		@"\bINSERT\s+INTO\s+RolesIn(?:Graph|Member|Cache)\b[^;]*?\bSELECT\b[^;]*?\bFROM\s+RolesIn(?:Graph|Member|Cache)\b",
		RegexOptions.IgnoreCase | RegexOptions.Compiled);

	/// <summary>
	/// Matches a pre-COUNT check on a RolesIn* source table.
	/// Accepts COUNT( or COUNT_BIG( anywhere in the SQL (case-insensitive).
	/// </summary>
	private static readonly Regex CountCheckPattern = new(
		@"\bCOUNT_?BIG?\s*\(",
		RegexOptions.IgnoreCase | RegexOptions.Compiled);

	/// <summary>
	/// Matches a direct Rolename='*' fallback grant.
	/// Accepts both single-quoted and escaped-quote variants.
	/// </summary>
	private static readonly Regex RolenameStarPattern = new(
		@"\bRolename\s*=\s*'\*'",
		RegexOptions.IgnoreCase | RegexOptions.Compiled);

	public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics =>
		ImmutableArray.Create(Descriptors.PX1122_MissingRoleGrantFallback);

	public MissingRoleGrantFallbackAnalyzer() : base() { }

	public MissingRoleGrantFallbackAnalyzer(CodeAnalysisSettings codeAnalysisSettings) : base(codeAnalysisSettings) { }

	protected override void AnalyzeCompilation(CompilationStartAnalysisContext compilationStartContext, PXContext pxContext)
	{
		compilationStartContext.RegisterSyntaxNodeAction(
			syntaxContext => AnalyzeInvocation(syntaxContext, pxContext),
			SyntaxKind.InvocationExpression);
	}

	private void AnalyzeInvocation(SyntaxNodeAnalysisContext syntaxContext, PXContext pxContext)
	{
		syntaxContext.CancellationToken.ThrowIfCancellationRequested();

		var invocation = (InvocationExpressionSyntax)syntaxContext.Node;

		if (!IsPxDatabaseExecuteCall(invocation, syntaxContext.SemanticModel, pxContext, syntaxContext.CancellationToken))
			return;

		var sqlArgument = invocation.ArgumentList.Arguments.FirstOrDefault();
		if (sqlArgument is null)
			return;

		string? sqlText = TryGetRgfStringValue(sqlArgument.Expression, syntaxContext.SemanticModel, syntaxContext.CancellationToken);
		if (sqlText is null)
			return;

		string sanitized = StripRgfCommentsAndStringLiterals(sqlText);

		if (!RolesInInsertSelectPattern.IsMatch(sanitized))
			return;

		// Walk up to the enclosing method declaration and collect all SQL-like
		// string literals it contains.  We look for both the COUNT guard and the
		// Rolename='*' fallback anywhere in that scope.
		var enclosingMethod = invocation.Ancestors()
			.OfType<MethodDeclarationSyntax>()
			.FirstOrDefault();

		if (enclosingMethod is null)
			return;

		bool hasCountCheck = false;
		bool hasRolenameStar = false;

		foreach (var node in enclosingMethod.DescendantNodes())
		{
			string? candidateText = null;

			if (node is LiteralExpressionSyntax literal &&
				literal.Kind() == SyntaxKind.StringLiteralExpression)
			{
				candidateText = literal.Token.ValueText;
			}
			else if (node is InterpolatedStringExpressionSyntax interp)
			{
				candidateText = TryGetRgfStringValue(interp, syntaxContext.SemanticModel, syntaxContext.CancellationToken);
			}

			if (candidateText is null)
				continue;

			string candidateSanitized = StripRgfCommentsAndStringLiterals(candidateText);

			if (!hasCountCheck && CountCheckPattern.IsMatch(candidateSanitized))
				hasCountCheck = true;

			if (!hasRolenameStar && RolenameStarPattern.IsMatch(candidateSanitized))
				hasRolenameStar = true;

			if (hasCountCheck && hasRolenameStar)
				break;
		}

		if (hasCountCheck && hasRolenameStar)
			return;

		syntaxContext.ReportDiagnosticWithSuppressionCheck(
			Diagnostic.Create(Descriptors.PX1122_MissingRoleGrantFallback, invocation.GetLocation()),
			pxContext.CodeAnalysisSettings);
	}

	private static bool IsPxDatabaseExecuteCall(
		InvocationExpressionSyntax invocation,
		SemanticModel semanticModel,
		PXContext pxContext,
		System.Threading.CancellationToken cancellationToken)
	{
		var symbolInfo = semanticModel.GetSymbolInfo(invocation, cancellationToken);
		if (symbolInfo.Symbol is not IMethodSymbol methodSymbol)
			return false;

		if (methodSymbol.Name != ExecuteMethodName)
			return false;

		var pxDatabaseType = pxContext.PXDatabase.Type;
		if (pxDatabaseType is null)
			return false;

		return SymbolEqualityComparer.Default.Equals(methodSymbol.ContainingType, pxDatabaseType);
	}

	/// <summary>
	/// Resolves a C# expression to its SQL string value.  Handles:
	/// <list type="bullet">
	///   <item>Compile-time string constants (including concatenation folded by Roslyn).</item>
	///   <item>Interpolated string expressions — literal segments are concatenated;
	///     interpolation holes are replaced with a whitespace placeholder so they
	///     cannot accidentally join two keywords into a false match.</item>
	/// </list>
	/// Returns <c>null</c> for non-constant, <c>StringBuilder</c>-composed, or other
	/// runtime-dynamic SQL that cannot be resolved statically.
	/// </summary>
	private static string? TryGetRgfStringValue(ExpressionSyntax expression, SemanticModel semanticModel, System.Threading.CancellationToken cancellationToken)
	{
		var constant = semanticModel.GetConstantValue(expression, cancellationToken);
		if (constant.HasValue && constant.Value is string constStr)
			return constStr;

		if (expression is InterpolatedStringExpressionSyntax interp)
		{
			var sb = new StringBuilder();
			bool any = false;
			foreach (var content in interp.Contents)
			{
				if (content is InterpolatedStringTextSyntax text)
				{
					sb.Append(text.TextToken.ValueText);
					any = true;
				}
				else
				{
					sb.Append(InterpolationHolePlaceholder);
					any = true;
				}
			}
			return any ? sb.ToString() : null;
		}

		return null;
	}

	/// <summary>
	/// Strips SQL comments (<c>--</c> line and <c>/* */</c> block) and string
	/// literals (<c>'...'</c>) from the SQL text, replacing stripped characters
	/// with spaces (preserving newlines) so that keyword offsets are not shifted
	/// and keywords embedded in comments/literals do not produce false matches.
	/// </summary>
	private static string StripRgfCommentsAndStringLiterals(string sql)
	{
		var sb = new StringBuilder(sql.Length);
		int i = 0;
		while (i < sql.Length)
		{
			char c = sql[i];

			// -- line comment
			if (c == '-' && i + 1 < sql.Length && sql[i + 1] == '-')
			{
				while (i < sql.Length && sql[i] != '\n')
				{
					sb.Append(' ');
					i++;
				}
				continue;
			}

			// /* block comment */
			if (c == '/' && i + 1 < sql.Length && sql[i + 1] == '*')
			{
				sb.Append("  ");
				i += 2;
				while (i + 1 < sql.Length && !(sql[i] == '*' && sql[i + 1] == '/'))
				{
					sb.Append(sql[i] == '\n' ? '\n' : ' ');
					i++;
				}
				if (i + 1 < sql.Length)
				{
					sb.Append("  ");
					i += 2;
				}
				continue;
			}

			// 'string literal' ('' is an escaped single-quote inside the literal)
			if (c == '\'')
			{
				sb.Append(' ');
				i++;
				while (i < sql.Length)
				{
					if (sql[i] == '\'')
					{
						if (i + 1 < sql.Length && sql[i + 1] == '\'')
						{
							sb.Append("  ");
							i += 2;
							continue;
						}
						sb.Append(' ');
						i++;
						break;
					}
					sb.Append(sql[i] == '\n' ? '\n' : ' ');
					i++;
				}
				continue;
			}

			sb.Append(c);
			i++;
		}
		return sb.ToString();
	}
}
