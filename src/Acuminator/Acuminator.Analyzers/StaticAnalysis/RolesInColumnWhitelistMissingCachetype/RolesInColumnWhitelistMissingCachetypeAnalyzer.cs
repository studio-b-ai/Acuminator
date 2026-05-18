using System.Collections.Generic;
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

namespace Acuminator.Analyzers.StaticAnalysis.RolesInColumnWhitelistMissingCachetype;

/// <summary>
/// PX1123: Detects calls to <c>PXDatabase.Execute</c> that perform an
/// <c>INSERT INTO RolesInMember</c> or <c>INSERT INTO RolesInCache</c> with
/// an explicit column list that omits the <c>Cachetype</c> column.
///
/// <c>Cachetype</c> is a NOT NULL column on both <c>RolesInMember</c> and
/// <c>RolesInCache</c>; it does not exist on <c>RolesInGraph</c>.  An INSERT
/// into either table that names an explicit column list but omits <c>Cachetype</c>
/// will raise a SQL runtime error:
/// <code>Cannot insert the value NULL into column 'Cachetype', table '...'</code>
///
/// The fix is either to add <c>Cachetype</c> to the column list explicitly, or to
/// discover the columns dynamically via <c>INFORMATION_SCHEMA.COLUMNS</c> so that
/// unknown columns default to their schema-defined defaults rather than NULL.
///
/// Detection is per-INSERT: each INSERT into <c>RolesInMember</c> or
/// <c>RolesInCache</c> that has an explicit column list lacking <c>Cachetype</c>
/// is reported independently.  INSERTs without an explicit column list (for example,
/// <c>INSERT INTO RolesInMember SELECT ...</c>) are not flagged because the implicit
/// column ordering respects table defaults.  INSERTs into <c>RolesInGraph</c> are
/// never flagged because that table does not have a <c>Cachetype</c> column.
///
/// Comments (<c>--</c> line and <c>/* */</c> block) and string literals (<c>'...'</c>)
/// inside the SQL are stripped before matching so their contents do not produce
/// false positives or false negatives.
///
/// Known limitations (heuristic-based; full T-SQL parse would resolve them):
///   - Nested block comments and bracketed-identifier escape sequences
///     (<c>[a]]b]</c>) are not modeled.
///   - For interpolated strings with holes, literal segments are scanned;
///     a hole that stands in for a column name (for example, <c>$"INSERT INTO
///     RolesInMember ({columnList}) ..."</c>) is not modeled.
///   - Runtime-computed SQL (<c>StringBuilder</c>-concatenated, non-constant)
///     cannot be analyzed statically and is silently skipped.
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public class RolesInColumnWhitelistMissingCachetypeAnalyzer : PXDiagnosticAnalyzer
{
	private const string ExecuteMethodName = "Execute";

	private const string InterpolationHolePlaceholder = " __pxsb_hole__ ";

	/// <summary>
	/// Matches INSERT INTO RolesInMember or RolesInCache followed by an explicit
	/// column list in parentheses.
	/// Group 1: Member or Cache (to distinguish which table).
	/// Group 2: the column list text inside the parentheses.
	/// </summary>
	// Codex P2: accept SQL Server's common identifier forms:
	//   bare:              INSERT INTO RolesInMember (...)
	//   bracketed:         INSERT INTO [RolesInMember] (...)
	//   double-quoted:     INSERT INTO "RolesInMember" (...)
	//   schema-qualified:  INSERT INTO dbo.RolesInMember (...) | [dbo].[RolesInMember]
	private static readonly Regex InsertRolesInPattern = new(
		@"\bINSERT\s+INTO\s+(?:[\[""]?\w+[\]""]?\s*\.\s*)?[\[""]?RolesIn(Member|Cache)[\]""]?\s*\(([^)]+)\)",
		RegexOptions.IgnoreCase | RegexOptions.Compiled);

	/// <summary>
	/// Matches the Cachetype column name as a standalone token, accepting
	/// bare identifiers and bracket- or double-quote-enclosed variants.
	/// </summary>
	private static readonly Regex CachetypeTokenPattern = new(
		@"(?:^|,)\s*(?:\[Cachetype\]|""Cachetype""|Cachetype)(?:\s*,|\s*$)",
		RegexOptions.IgnoreCase | RegexOptions.Compiled);

	public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics =>
		ImmutableArray.Create(Descriptors.PX1123_RolesInColumnWhitelistMissingCachetype);

	public RolesInColumnWhitelistMissingCachetypeAnalyzer() : base() { }

	public RolesInColumnWhitelistMissingCachetypeAnalyzer(CodeAnalysisSettings codeAnalysisSettings) : base(codeAnalysisSettings) { }

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

		string? sqlText = TryGetStringValue(sqlArgument.Expression, syntaxContext.SemanticModel, syntaxContext.CancellationToken);
		if (sqlText is null)
			return;

		// Codex P3: report every offending INSERT in the SQL batch, not just the first.
		// If one Execute call has both a bad RolesInMember INSERT and a bad RolesInCache
		// INSERT, emit two diagnostics so the second isn't masked by fixing the first.
		int missingCount = CountInsertsWithMissingCachetype(sqlText);
		for (int i = 0; i < missingCount; i++)
		{
			syntaxContext.ReportDiagnosticWithSuppressionCheck(
				Diagnostic.Create(Descriptors.PX1123_RolesInColumnWhitelistMissingCachetype, invocation.GetLocation()),
				pxContext.CodeAnalysisSettings);
		}
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
	/// Scans the sanitized SQL for every INSERT INTO RolesInMember/RolesInCache
	/// with an explicit column list. Returns the count of INSERTs that omit
	/// <c>Cachetype</c>. Codex P3: caller reports one diagnostic per offending
	/// INSERT so multiple violations in the same SQL aren't masked.
	/// </summary>
	private static int CountInsertsWithMissingCachetype(string sql)
	{
		string sanitized = StripCommentsAndStringLiterals(sql);
		int missing = 0;

		foreach (Match m in InsertRolesInPattern.Matches(sanitized))
		{
			// Group 2 is the raw column list between the parentheses.
			string columnList = m.Groups[2].Value;

			if (!ColumnListContainsCachetype(columnList))
				missing++;
		}

		return missing;
	}

	/// <summary>
	/// Checks whether a comma-separated column list contains <c>Cachetype</c>
	/// as a standalone column token (case-insensitive, with optional bracket or
	/// double-quote delimiters).
	/// </summary>
	private static bool ColumnListContainsCachetype(string columnList)
	{
		// Split on commas and check each trimmed token.
		foreach (string rawToken in columnList.Split(','))
		{
			string token = rawToken.Trim();

			// Strip bracket or double-quote enclosure.
			if (token.Length >= 2 && token[0] == '[' && token[token.Length - 1] == ']')
				token = token.Substring(1, token.Length - 2).Trim();
			else if (token.Length >= 2 && token[0] == '"' && token[token.Length - 1] == '"')
				token = token.Substring(1, token.Length - 2).Trim();

			if (string.Equals(token, "Cachetype", System.StringComparison.OrdinalIgnoreCase))
				return true;
		}

		return false;
	}

	private static string? TryGetStringValue(ExpressionSyntax expression, SemanticModel semanticModel, System.Threading.CancellationToken cancellationToken)
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
	private static string StripCommentsAndStringLiterals(string sql)
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
