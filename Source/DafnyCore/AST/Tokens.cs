using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Dafny;

public static class TokenExtensions {



  public static DafnyRange ToDafnyRange(this INode node, bool includeTrailingWhitespace = false) {
    var startLine = node.StartToken.line - 1;
    var startColumn = node.StartToken.col - 1;
    var endLine = node.EndToken.line - 1;
    int whitespaceOffset = 0;
    if (includeTrailingWhitespace) {
      string trivia = node.EndToken.TrailingTrivia;
      // Don't want to remove newlines or comments -- just spaces and tabs
      while (whitespaceOffset < trivia.Length && (trivia[whitespaceOffset] == ' ' || trivia[whitespaceOffset] == '\t')) {
        whitespaceOffset++;
      }
    }

    var inclusiveEnd = true; // node.InclusiveEnd
    var endColumn = node.EndToken.col + (inclusiveEnd ? node.EndToken.val.Length : 0) + whitespaceOffset - 1;
    return new DafnyRange(
      new DafnyPosition(startLine, startColumn),
      new DafnyPosition(endLine, endColumn));
  }

  public static IOrigin MakeAutoGenerated(this IOrigin origin) {
    return new AutoGeneratedOrigin(origin);
  }

  public static IOrigin MakeRefined(this IOrigin origin, ModuleDefinition module) {
    return new RefinementOrigin(origin, module);
  }

  public static bool Contains(this TokenRange container, Token otherToken) {
    return container.StartToken.Uri == otherToken.Uri &&
           container.StartToken.pos <= otherToken.pos &&
           (container.EndToken == null || otherToken.pos <= container.EndToken.pos);
  }

  public static bool Intersects(this TokenRange origin, TokenRange other) {
    return !(other.EndToken.pos + other.EndToken.val.Length <= origin.StartToken.pos
             || origin.EndToken.pos + origin.EndToken.val.Length <= other.StartToken.pos);
  }

  public static bool IsSet(this IOrigin token) => token.Uri != null;

  public static string OriginToString(this IOrigin origin, DafnyOptions options) {
    if (origin.line == Token.Cli.line) {
      return "CLI";
    }

    return origin.ReportingRange.ToFileRangeString(options);
  }

  public static string ToRangeString(this TokenRange range) {
    var start = range.StartToken;
    var end = range.EndToken;
    return $"({start.line}:{start.col - 1}-{end.line}:{end.col - 1 + range.EndLength})";
  }

  public static string ToFileRangeString(this TokenRange range, DafnyOptions options) {

    var start = range.StartToken;
    if (start.Uri == null) {
      if (options.Get(CommonOptionBag.PrintDiagnosticsRanges)) {
        return range.ToRangeString();
      }
      return $"({start.line},{start.col - 1})";
    }

    var currentDirectory = Directory.GetCurrentDirectory();
    string filename = range.Uri.Scheme switch {
      "stdin" => "<stdin>",
      "transcript" => Path.GetFileName(start.Filepath),
      _ => options.UseBaseNameForFileName
        ? Path.GetFileName(start.Filepath)
        : (start.Filepath.StartsWith(currentDirectory) ? Path.GetRelativePath(currentDirectory, start.Filepath) : start.Filepath)
    };

    if (options.Get(CommonOptionBag.PrintDiagnosticsRanges)) {
      return $"{filename}{range.ToRangeString()}";
    }
    return $"{filename}({start.line},{start.col - 1})";
  }
}

/// <summary>
/// A token wrapper used to produce better type checking errors
/// for quantified variables. See QuantifierVar.ExtractSingleRange()
/// </summary>
public class QuantifiedVariableDomainOrigin : OriginWrapper {
  public QuantifiedVariableDomainOrigin(IOrigin wrappedOrigin)
    : base(wrappedOrigin) {
    Contract.Requires(wrappedOrigin != null);
  }

  public override string val {
    get { return WrappedOrigin.val; }
    set { WrappedOrigin.val = value; }
  }
}

/// <summary>
/// A token wrapper used to produce better type checking errors
/// for quantified variables. See QuantifierVar.ExtractSingleRange()
/// </summary>
public class QuantifiedVariableRangeOrigin : OriginWrapper {
  public QuantifiedVariableRangeOrigin(IOrigin wrappedOrigin)
    : base(wrappedOrigin) {
    Contract.Requires(wrappedOrigin != null);
  }

  public override string val {
    get { return WrappedOrigin.val; }
    set { WrappedOrigin.val = value; }
  }
}
