
using System;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny;

/// <summary>
/// Has one-indexed line and column fields
/// </summary>
public class Token : IOrigin {

  public Token peekedTokens; // Used only internally by Coco when the scanner "peeks" tokens. Normally null at the end of parsing
  public static readonly Token NoToken = new();
  public static readonly Token Cli = new(1, 1);
  public static readonly Token Ide = new(1, 1);
  public Token() : this(0, 0) { }

  public Token(int linenum, int colnum) {
    this.line = linenum;
    this.col = colnum;
    this.val = "";
  }

  public bool IsSourceToken => this != NoToken;
  public int kind { get; set; } // Used by coco, so we can't rename it to Kind

  public string ActualFilename => Filepath;
  public string Filepath => Uri?.LocalPath;
  public Uri Uri { get; set; }

  public int pos { get; set; } // Used by coco, so we can't rename it to Pos

  /// <summary>
  /// One-indexed
  /// </summary>
  public int col { get; set; } // Used by coco, so we can't rename it to Col

  /// <summary>
  /// One-indexed
  /// </summary>
  public int line { get; set; } // Used by coco, so we can't rename it to Line

  public string val { get; set; } // Used by coco, so we can't rename it to Val

  public string LeadingTrivia { get; set; } = "";

  public string TrailingTrivia { get; set; } = "";

  public Token Next { get; set; } // The next token

  public Token Prev { get; set; } // The previous token

  public bool IsValid => this.ActualFilename != null;

  public RangeToken To(Token end) => new(this, end);

  public bool IsMissingRange => true;

  public bool IsInherited(ModuleDefinition d) {
    return false;
  }

  public Token Center => this;
  public Token StartToken => this;  // TODO throw exception?
  public Token EndToken => this; // TODO throw exception?
  public bool ContainsRange => false;
  public string filename => Path.GetFileName(Filepath); // TODO rename or inline

  IOrigin IOrigin.WithVal(string val) {
    return WithVal(val);
  }

  public Token WithVal(string newVal) {
    return new Token {
      pos = pos,
      col = col,
      line = line,
      Prev = Prev,
      Next = Next,
      Uri = Uri,
      kind = kind,
      val = newVal
    };
  }

  public bool IsCopy => false;

  public int CompareTo(Boogie.IToken other) {
    if (line != other.line) {
      return line.CompareTo(other.line);
    }
    return col.CompareTo(other.col);
  }

  public override int GetHashCode() {
    return pos;
  }

  public override string ToString() {
    return $"'{val}': {Path.GetFileName(Filepath)}@{pos} - @{line}:{col}";
  }

  public int CompareTo(IOrigin other) {
    if (line != other.line) {
      return line.CompareTo(other.line);
    }
    return col.CompareTo(other.col);
  }
}

public static class TokenExtensions {

  public static RangeToken SingleTokenRange(this Token token) {
    return new RangeToken(token, token);
  }

  /// <summary>
  /// Gets the LSP range of the specified token.
  /// </summary>
  /// <param name="startToken">The token to get the range of.</param>
  /// <param name="endToken">An optional other token to get the end of the range of.</param>
  /// <returns>The LSP range of the token.</returns>
  public static Range ToLspRange(this IOrigin range) {
    return range.ToDafnyRange().ToLspRange();
  }

  public static DafnyRange ToDafnyRange(this IOrigin origin, bool includeTrailingWhitespace = false) {
    var startLine = origin.StartToken.line - 1;
    var startColumn = origin.StartToken.col - 1;
    var endLine = origin.EndToken.line - 1;
    int whitespaceOffset = 0;
    if (includeTrailingWhitespace) {
      string trivia = origin.EndToken.TrailingTrivia;
      // Don't want to remove newlines or comments -- just spaces and tabs
      while (whitespaceOffset < trivia.Length && (trivia[whitespaceOffset] == ' ' || trivia[whitespaceOffset] == '\t')) {
        whitespaceOffset++;
      }
    }

    var endColumn = origin.EndToken.col + (origin.InclusiveEnd ? origin.EndToken.val.Length : 0) + whitespaceOffset - 1;
    return new DafnyRange(
      new DafnyPosition(startLine, startColumn),
      new DafnyPosition(endLine, endColumn));
  }


  public static bool Contains(this IOrigin origin, IOrigin otherToken) {
    return origin.StartToken.Uri == otherToken.Uri &&
           origin.StartToken.pos <= otherToken.pos &&
           (origin.EndToken == null || otherToken.pos <= origin.EndToken.pos);
  }

  public static bool Intersects(this IOrigin origin, IOrigin other) {
    return !(other.EndToken.pos + other.EndToken.val.Length <= origin.StartToken.pos
             || origin.EndToken.pos + origin.EndToken.val.Length <= other.StartToken.pos);
  }

  public static string PrintOriginal(this IOrigin origin) {
    var token = origin.StartToken;
    var originalString = new StringBuilder();
    originalString.Append(token.val);
    while (token.Next != null && token.pos < origin.EndToken.pos) {
      originalString.Append(token.TrailingTrivia);
      token = token.Next;
      originalString.Append(token.LeadingTrivia);
      originalString.Append(token.val);
    }

    return originalString.ToString();
  }

  public static IOrigin MakeAutoGenerated(this IOrigin origin) { // TODO inline?
    return new AutoGeneratedOrigin(origin);
  }

  public static IOrigin MakeRefined(this IOrigin origin, ModuleDefinition module) { // TODO inline?
    return new RefinementOrigin(origin, module);
  }

  public static bool IsSet(this IOrigin token) => token.Uri != null;

  public static string TokenToString(this IOrigin tok, DafnyOptions options) {
    if (tok == Token.Cli) {
      return "CLI";
    }

    if (tok.Uri == null) {
      return $"({tok.line},{tok.col - 1})";
    }

    var currentDirectory = Directory.GetCurrentDirectory();
    string filename = tok.Uri.Scheme switch {
      "stdin" => "<stdin>",
      "transcript" => Path.GetFileName(tok.Filepath),
      _ => options.UseBaseNameForFileName
        ? Path.GetFileName(tok.Filepath)
        : (tok.Filepath.StartsWith(currentDirectory) ? Path.GetRelativePath(currentDirectory, tok.Filepath) : tok.Filepath)
    };

    return $"{filename}({tok.line},{tok.col - 1})";
  }

  public static IOrigin Unwrap(this IOrigin token) {
    if (token is OriginWrapper wrapper) {
      return Unwrap(wrapper.WrappedOrigin);
    }

    return token;
  }
}

public class BoogieRangeOrigin : OriginWrapper {
  // The wrapped token is the startTok
  public override Token StartToken { get; }
  public override Token EndToken { get; }

  /// <summary>
  /// If only a single position is used to refer to this piece of code, this position is the best
  /// </summary>
  public IOrigin Centerish { get; }

  // Used for range reporting
  public override string val => new(' ', Math.Max(EndToken.pos + EndToken.val.Length - pos, 1));

  public BoogieRangeOrigin(Token startTok, Token endTok, IOrigin center) : base(
    center ?? startTok) {
    StartToken = startTok;
    EndToken = endTok;
    Centerish = center;
  }

  public override IOrigin WithVal(string newVal) {
    return this;
  }

  public string PrintOriginal() {
    return new RangeToken(StartToken, EndToken).PrintOriginal();
  }
}

public class NestedOrigin : OriginWrapper {
  public NestedOrigin(IOrigin outer, IOrigin inner, string message = null)
    : base(outer) {
    Contract.Requires(outer != null);
    Contract.Requires(inner != null);
    Inner = inner;
    this.Message = message;
  }

  public override bool IsInherited(ModuleDefinition d) => Outer.IsInherited(d) || Inner.IsInherited(d);

  public IOrigin Outer => WrappedOrigin;
  public readonly IOrigin Inner;
  public readonly string Message;

  public override IOrigin WithVal(string newVal) {
    return this;
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

  public override IOrigin WithVal(string newVal) {
    return new QuantifiedVariableDomainOrigin((WrappedOrigin.WithVal(newVal)));
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

  public override IOrigin WithVal(string newVal) {
    return new QuantifiedVariableRangeOrigin(WrappedOrigin.WithVal(newVal));
  }
}
