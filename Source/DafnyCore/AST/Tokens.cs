
using System;
using System.Diagnostics.Contracts;
using System.IO;

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

  public IOrigin WithVal(string newVal) {
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

  public static RangeToken ToRange(this IOrigin token) {
    if (token is BoogieRangeOrigin boogieRangeToken) {
      return new RangeToken(boogieRangeToken.StartToken, boogieRangeToken.EndToken);
    }

    if (token is NestedOrigin nestedToken) {
      return ToRange(nestedToken.Outer);
    }
    return token as RangeToken ?? new RangeToken(token, token);
  }
}

public class BoogieRangeOrigin : OriginWrapper {
  // The wrapped token is the startTok
  public IOrigin StartToken { get; }
  public IOrigin EndToken { get; }

  /// <summary>
  /// If only a single position is used to refer to this piece of code, this position is the best
  /// </summary>
  public IOrigin Center { get; }

  // Used for range reporting
  public override string val => new(' ', Math.Max(EndToken.pos + EndToken.val.Length - pos, 1));

  public BoogieRangeOrigin(IOrigin startTok, IOrigin endTok, IOrigin center) : base(
    center ?? startTok) {
    StartToken = startTok;
    EndToken = endTok;
    Center = center;
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
  public IOrigin Outer { get { return WrappedToken; } }
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
  public QuantifiedVariableDomainOrigin(IOrigin wrappedToken)
    : base(wrappedToken) {
    Contract.Requires(wrappedToken != null);
  }

  public override string val {
    get { return WrappedToken.val; }
    set { WrappedToken.val = value; }
  }

  public override IOrigin WithVal(string newVal) {
    return new QuantifiedVariableDomainOrigin((WrappedToken.WithVal(newVal)));
  }
}

/// <summary>
/// A token wrapper used to produce better type checking errors
/// for quantified variables. See QuantifierVar.ExtractSingleRange()
/// </summary>
public class QuantifiedVariableRangeOrigin : OriginWrapper {
  public QuantifiedVariableRangeOrigin(IOrigin wrappedToken)
    : base(wrappedToken) {
    Contract.Requires(wrappedToken != null);
  }

  public override string val {
    get { return WrappedToken.val; }
    set { WrappedToken.val = value; }
  }

  public override IOrigin WithVal(string newVal) {
    return new QuantifiedVariableRangeOrigin(WrappedToken.WithVal(newVal));
  }
}
