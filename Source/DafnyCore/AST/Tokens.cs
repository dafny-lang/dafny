
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text;

namespace Microsoft.Dafny;

public interface IToken : Microsoft.Boogie.IToken {
  public RangeToken To(IToken end) => new RangeToken(this, end);

  /*
  int kind { get; set; }
  int pos { get; set; }
  int col { get; set; }
  int line { get; set; }
  string val { get; set; }
  bool IsValid { get; }*/
  string Boogie.IToken.filename {
    get => Uri?.AbsoluteUri;
    set => throw new NotSupportedException();
  }
  // string Boogie.IToken.filename {
  //   get => Uri?.LocalPath;
  //   set => Uri = new Uri(value);
  // }

  public string ActualFilename => Uri.LocalPath;
  string Filepath => Uri.LocalPath;

  Uri Uri { get; set; }

  /// <summary>
  /// TrailingTrivia contains everything after the token,
  /// until and including two newlines between which there is no commment
  /// All the remaining trivia is for the LeadingTrivia of the next token
  ///
  /// ```
  /// const /*for const*/ x /*for x*/ := /* for := */ 1/* for 1 */
  /// // for 1 again
  /// // for 1 again
  ///
  /// // Two newlines, now all the trivia is for var y
  /// // this line as well.
  /// var y := 2
  /// ```
  /// </summary>
  string TrailingTrivia { get; set; }
  string LeadingTrivia { get; set; }
  IToken Next { get; set; } // The next token
  IToken Prev { get; set; } // The previous token

  public IToken WithVal(string val);  // create a new token by setting the given val.
}

/// <summary>
/// Has one-indexed line and column fields
/// </summary>
public class Token : IToken {

  public Token peekedTokens; // Used only internally by Coco when the scanner "peeks" tokens. Normallly null at the end of parsing
  public static readonly IToken NoToken = new Token();

  static Token() {
    NoToken.Next = NoToken;
    NoToken.Prev = NoToken;
  }

  public Token() : this(0, 0) { }

  public Token(int linenum, int colnum) {
    this.line = linenum;
    this.col = colnum;
    this.val = "";
  }

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

  public IToken Next { get; set; } // The next token

  public IToken Prev { get; set; } // The previous token

  public bool IsValid => this.ActualFilename != null;

  public IToken WithVal(string newVal) {
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

  public override int GetHashCode() {
    return pos;
  }

  public override string ToString() {
    return $"{Filepath}@{pos} - @{line}:{col}";
  }
}

public abstract class TokenWrapper : IToken {

  public readonly IToken WrappedToken;
  protected TokenWrapper(IToken wrappedToken) {
    Contract.Requires(wrappedToken != null);
    WrappedToken = wrappedToken;
  }

  public abstract IToken WithVal(string newVal);

  public virtual int col {
    get { return WrappedToken.col; }
    set { WrappedToken.col = value; }
  }

  public string ActualFilename => WrappedToken.ActualFilename;

  public virtual string Filepath {
    get { return WrappedToken.Filepath; }
    set { WrappedToken.filename = value; } // TODO fix?
  }

  public Uri Uri {
    get => WrappedToken.Uri;
    set => WrappedToken.Uri = value;
  }

  public bool IsValid {
    get { return WrappedToken.IsValid; }
  }
  public int kind {
    get { return WrappedToken.kind; }
    set { WrappedToken.kind = value; }
  }
  public virtual int line {
    get { return WrappedToken.line; }
    set { WrappedToken.line = value; }
  }
  public virtual int pos {
    get { return WrappedToken.pos; }
    set { WrappedToken.pos = value; }
  }

  public virtual string val {
    get { return WrappedToken.val; }
    set { WrappedToken.val = value; }
  }
  public virtual string LeadingTrivia {
    get { return WrappedToken.LeadingTrivia; }
    set { throw new NotSupportedException(); }
  }
  public virtual string TrailingTrivia {
    get { return WrappedToken.TrailingTrivia; }
    set { throw new NotSupportedException(); }
  }
  public virtual IToken Next {
    get { return WrappedToken.Next; }
    set { throw new NotSupportedException(); }
  }
  public virtual IToken Prev {
    get { return WrappedToken.Prev; }
    set { throw new NotSupportedException(); }
  }
}

public static class TokenExtensions {


  public static string TokenToString(this IToken tok, DafnyOptions options) {
    if (tok.Uri == null) {
      return "Token has no URI" + tok;
    }
    
    var filename = tok.Uri.Scheme == "stdin"
      ? "<stdin>"
      : (options.UseBaseNameForFileName
        ? Path.GetFileName(tok.Filepath)
        : Path.GetRelativePath(Directory.GetCurrentDirectory(), tok.Filepath));
    return $"{filename}({tok.line},{tok.col - 1})";
  }

  public static RangeToken ToRange(this IToken token) {
    if (token is BoogieRangeToken boogieRangeToken) {
      return new RangeToken(boogieRangeToken.StartToken, boogieRangeToken.EndToken);
    }
    return token as RangeToken ?? new RangeToken(token, token);
  }
}

public class RangeToken : TokenWrapper {
  public IToken StartToken => WrappedToken;

  public IToken EndToken => endToken ?? StartToken;

  public bool InclusiveEnd => endToken != null;

  public DafnyRange ToDafnyRange(bool includeTrailingWhitespace = false) {
    var startLine = StartToken.line - 1;
    var startColumn = StartToken.col - 1;
    var endLine = EndToken.line - 1;
    int whitespaceOffset = 0;
    if (includeTrailingWhitespace) {
      string trivia = EndToken.TrailingTrivia;
      // Don't want to remove newlines or comments -- just spaces and tabs
      while (whitespaceOffset < trivia.Length && (trivia[whitespaceOffset] == ' ' || trivia[whitespaceOffset] == '\t')) {
        whitespaceOffset++;
      }
    }

    var endColumn = EndToken.col + (InclusiveEnd ? EndToken.val.Length : 0) + whitespaceOffset - 1;
    return new DafnyRange(
      new DafnyPosition(startLine, startColumn),
      new DafnyPosition(endLine, endColumn));
  }

  public RangeToken(IToken startToken, IToken endToken) : base(startToken) {
    this.endToken = endToken;
  }

  public string PrintOriginal() {
    var token = StartToken;
    var originalString = new StringBuilder();
    originalString.Append(token.val);
    while (token.Next != null && token.pos < EndToken.pos) {
      originalString.Append(token.TrailingTrivia);
      token = token.Next;
      originalString.Append(token.LeadingTrivia);
      originalString.Append(token.val);
    }

    return originalString.ToString();
  }

  public RangeToken MakeAutoGenerated() {
    return new RangeToken(new AutoGeneratedToken(StartToken), EndToken);
  }

  public RangeToken MakeRefined(ModuleDefinition module) {
    return new RangeToken(new RefinementToken(StartToken, module), EndToken);
  }

  // TODO rename to Generated, and Token.NoToken to Token.Generated, and remove AutoGeneratedToken.
  public static RangeToken NoToken = new(Token.NoToken, Token.NoToken);
  private readonly IToken endToken;

  public override IToken WithVal(string newVal) {
    throw new NotImplementedException();
  }

  public BoogieRangeToken ToToken() {
    return new BoogieRangeToken(StartToken, EndToken);
  }
}

public class BoogieRangeToken : TokenWrapper {
  // The wrapped token is the startTok
  public IToken StartToken => WrappedToken;
  public IToken EndToken { get; }

  // Used for range reporting
  public override string val => new string(' ', Math.Max(EndToken.pos + EndToken.val.Length - pos, 1));

  public BoogieRangeToken(IToken startTok, IToken endTok) : base(
    startTok) {
    this.EndToken = endTok;
  }

  public override IToken WithVal(string newVal) {
    return this;
  }

  public string PrintOriginal() {
    return new RangeToken(StartToken, EndToken).PrintOriginal();
  }
}

public class NestedToken : TokenWrapper {
  public NestedToken(IToken outer, IToken inner, string message = null)
    : base(outer) {
    Contract.Requires(outer != null);
    Contract.Requires(inner != null);
    Inner = inner;
    this.Message = message;
  }
  public IToken Outer { get { return WrappedToken; } }
  public readonly IToken Inner;
  public readonly string Message;

  public override IToken WithVal(string newVal) {
    return this;
  }
}

/// <summary>
/// A token wrapper used to produce better type checking errors
/// for quantified variables. See QuantifierVar.ExtractSingleRange()
/// </summary>
public class QuantifiedVariableDomainToken : TokenWrapper {
  public QuantifiedVariableDomainToken(IToken wrappedToken)
    : base(wrappedToken) {
    Contract.Requires(wrappedToken != null);
  }

  public override string val {
    get { return WrappedToken.val; }
    set { WrappedToken.val = value; }
  }

  public override IToken WithVal(string newVal) {
    return new QuantifiedVariableDomainToken((WrappedToken.WithVal(newVal)));
  }
}

/// <summary>
/// A token wrapper used to produce better type checking errors
/// for quantified variables. See QuantifierVar.ExtractSingleRange()
/// </summary>
public class QuantifiedVariableRangeToken : TokenWrapper {
  public QuantifiedVariableRangeToken(IToken wrappedToken)
    : base(wrappedToken) {
    Contract.Requires(wrappedToken != null);
  }

  public override string val {
    get { return WrappedToken.val; }
    set { WrappedToken.val = value; }
  }

  public override IToken WithVal(string newVal) {
    return new QuantifiedVariableRangeToken(WrappedToken.WithVal(newVal));
  }
}
