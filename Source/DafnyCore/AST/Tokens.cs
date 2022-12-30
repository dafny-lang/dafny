
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public interface IToken : Microsoft.Boogie.IToken {
  /*
  int kind { get; set; }
  int pos { get; set; }
  int col { get; set; }
  int line { get; set; }
  string val { get; set; }
  bool IsValid { get; }*/
  string Boogie.IToken.filename {
    get => Filename;
    set => Filename = value;
  }

  public string ActualFilename { get; }
  string Filename { get; set; }

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
public record Token : IToken {
  public Token peekedTokens; // Used only internally by Coco when the scanner "peeks" tokens. Normallly null at the end of parsing
  public static readonly IToken NoToken = (IToken)new Token();

  public Token() : this(0, 0) { }

  public Token(int linenum, int colnum) {
    this.line = linenum;
    this.col = colnum;
    this.val = "";
  }

  public int kind { get; set; } // Used by coco, so we can't rename it to Kind

  public string ActualFilename => Filename;
  public string Filename { get; set; }

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

  public IToken WithVal(string val) {
    return this with { val = val };
  }

  public override int GetHashCode() {
    return pos;
  }

  public override string ToString() {
    return $"{Filename}@{pos} - @{line}:{col}";
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

  public virtual string Filename {
    get { return WrappedToken.Filename; }
    set { WrappedToken.filename = value; }
  }

  public bool IsValid {
    get { return WrappedToken.IsValid; }
  }
  public int kind {
    get { return WrappedToken.kind; }
    set { throw new NotSupportedException(); }
  }
  public virtual int line {
    get { return WrappedToken.line; }
    set { throw new NotSupportedException(); }
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

public class RangeToken : TokenWrapper {
  // The wrapped token is the startTok
  private IToken endTok;
  public IToken StartToken => WrappedToken;
  public IToken EndToken => endTok;

  // Used for range reporting
  override public string val {
    get {
      return new string(' ', endTok.pos + endTok.val.Length - pos);
    }
  }

  // If we don't ensure that the endToken is after the start token,
  // then the rangeToken.val will cause an exception because it will try to create
  // an string made of a negative number of spaces.
  // There is at least one case in which the RangeToken is not set linearly
  // because we assume that "tok" is before "endTok" in the statement constructor
  // but that was at least not the case.
  public RangeToken(IToken startTok, IToken endTok) : base(
    endTok.pos < startTok.pos && startTok is RangeToken startRange ?
        startRange.StartToken : startTok) {
    if (endTok.pos < startTok.pos && startTok is RangeToken startRange2) {
      this.endTok = startRange2.EndToken;
    } else {
      this.endTok = endTok;
    }
  }

  public override IToken WithVal(string newVal) {
    return this;
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
/// An IncludeToken is a wrapper that indicates that the function/method was
/// declared in a file that was included. Any proof obligations from such an
/// included file are to be ignored.
/// </summary>
public class IncludeToken : TokenWrapper {
  public Include Include;
  public IncludeToken(Include include, IToken wrappedToken)
    : base(wrappedToken) {
    Contract.Requires(wrappedToken != null);
    this.Include = include;
  }

  public override string val {
    get { return WrappedToken.val; }
    set { WrappedToken.val = value; }
  }

  public override int pos {
    get { return WrappedToken.pos; }
    set { WrappedToken.pos = value; }
  }

  public override int line {
    get { return WrappedToken.line; }
    set { WrappedToken.line = value; }
  }

  public override int col {
    get { return WrappedToken.col; }
    set { WrappedToken.col = value; }
  }

  public override IToken Prev {
    get { return WrappedToken.Prev; }
    set { WrappedToken.Prev = value; }
  }

  public override IToken Next {
    get { return WrappedToken.Next; }
    set { WrappedToken.Next = value; }
  }

  public override IToken WithVal(string newVal) {
    return new IncludeToken(Include, WrappedToken.WithVal(newVal));
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
