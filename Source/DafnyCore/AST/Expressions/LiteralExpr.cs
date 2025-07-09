#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;


namespace Microsoft.Dafny;

public class LiteralExpr : Expression, ICloneable<LiteralExpr> {
  /// <summary>
  /// One of the following:
  ///   * 'null' for the 'null' literal (a special case of which is the subclass StaticReceiverExpr)
  ///   * a bool for a bool literal
  ///   * a BigInteger for int literal
  ///   * a BaseTypes.BigDec for a (rational) real literal
  ///   * a string for a char literal
  ///     This case always uses the subclass CharLiteralExpr.
  ///     Note, a string is stored to keep any escape sequence, since this simplifies printing of the character
  ///     literal, both when pretty printed as a Dafny expression and when being compiled into C# code.  The
  ///     parser checks the validity of any escape sequence and the verifier deals with turning such into a
  ///     single character value.
  ///   * a string for a string literal
  ///     This case always uses the subclass StringLiteralExpr.
  ///     Note, the string is stored with all escapes as characters.  For example, the input string "hello\n" is
  ///     stored in a LiteralExpr has being 7 characters long, whereas the Dafny (and C#) length of this string is 6.
  ///     This simplifies printing of the string, both when pretty printed as a Dafny expression and when being
  ///     compiled into C# code.  The parser checks the validity of the escape sequences and the verifier deals
  ///     with turning them into single characters.
  /// </summary>
  public object? Value;

  public string EscapedValue => $"{Value}".Replace("{", "{{").Replace("}", "}}");

  [System.Diagnostics.Contracts.Pure]
  public static bool IsTrue(Expression e) {
    Contract.Requires(e != null);
    return Expression.IsBoolLiteral(e, out var value) && value;
  }

  public static bool IsFalse(Expression e) {
    Contract.Requires(e != null);
    return Expression.IsBoolLiteral(e, out var value) && !value;
  }

  public static bool IsEmptySet(Expression e) {
    Contract.Requires(e != null);
    return StripParens(e) is SetDisplayExpr display && display.Elements.Count == 0;
  }

  public static bool IsEmptyMultiset(Expression e) {
    Contract.Requires(e != null);
    return StripParens(e) is MultiSetDisplayExpr display && display.Elements.Count == 0;
  }

  public static bool IsEmptySequence(Expression e) {
    Contract.Requires(e != null);
    return StripParens(e) is SeqDisplayExpr display && display.Elements.Count == 0;
  }

  [SyntaxConstructor]
  public LiteralExpr(IOrigin origin, object? value)
    : base(origin) {
    this.Value = value switch {
      int n => new BigInteger(n),
      short n => new BigInteger(n),
      long n => new BigInteger(n),
      _ => value
    };
  }

  public LiteralExpr(IOrigin origin)
    : base(origin) {  // represents the Dafny literal "null"
    Contract.Requires(origin != null);
    this.Value = null;
  }

  public LiteralExpr(IOrigin origin, BigInteger value)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(0 <= value.Sign);
    this.Value = value;
  }

  public LiteralExpr(IOrigin origin, BaseTypes.BigDec value)
    : base(origin) {
    Contract.Requires(0 <= value.Mantissa.Sign);
    Contract.Requires(origin != null);
    this.Value = value;
  }

  public LiteralExpr(IOrigin origin, int n)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(0 <= n);
    this.Value = new BigInteger(n);
  }

  public LiteralExpr(IOrigin origin, bool value)
    : base(origin) {
    Contract.Requires(origin != null);
    this.Value = value;
  }

  /// <summary>
  /// This constructor is to be used only with the StringLiteralExpr and CharLiteralExpr subclasses, for
  /// two reasons:  both of these literals store a string in .Value, and string literals also carry an
  /// additional field.
  /// </summary>
  protected LiteralExpr(IOrigin origin, string value)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(value != null);
    this.Value = value;
  }

  public LiteralExpr(Cloner cloner, LiteralExpr original) : base(cloner, original) {
    Value = original.Value;
  }

  public LiteralExpr Clone(Cloner cloner) {
    return new LiteralExpr(cloner, this);
  }
}

public class CharLiteralExpr : LiteralExpr, ICloneable<CharLiteralExpr> {

  /// <summary>
  /// Because the base field type is object, we need an object constructor here as well
  /// </summary>
  [SyntaxConstructor]
  public CharLiteralExpr(IOrigin origin, object value)
    : base(origin, value) {
    Contract.Requires(value != null);
  }

  public CharLiteralExpr(IOrigin origin, string value)
    : base(origin, value) {
    Contract.Requires(value != null);
  }

  public CharLiteralExpr(Cloner cloner, CharLiteralExpr original) : base(cloner, original) {
  }

  public new CharLiteralExpr Clone(Cloner cloner) {
    return new CharLiteralExpr(cloner, this);
  }
}

public class StringLiteralExpr : LiteralExpr, ICloneable<StringLiteralExpr> {
  public bool IsVerbatim;

  /// <summary>
  /// Because the base field type is object, we need an object constructor here as well
  /// </summary>
  [SyntaxConstructor]
  public StringLiteralExpr(IOrigin origin, object value, bool isVerbatim)
    : this(origin, (string)value, isVerbatim) {
  }

  public StringLiteralExpr(IOrigin origin, string value, bool isVerbatim)
    : base(origin, value) {
    IsVerbatim = isVerbatim;
  }

  public StringLiteralExpr(Cloner cloner, StringLiteralExpr original) : base(cloner, original) {
    IsVerbatim = original.IsVerbatim;
  }

  public new StringLiteralExpr Clone(Cloner cloner) {
    return new StringLiteralExpr(cloner, this);
  }
}

/// <summary>
/// A NegationExpression e represents the value -e and is syntactic shorthand
/// for 0-e (for integers) or 0.0-e (for reals).
/// </summary>
public class NegationExpression : ConcreteSyntaxExpression, ICloneable<NegationExpression> {
  public Expression E;

  public NegationExpression Clone(Cloner cloner) {
    return new NegationExpression(cloner, this);
  }

  public NegationExpression(Cloner cloner, NegationExpression original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
  }

  [SyntaxConstructor]
  public NegationExpression(IOrigin origin, Expression e)
    : base(origin) {
    Contract.Requires(origin != null);
    E = e;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression == null) {
        // the expression hasn't yet been turned into a resolved expression, so use .E as the subexpression
        yield return E;
      } else {
        foreach (var ee in base.SubExpressions) {
          yield return ee;
        }
      }
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return E;
    }
  }
}