// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
namespace Formatting {

  public partial class __default {
    public static System.String ReindentProgramFromFirstToken(Microsoft.Dafny.IToken firstToken, Formatting.IIndentationFormatter reindent) {
      System.String s = default(System.String);
      Microsoft.Dafny.IToken token;
      token = firstToken;
      System.Text.StringBuilder sb;
      System.Text.StringBuilder _nw0 = new System.Text.StringBuilder();
      sb = _nw0;
      while ((token) != (object)((Microsoft.Dafny.IToken)null)) {
        System.String newLeadingTrivia;
        newLeadingTrivia = (reindent).GetNewLeadingTrivia(token);
        System.String newTrailingTrivia;
        newTrailingTrivia = (reindent).GetNewTrailingTrivia(token);
        (sb).Append(newLeadingTrivia);
        (sb).Append(token.val);
        (sb).Append(newTrailingTrivia);
        token = token.Next;
      }
      System.String _out0;
      _out0 = (sb).ToString().ToString();
      s = _out0;
      return s;
    }
  }

  public interface IIndentationFormatter {
    System.String GetNewLeadingTrivia(Microsoft.Dafny.IToken token);
    System.String GetNewTrailingTrivia(Microsoft.Dafny.IToken token);
  }
  public class _Companion_IIndentationFormatter {
  }
} // end of namespace Formatting


namespace Wrappers {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> IntToString(BigInteger i) {
      if ((i).Sign == -1) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"), Wrappers.__default.IntToString((BigInteger.Zero) - (i)));
      } else {
        Dafny.ISequence<Dafny.Rune> unit = Dafny.Sequence<Dafny.Rune>.FromElements((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Select(Dafny.Helpers.EuclideanModulus(i, new BigInteger(10))));
        if ((i) <= (new BigInteger(9))) {
          return unit;
        } else {
          return Dafny.Sequence<Dafny.Rune>.Concat(Wrappers.__default.IntToString(Dafny.Helpers.EuclideanDivision(i, new BigInteger(10))), unit);
        }
      }
    }
  }

  public interface _IResult<S> {
    bool is_Success { get; }
    bool is_Failure { get; }
    S dtor_value { get; }
    Dafny.ISequence<Dafny.Rune> dtor_msg { get; }
    _IResult<__S> DowncastClone<__S>(Func<S, __S> converter0);
    Wrappers._IResult<__T> Map<__T>(Func<S, __T> f);
    bool IsFailure();
    Wrappers._IResult<__U> PropagateFailure<__U>();
    S Extract();
  }
  public abstract class Result<S> : _IResult<S> {
    public Result() {
    }
    public static Wrappers._IResult<S> Default() {
      return create_Failure(Dafny.Sequence<Dafny.Rune>.Empty);
    }
    public static Dafny.TypeDescriptor<Wrappers._IResult<S>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers._IResult<S>>(Wrappers.Result<S>.Default());
    }
    public static _IResult<S> create_Success(S @value) {
      return new Result_Success<S>(@value);
    }
    public static _IResult<S> create_Failure(Dafny.ISequence<Dafny.Rune> msg) {
      return new Result_Failure<S>(msg);
    }
    public bool is_Success { get { return this is Result_Success<S>; } }
    public bool is_Failure { get { return this is Result_Failure<S>; } }
    public S dtor_value {
      get {
        var d = this;
        return ((Result_Success<S>)d)._value;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_msg {
      get {
        var d = this;
        return ((Result_Failure<S>)d)._msg;
      }
    }
    public abstract _IResult<__S> DowncastClone<__S>(Func<S, __S> converter0);
    public Wrappers._IResult<__T> Map<__T>(Func<S, __T> f) {
      if ((this).is_Success) {
        return Wrappers.Result<__T>.create_Success(Dafny.Helpers.Id<Func<S, __T>>(f)((this).dtor_value));
      } else {
        return Wrappers.Result<__T>.create_Failure((this).dtor_msg);
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers._IResult<__U> PropagateFailure<__U>() {
      return Wrappers.Result<__U>.create_Failure((this).dtor_msg);
    }
    public S Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<S> : Result<S> {
    public readonly S _value;
    public Result_Success(S @value) : base() {
      this._value = @value;
    }
    public override _IResult<__S> DowncastClone<__S>(Func<S, __S> converter0) {
      if (this is _IResult<__S> dt) { return dt; }
      return new Result_Success<__S>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Result_Success<S>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<S> : Result<S> {
    public readonly Dafny.ISequence<Dafny.Rune> _msg;
    public Result_Failure(Dafny.ISequence<Dafny.Rune> msg) : base() {
      this._msg = msg;
    }
    public override _IResult<__S> DowncastClone<__S>(Func<S, __S> converter0) {
      if (this is _IResult<__S> dt) { return dt; }
      return new Result_Failure<__S>(_msg);
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Result_Failure<S>;
      return oth != null && object.Equals(this._msg, oth._msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._msg));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Failure";
      s += "(";
      s += this._msg.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
} // end of namespace Wrappers
namespace AlcorProofKernel {


  public interface _IExpr {
    bool is_True { get; }
    bool is_False { get; }
    bool is_And { get; }
    bool is_Imp { get; }
    bool is_Eq { get; }
    bool is_Or { get; }
    bool is_Var { get; }
    bool is_Abs { get; }
    bool is_App { get; }
    bool is_Forall { get; }
    AlcorProofKernel._IExpr dtor_left { get; }
    AlcorProofKernel._IExpr dtor_right { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    BigInteger dtor_version { get; }
    Dafny.ISequence<Dafny.Rune> dtor_lbl { get; }
    AlcorProofKernel._IExpr dtor_body { get; }
    _IExpr DowncastClone();
    Dafny.ISequence<Dafny.Rune> Operator();
    Dafny.ISequence<Dafny.Rune> ToStringWrap(BigInteger outerPriority);
    BigInteger Priority();
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public abstract class Expr : _IExpr {
    public Expr() {
    }
    private static readonly AlcorProofKernel._IExpr theDefault = create_True();
    public static AlcorProofKernel._IExpr Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorProofKernel._IExpr> _TYPE = new Dafny.TypeDescriptor<AlcorProofKernel._IExpr>(AlcorProofKernel.Expr.Default());
    public static Dafny.TypeDescriptor<AlcorProofKernel._IExpr> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpr create_True() {
      return new Expr_True();
    }
    public static _IExpr create_False() {
      return new Expr_False();
    }
    public static _IExpr create_And(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) {
      return new Expr_And(left, right);
    }
    public static _IExpr create_Imp(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) {
      return new Expr_Imp(left, right);
    }
    public static _IExpr create_Eq(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) {
      return new Expr_Eq(left, right);
    }
    public static _IExpr create_Or(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) {
      return new Expr_Or(left, right);
    }
    public static _IExpr create_Var(Dafny.ISequence<Dafny.Rune> name, BigInteger version, Dafny.ISequence<Dafny.Rune> lbl) {
      return new Expr_Var(name, version, lbl);
    }
    public static _IExpr create_Abs(Dafny.ISequence<Dafny.Rune> name, AlcorProofKernel._IExpr body) {
      return new Expr_Abs(name, body);
    }
    public static _IExpr create_App(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) {
      return new Expr_App(left, right);
    }
    public static _IExpr create_Forall(AlcorProofKernel._IExpr body) {
      return new Expr_Forall(body);
    }
    public bool is_True { get { return this is Expr_True; } }
    public bool is_False { get { return this is Expr_False; } }
    public bool is_And { get { return this is Expr_And; } }
    public bool is_Imp { get { return this is Expr_Imp; } }
    public bool is_Eq { get { return this is Expr_Eq; } }
    public bool is_Or { get { return this is Expr_Or; } }
    public bool is_Var { get { return this is Expr_Var; } }
    public bool is_Abs { get { return this is Expr_Abs; } }
    public bool is_App { get { return this is Expr_App; } }
    public bool is_Forall { get { return this is Expr_Forall; } }
    public AlcorProofKernel._IExpr dtor_left {
      get {
        var d = this;
        if (d is Expr_And) { return ((Expr_And)d)._left; }
        if (d is Expr_Imp) { return ((Expr_Imp)d)._left; }
        if (d is Expr_Eq) { return ((Expr_Eq)d)._left; }
        if (d is Expr_Or) { return ((Expr_Or)d)._left; }
        return ((Expr_App)d)._left;
      }
    }
    public AlcorProofKernel._IExpr dtor_right {
      get {
        var d = this;
        if (d is Expr_And) { return ((Expr_And)d)._right; }
        if (d is Expr_Imp) { return ((Expr_Imp)d)._right; }
        if (d is Expr_Eq) { return ((Expr_Eq)d)._right; }
        if (d is Expr_Or) { return ((Expr_Or)d)._right; }
        return ((Expr_App)d)._right;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Expr_Var) { return ((Expr_Var)d)._name; }
        return ((Expr_Abs)d)._name;
      }
    }
    public BigInteger dtor_version {
      get {
        var d = this;
        return ((Expr_Var)d)._version;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_lbl {
      get {
        var d = this;
        return ((Expr_Var)d)._lbl;
      }
    }
    public AlcorProofKernel._IExpr dtor_body {
      get {
        var d = this;
        if (d is Expr_Abs) { return ((Expr_Abs)d)._body; }
        return ((Expr_Forall)d)._body;
      }
    }
    public abstract _IExpr DowncastClone();
    public static AlcorProofKernel._IExpr Not(AlcorProofKernel._IExpr expr) {
      return AlcorProofKernel.Expr.create_Imp(expr, AlcorProofKernel.Expr.create_False());
    }
    public Dafny.ISequence<Dafny.Rune> Operator() {
      if ((this).is_And) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&");
      } else if ((this).is_Or) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||");
      } else if ((this).is_Imp) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("==>");
      } else if ((this).is_Eq) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("==");
      } else if ((this).is_False) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false");
      } else if ((this).is_True) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true");
      } else if ((this).is_Var) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_name, ((!((this).dtor_lbl).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("@"), (this).dtor_lbl)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), ((((this).dtor_version).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("@"), Wrappers.__default.IntToString((this).dtor_version)))));
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      }
    }
    public Dafny.ISequence<Dafny.Rune> ToStringWrap(BigInteger outerPriority) {
      Dafny.ISequence<Dafny.Rune> r = (this)._ToString();
      if ((outerPriority) >= ((this).Priority())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), r), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        return r;
      }
    }
    public BigInteger Priority() {
      if ((((this).is_False) || ((this).is_True)) || ((this).is_Var)) {
        return new BigInteger(10);
      } else if ((this).is_Eq) {
        return new BigInteger(9);
      } else if ((this).is_And) {
        return new BigInteger(8);
      } else if ((this).is_Or) {
        return new BigInteger(7);
      } else if ((this).is_Imp) {
        if (((this).dtor_right).is_False) {
          return new BigInteger(10);
        } else {
          return new BigInteger(6);
        }
      } else if ((this).is_Abs) {
        return new BigInteger(5);
      } else if ((this).is_App) {
        return new BigInteger(5);
      } else if ((this).is_Forall) {
        return new BigInteger(4);
      } else {
        return BigInteger.Zero;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      BigInteger p = (this).Priority();
      if (((this).is_Imp) && (((this).dtor_right).is_False)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), ((this).dtor_left).ToStringWrap(p));
      } else if (((((this).is_And) || ((this).is_Or)) || ((this).is_Eq)) || ((this).is_Imp)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_left).ToStringWrap(p), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), (this).Operator()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_right).ToStringWrap(p));
      } else if ((this).is_Abs) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\"), (this).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((this).dtor_body).ToStringWrap((p) + (BigInteger.One)));
      } else if ((this).is_App) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_left).ToStringWrap(p), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_right).ToStringWrap(p));
      } else if ((this).is_Forall) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("forall "), ((this).dtor_body).ToStringWrap((p) + (BigInteger.One)));
      } else {
        return (this).Operator();
      }
    }
  }
  public class Expr_True : Expr {
    public Expr_True() : base() {
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_True();
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_True;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.True";
      return s;
    }
  }
  public class Expr_False : Expr {
    public Expr_False() : base() {
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_False();
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_False;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.False";
      return s;
    }
  }
  public class Expr_And : Expr {
    public readonly AlcorProofKernel._IExpr _left;
    public readonly AlcorProofKernel._IExpr _right;
    public Expr_And(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_And(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_And;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.And";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class Expr_Imp : Expr {
    public readonly AlcorProofKernel._IExpr _left;
    public readonly AlcorProofKernel._IExpr _right;
    public Expr_Imp(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Imp(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Imp;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Imp";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class Expr_Eq : Expr {
    public readonly AlcorProofKernel._IExpr _left;
    public readonly AlcorProofKernel._IExpr _right;
    public Expr_Eq(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Eq(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Eq;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Eq";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class Expr_Or : Expr {
    public readonly AlcorProofKernel._IExpr _left;
    public readonly AlcorProofKernel._IExpr _right;
    public Expr_Or(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Or(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Or;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Or";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class Expr_Var : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly BigInteger _version;
    public readonly Dafny.ISequence<Dafny.Rune> _lbl;
    public Expr_Var(Dafny.ISequence<Dafny.Rune> name, BigInteger version, Dafny.ISequence<Dafny.Rune> lbl) : base() {
      this._name = name;
      this._version = version;
      this._lbl = lbl;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Var(_name, _version, _lbl);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Var;
      return oth != null && object.Equals(this._name, oth._name) && this._version == oth._version && object.Equals(this._lbl, oth._lbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._version));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lbl));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Var";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._version);
      s += ", ";
      s += this._lbl.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_Abs : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly AlcorProofKernel._IExpr _body;
    public Expr_Abs(Dafny.ISequence<Dafny.Rune> name, AlcorProofKernel._IExpr body) : base() {
      this._name = name;
      this._body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Abs(_name, _body);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Abs;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Abs";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Expr_App : Expr {
    public readonly AlcorProofKernel._IExpr _left;
    public readonly AlcorProofKernel._IExpr _right;
    public Expr_App(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_App(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_App;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.App";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class Expr_Forall : Expr {
    public readonly AlcorProofKernel._IExpr _body;
    public Expr_Forall(AlcorProofKernel._IExpr body) : base() {
      this._body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Forall(_body);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Forall;
      return oth != null && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Forall";
      s += "(";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }

  public interface _IProof {
    bool is_Proof { get; }
    AlcorProofKernel._IExpr dtor_expr { get; }
  }
  public class Proof : _IProof {
    public readonly AlcorProofKernel._IExpr _expr;
    public Proof(AlcorProofKernel._IExpr expr) {
      this._expr = expr;
    }
    public static AlcorProofKernel._IExpr DowncastClone(AlcorProofKernel._IExpr _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Proof;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Proof.Proof";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
    private static readonly AlcorProofKernel._IExpr theDefault = AlcorProofKernel.Expr.Default();
    public static AlcorProofKernel._IExpr Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorProofKernel._IExpr> _TYPE = new Dafny.TypeDescriptor<AlcorProofKernel._IExpr>(AlcorProofKernel.Expr.Default());
    public static Dafny.TypeDescriptor<AlcorProofKernel._IExpr> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IProof create(AlcorProofKernel._IExpr expr) {
      return new Proof(expr);
    }
    public static _IProof create_Proof(AlcorProofKernel._IExpr expr) {
      return create(expr);
    }
    public bool is_Proof { get { return true; } }
    public AlcorProofKernel._IExpr dtor_expr {
      get {
        return this._expr;
      }
    }
    public static AlcorProofKernel._IExpr GetExpr(AlcorProofKernel._IExpr _this) {
      return (_this);
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> and(AlcorProofKernel._IExpr _this, AlcorProofKernel._IExpr other) {
      return AlcorProofKernel.Proof.AndIntro(_this, other);
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> AndIntro(AlcorProofKernel._IExpr left, AlcorProofKernel._IExpr right) {
      return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(AlcorProofKernel.Expr.create_And((left), (right)));
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> AndElimLeft(AlcorProofKernel._IExpr elem) {
      if (!(((elem)).is_And)) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("To apply AndElimLeft, expected And(), got "), ((elem))._ToString()));
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(((elem)).dtor_left);
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> AndElimRight(AlcorProofKernel._IExpr elem) {
      if (!(((elem)).is_And)) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("To apply AndElimRight, expected And(), got "), ((elem))._ToString()));
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(((elem)).dtor_right);
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> ImpElim(AlcorProofKernel._IExpr aToB, AlcorProofKernel._IExpr a) {
      if (!(((aToB)).is_Imp)) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("To apply ImpElim, the first argument must be ==>, got "), ((aToB))._ToString()));
      } else if (!object.Equals(((aToB)).dtor_left, (a))) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("To apply ImpElim, the second argument must be the hypothesis of the first one. But got "), ((aToB))._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" and ")), ((a))._ToString()));
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(((aToB)).dtor_right);
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> ImpIntro(AlcorProofKernel._IExpr hypothesis, Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>> pHypothesis) {
      AlcorProofKernel._IExpr p = hypothesis;
      Wrappers._IResult<AlcorProofKernel._IExpr> valueOrError0 = Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>>(pHypothesis)(p);
      if ((valueOrError0).IsFailure()) {
        return (valueOrError0).PropagateFailure<AlcorProofKernel._IExpr>();
      } else {
        AlcorProofKernel._IExpr result = (valueOrError0).Extract();
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(AlcorProofKernel.Expr.create_Imp(hypothesis, (result)));
      }
    }
  }
} // end of namespace AlcorProofKernel
namespace Alcor {

  public partial class __default {
    public static Alcor._IProofProgram Let(Dafny.ISequence<Dafny.Rune> name, Alcor._IType tpe, Alcor._IProofProgram expression, Alcor._IProofProgram body) {
      return Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofAbs(name, tpe, body), expression);
    }
    public static BigInteger Debug(Dafny.ISequence<Dafny.Rune> msg) {
      BigInteger result = BigInteger.Zero;
      Dafny.Helpers.Print((msg).ToVerbatimString(false));
      result = BigInteger.Zero;
      return result;
    }
    public static Wrappers._IResult<Alcor._IProofValue> ExecuteProof(Alcor._IProofProgram program, Alcor._IEnvironment environment) {
      Alcor._IProofProgram _source0 = program;
      if (_source0.is_ProofVar) {
        Dafny.ISequence<Dafny.Rune> _10___mcc_h0 = _source0.dtor_name;
        Dafny.ISequence<Dafny.Rune> _11_name = _10___mcc_h0;
        return (environment).Lookup(_11_name);
      } else if (_source0.is_ProofExpr) {
        AlcorProofKernel._IExpr _12___mcc_h1 = _source0.dtor_expr;
        AlcorProofKernel._IExpr _13_expr = _12___mcc_h1;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneExpr(_13_expr));
      } else if (_source0.is_ProofAbs) {
        Dafny.ISequence<Dafny.Rune> _14___mcc_h2 = _source0.dtor_name;
        Alcor._IType _15___mcc_h3 = _source0.dtor_tpe;
        Alcor._IProofProgram _16___mcc_h4 = _source0.dtor_body;
        Alcor._IProofProgram _17_body = _16___mcc_h4;
        Alcor._IType _18_tpe = _15___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _19_name = _14___mcc_h2;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosure(_19_name, _18_tpe, _17_body, environment));
      } else if (_source0.is_ProofApp) {
        Alcor._IProofProgram _20___mcc_h5 = _source0.dtor_left;
        Alcor._IProofProgram _21___mcc_h6 = _source0.dtor_right;
        Alcor._IProofProgram _22_right = _21___mcc_h6;
        Alcor._IProofProgram _23_left = _20___mcc_h5;
        Wrappers._IResult<Alcor._IProofValue> _24_valueOrError0 = Alcor.__default.ExecuteProof(_23_left, environment);
        if ((_24_valueOrError0).IsFailure()) {
          return (_24_valueOrError0).PropagateFailure<Alcor._IProofValue>();
        } else {
          Alcor._IProofValue _25_result = (_24_valueOrError0).Extract();
          if ((_25_result).is_OneClosure) {
            Wrappers._IResult<Alcor._IProofValue> _26_valueOrError1 = Alcor.__default.ExecuteProof(_22_right, environment);
            if ((_26_valueOrError1).IsFailure()) {
              return (_26_valueOrError1).PropagateFailure<Alcor._IProofValue>();
            } else {
              Alcor._IProofValue _27_argument = (_26_valueOrError1).Extract();
              return Alcor.__default.ExecuteProof((_25_result).dtor_body, Alcor.Environment.create_EnvCons((_25_result).dtor_argName, _27_argument, (_25_result).dtor_environment));
            }
          } else if ((_25_result).is_OneClosureAxiom) {
            Wrappers._IResult<Alcor._IProofValue> _28_valueOrError2 = Alcor.__default.ExecuteProof(_22_right, environment);
            if ((_28_valueOrError2).IsFailure()) {
              return (_28_valueOrError2).PropagateFailure<Alcor._IProofValue>();
            } else {
              Alcor._IProofValue _29_argument = (_28_valueOrError2).Extract();
              if ((((_25_result).dtor_axiom).Arity()) == ((new BigInteger(((_25_result).dtor_args).Count)) + (BigInteger.One))) {
                return ((_25_result).dtor_axiom).ApplyArgs(Dafny.Sequence<Alcor._IProofValue>.Concat((_25_result).dtor_args, Dafny.Sequence<Alcor._IProofValue>.FromElements(_29_argument)), environment);
              } else {
                return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosureAxiom(Dafny.Sequence<Alcor._IProofValue>.Concat((_25_result).dtor_args, Dafny.Sequence<Alcor._IProofValue>.FromElements(_29_argument)), (_25_result).dtor_axiom));
              }
            }
          } else {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Left of application was not a closure"));
          }
        }
      } else {
        Alcor._IProofAxiom _30___mcc_h7 = _source0.dtor_axiom;
        Alcor._IProofAxiom _31_axiom = _30___mcc_h7;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosureAxiom(Dafny.Sequence<Alcor._IProofValue>.FromElements(), _31_axiom));
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> CheckProof(Alcor._IProofProgram program, Alcor._IEnvironment environment, AlcorProofKernel._IExpr expected) {
      Wrappers._IResult<Alcor._IProofValue> _32_valueOrError0 = Alcor.__default.ExecuteProof(program, environment);
      if ((_32_valueOrError0).IsFailure()) {
        return (_32_valueOrError0).PropagateFailure<AlcorProofKernel._IExpr>();
      } else {
        Alcor._IProofValue _33_result = (_32_valueOrError0).Extract();
        if (((_33_result).is_OneClosure) || ((_33_result).is_OneClosureAxiom)) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a closure proof")));
        } else if ((_33_result).is_OneExpr) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a simple expression")));
        } else if (!object.Equals(AlcorProofKernel.Proof.GetExpr((_33_result).dtor_proof), expected)) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" but got a proof of ")), (AlcorProofKernel.Proof.GetExpr((_33_result).dtor_proof))._ToString()));
        } else {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_33_result).dtor_proof);
        }
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> checkGoalAgainstExpr(Alcor._IProofValue pv, AlcorProofKernel._IExpr expr) {
      if (!((pv).is_OneProof)) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DummyProofFinder did not generate a proof but "), (pv).Summary()));
      } else {
        AlcorProofKernel._IExpr _34_p = (pv).dtor_proof;
        if (object.Equals(AlcorProofKernel.Proof.GetExpr(_34_p), expr)) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(_34_p);
        } else {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DummyProofFinder was looking for a proof of "), (expr)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" but returned a proof of ")), (AlcorProofKernel.Proof.GetExpr(_34_p))._ToString()));
        }
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> DummyProofFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<AlcorProofKernel._IExpr> result = Wrappers.Result<AlcorProofKernel._IExpr>.Default();
      Func<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>> _35_checkGoal;
      _35_checkGoal = Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, Func<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>>>((_36_expr) => ((System.Func<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>)((_37_pv) => {
        return Alcor.__default.checkGoalAgainstExpr(_37_pv, _36_expr);
      })))(expr);
      if (!((expr).is_Imp)) {
        result = Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ProofFinder requires an implication"));
        return result;
      }
      AlcorProofKernel._IExpr _38_goal;
      _38_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _39_env;
      _39_env = (expr).dtor_left;
      if ((_38_goal).is_Imp) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _40_proofOfConclusion;
        Wrappers._IResult<AlcorProofKernel._IExpr> _out1;
        _out1 = Alcor.__default.DummyProofFinder(AlcorProofKernel.Expr.create_Imp(AlcorProofKernel.Expr.create_And((_38_goal).dtor_left, _39_env), (_38_goal).dtor_right));
        _40_proofOfConclusion = _out1;
        if ((_40_proofOfConclusion).is_Success) {
          Alcor._IEnvironment _41_execEnv;
          _41_execEnv = Alcor.Environment.create_EnvCons(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b"), Alcor.ProofValue.create_OneProof((_40_proofOfConclusion).dtor_value), Alcor.Environment.create_EnvNil());
          Alcor._IProofValue _42_r;
          Wrappers._IResult<Alcor._IProofValue> _43_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
          _43_valueOrError0 = Alcor.__default.ExecuteProof((Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_39_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr((_38_goal).dtor_left), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proofOfA"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_ImpElim()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b")), (Alcor.ProofAxiom.create_AndIntro()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proofOfA")), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))))))), _41_execEnv);
          if ((_43_valueOrError0).IsFailure()) {
            result = (_43_valueOrError0).PropagateFailure<AlcorProofKernel._IExpr>();
            return result;
          }
          _42_r = (_43_valueOrError0).Extract();
          result = Dafny.Helpers.Id<Func<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>>(_35_checkGoal)(_42_r);
          return result;
        }
      }
      if (!((_39_env).is_And)) {
        result = Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ProofFinder requires an environment to the left of ==>"));
        return result;
      }
      AlcorProofKernel._IExpr _44_A0;
      _44_A0 = (_39_env).dtor_left;
      AlcorProofKernel._IExpr _45_tail;
      _45_tail = (_39_env).dtor_right;
      if ((_44_A0).is_And) {
        if (object.Equals((_44_A0).dtor_left, _38_goal)) {
          Alcor._IProofProgram _46_proofProgram;
          _46_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_39_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _47_r;
          Wrappers._IResult<Alcor._IProofValue> _48_valueOrError1 = Wrappers.Result<Alcor._IProofValue>.Default();
          _48_valueOrError1 = Alcor.__default.ExecuteProof(_46_proofProgram, Alcor.Environment.create_EnvNil());
          if ((_48_valueOrError1).IsFailure()) {
            result = (_48_valueOrError1).PropagateFailure<AlcorProofKernel._IExpr>();
            return result;
          }
          _47_r = (_48_valueOrError1).Extract();
          result = Dafny.Helpers.Id<Func<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>>(_35_checkGoal)(_47_r);
          return result;
        }
        if (object.Equals((_44_A0).dtor_right, _38_goal)) {
          Alcor._IProofProgram _49_proofProgram;
          _49_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_39_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimRight()).apply1((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _50_r;
          Wrappers._IResult<Alcor._IProofValue> _51_valueOrError2 = Wrappers.Result<Alcor._IProofValue>.Default();
          _51_valueOrError2 = Alcor.__default.ExecuteProof(_49_proofProgram, Alcor.Environment.create_EnvNil());
          if ((_51_valueOrError2).IsFailure()) {
            result = (_51_valueOrError2).PropagateFailure<AlcorProofKernel._IExpr>();
            return result;
          }
          _50_r = (_51_valueOrError2).Extract();
          result = Dafny.Helpers.Id<Func<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>>(_35_checkGoal)(_50_r);
          return result;
        }
      }
      AlcorProofKernel._IExpr _52_envSearch;
      _52_envSearch = _39_env;
      BigInteger _53_i;
      _53_i = BigInteger.Zero;
      while (((_52_envSearch).is_And) && (!object.Equals((_52_envSearch).dtor_left, _38_goal))) {
        _52_envSearch = (_52_envSearch).dtor_right;
        _53_i = (_53_i) + (BigInteger.One);
      }
      if (((_52_envSearch).is_And) && (object.Equals((_52_envSearch).dtor_left, _38_goal))) {
        Alcor._IProofProgram _54_proofElem;
        _54_proofElem = Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"));
        while ((_53_i).Sign != 0) {
          _54_proofElem = Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofAxiom(Alcor.ProofAxiom.create_AndElimRight()), _54_proofElem);
          _53_i = (_53_i) - (BigInteger.One);
        }
        Alcor._IProofProgram _55_proofProgram;
        _55_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_39_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofAxiom(Alcor.ProofAxiom.create_AndElimLeft()), _54_proofElem)));
        Alcor._IProofValue _56_r;
        Wrappers._IResult<Alcor._IProofValue> _57_valueOrError3 = Wrappers.Result<Alcor._IProofValue>.Default();
        _57_valueOrError3 = Alcor.__default.ExecuteProof(_55_proofProgram, Alcor.Environment.create_EnvNil());
        if ((_57_valueOrError3).IsFailure()) {
          result = (_57_valueOrError3).PropagateFailure<AlcorProofKernel._IExpr>();
          return result;
        }
        _56_r = (_57_valueOrError3).Extract();
        result = Dafny.Helpers.Id<Func<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>>(_35_checkGoal)(_56_r);
        return result;
      }
      result = Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not find a simple proof of "), (expr)._ToString()));
      return result;
      return result;
    }
  }

  public interface _IEnvironment {
    bool is_EnvNil { get; }
    bool is_EnvCons { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Alcor._IProofValue dtor_value { get; }
    Alcor._IEnvironment dtor_tail { get; }
    _IEnvironment DowncastClone();
    Wrappers._IResult<Alcor._IProofValue> Lookup(Dafny.ISequence<Dafny.Rune> searchName);
  }
  public abstract class Environment : _IEnvironment {
    public Environment() {
    }
    private static readonly Alcor._IEnvironment theDefault = create_EnvNil();
    public static Alcor._IEnvironment Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Alcor._IEnvironment> _TYPE = new Dafny.TypeDescriptor<Alcor._IEnvironment>(Alcor.Environment.Default());
    public static Dafny.TypeDescriptor<Alcor._IEnvironment> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnvironment create_EnvNil() {
      return new Environment_EnvNil();
    }
    public static _IEnvironment create_EnvCons(Dafny.ISequence<Dafny.Rune> name, Alcor._IProofValue @value, Alcor._IEnvironment tail) {
      return new Environment_EnvCons(name, @value, tail);
    }
    public bool is_EnvNil { get { return this is Environment_EnvNil; } }
    public bool is_EnvCons { get { return this is Environment_EnvCons; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((Environment_EnvCons)d)._name;
      }
    }
    public Alcor._IProofValue dtor_value {
      get {
        var d = this;
        return ((Environment_EnvCons)d)._value;
      }
    }
    public Alcor._IEnvironment dtor_tail {
      get {
        var d = this;
        return ((Environment_EnvCons)d)._tail;
      }
    }
    public abstract _IEnvironment DowncastClone();
    public Wrappers._IResult<Alcor._IProofValue> Lookup(Dafny.ISequence<Dafny.Rune> searchName) {
      _IEnvironment _this = this;
    TAIL_CALL_START:;
      if ((_this).is_EnvNil) {
        return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Did not find "), searchName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" in the proof environment")));
      } else if (((_this).dtor_name).Equals(searchName)) {
        return Wrappers.Result<Alcor._IProofValue>.create_Success((_this).dtor_value);
      } else {
        var _in0 = (_this).dtor_tail;
        Dafny.ISequence<Dafny.Rune> _in1 = searchName;
        _this = _in0;
        searchName = _in1;
        goto TAIL_CALL_START;
      }
    }
  }
  public class Environment_EnvNil : Environment {
    public Environment_EnvNil() : base() {
    }
    public override _IEnvironment DowncastClone() {
      if (this is _IEnvironment dt) { return dt; }
      return new Environment_EnvNil();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.Environment_EnvNil;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.Environment.EnvNil";
      return s;
    }
  }
  public class Environment_EnvCons : Environment {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Alcor._IProofValue _value;
    public readonly Alcor._IEnvironment _tail;
    public Environment_EnvCons(Dafny.ISequence<Dafny.Rune> name, Alcor._IProofValue @value, Alcor._IEnvironment tail) : base() {
      this._name = name;
      this._value = @value;
      this._tail = tail;
    }
    public override _IEnvironment DowncastClone() {
      if (this is _IEnvironment dt) { return dt; }
      return new Environment_EnvCons(_name, _value, _tail);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.Environment_EnvCons;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._value, oth._value) && object.Equals(this._tail, oth._tail);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tail));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.Environment.EnvCons";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tail);
      s += ")";
      return s;
    }
  }

  public interface _IProofAxiom {
    bool is_AndIntro { get; }
    bool is_AndElimLeft { get; }
    bool is_AndElimRight { get; }
    bool is_ImpElim { get; }
    bool is_ImpIntro { get; }
    _IProofAxiom DowncastClone();
    Alcor._IProofProgram apply1(Alcor._IProofProgram A);
    Alcor._IProofProgram apply2(Alcor._IProofProgram A, Alcor._IProofProgram B);
    Dafny.ISequence<Dafny.Rune> _ToString();
    BigInteger Arity();
    Wrappers._IResult<AlcorProofKernel._IExpr> ExtractProof(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i);
    Wrappers._IResult<AlcorProofKernel._IExpr> ExtractExpr(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i);
    Wrappers._IResult<Alcor._IProofValue> ApplyArgs(Dafny.ISequence<Alcor._IProofValue> args, Alcor._IEnvironment environment);
  }
  public abstract class ProofAxiom : _IProofAxiom {
    public ProofAxiom() {
    }
    private static readonly Alcor._IProofAxiom theDefault = create_AndIntro();
    public static Alcor._IProofAxiom Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Alcor._IProofAxiom> _TYPE = new Dafny.TypeDescriptor<Alcor._IProofAxiom>(Alcor.ProofAxiom.Default());
    public static Dafny.TypeDescriptor<Alcor._IProofAxiom> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IProofAxiom create_AndIntro() {
      return new ProofAxiom_AndIntro();
    }
    public static _IProofAxiom create_AndElimLeft() {
      return new ProofAxiom_AndElimLeft();
    }
    public static _IProofAxiom create_AndElimRight() {
      return new ProofAxiom_AndElimRight();
    }
    public static _IProofAxiom create_ImpElim() {
      return new ProofAxiom_ImpElim();
    }
    public static _IProofAxiom create_ImpIntro() {
      return new ProofAxiom_ImpIntro();
    }
    public bool is_AndIntro { get { return this is ProofAxiom_AndIntro; } }
    public bool is_AndElimLeft { get { return this is ProofAxiom_AndElimLeft; } }
    public bool is_AndElimRight { get { return this is ProofAxiom_AndElimRight; } }
    public bool is_ImpElim { get { return this is ProofAxiom_ImpElim; } }
    public bool is_ImpIntro { get { return this is ProofAxiom_ImpIntro; } }
    public static System.Collections.Generic.IEnumerable<_IProofAxiom> AllSingletonConstructors {
      get {
        yield return ProofAxiom.create_AndIntro();
        yield return ProofAxiom.create_AndElimLeft();
        yield return ProofAxiom.create_AndElimRight();
        yield return ProofAxiom.create_ImpElim();
        yield return ProofAxiom.create_ImpIntro();
      }
    }
    public abstract _IProofAxiom DowncastClone();
    public Alcor._IProofProgram apply1(Alcor._IProofProgram A) {
      return (Alcor.ProofProgram.create_ProofAxiom(this)).apply1(A);
    }
    public Alcor._IProofProgram apply2(Alcor._IProofProgram A, Alcor._IProofProgram B) {
      return (Alcor.ProofProgram.create_ProofAxiom(this)).apply2(A, B);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      Alcor._IProofAxiom _source1 = this;
      if (_source1.is_AndIntro) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndIntro");
      } else if (_source1.is_AndElimLeft) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndElimLeft");
      } else if (_source1.is_AndElimRight) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndElimRight");
      } else if (_source1.is_ImpElim) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ImpElim");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ImpIntro");
      }
    }
    public BigInteger Arity() {
      Alcor._IProofAxiom _source2 = this;
      if (_source2.is_AndIntro) {
        return new BigInteger(2);
      } else if (_source2.is_AndElimLeft) {
        return BigInteger.One;
      } else if (_source2.is_AndElimRight) {
        return BigInteger.One;
      } else if (_source2.is_ImpElim) {
        return new BigInteger(2);
      } else {
        return new BigInteger(2);
      }
    }
    public Wrappers._IResult<AlcorProofKernel._IExpr> ExtractProof(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i) {
      Alcor._IProofValue _58_arg = (args).Select(i);
      if ((_58_arg).is_OneProof) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_58_arg).dtor_proof);
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("At index "), Wrappers.__default.IntToString(i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), (this)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", expected proof, but got ")), (_58_arg).Summary()));
      }
    }
    public Wrappers._IResult<AlcorProofKernel._IExpr> ExtractExpr(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i) {
      Alcor._IProofValue _59_arg = (args).Select(i);
      if ((_59_arg).is_OneExpr) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_59_arg).dtor_expr);
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("At index "), Wrappers.__default.IntToString(i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), (this)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", expected expr, but got ")), (_59_arg).Summary()));
      }
    }
    public Wrappers._IResult<Alcor._IProofValue> ApplyArgs(Dafny.ISequence<Alcor._IProofValue> args, Alcor._IEnvironment environment) {
      Alcor._IProofAxiom _source3 = this;
      if (_source3.is_AndIntro) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _60_valueOrError0 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_60_valueOrError0).IsFailure()) {
          return (_60_valueOrError0).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _61_left = (_60_valueOrError0).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _62_valueOrError1 = (this).ExtractProof(args, BigInteger.One);
          if ((_62_valueOrError1).IsFailure()) {
            return (_62_valueOrError1).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _63_right = (_62_valueOrError1).Extract();
            return (AlcorProofKernel.Proof.AndIntro(_61_left, _63_right)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_64_p) => {
              return Alcor.ProofValue.create_OneProof(_64_p);
            })));
          }
        }
      } else if (_source3.is_AndElimLeft) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _65_valueOrError2 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_65_valueOrError2).IsFailure()) {
          return (_65_valueOrError2).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _66_elem = (_65_valueOrError2).Extract();
          return (AlcorProofKernel.Proof.AndElimLeft(_66_elem)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_67_p) => {
            return Alcor.ProofValue.create_OneProof(_67_p);
          })));
        }
      } else if (_source3.is_AndElimRight) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _68_valueOrError3 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_68_valueOrError3).IsFailure()) {
          return (_68_valueOrError3).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _69_elem = (_68_valueOrError3).Extract();
          return (AlcorProofKernel.Proof.AndElimRight(_69_elem)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_70_p) => {
            return Alcor.ProofValue.create_OneProof(_70_p);
          })));
        }
      } else if (_source3.is_ImpElim) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _71_valueOrError6 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_71_valueOrError6).IsFailure()) {
          return (_71_valueOrError6).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _72_left = (_71_valueOrError6).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _73_valueOrError7 = (this).ExtractProof(args, BigInteger.One);
          if ((_73_valueOrError7).IsFailure()) {
            return (_73_valueOrError7).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _74_right = (_73_valueOrError7).Extract();
            return (AlcorProofKernel.Proof.ImpElim(_72_left, _74_right)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_75_p) => {
              return Alcor.ProofValue.create_OneProof(_75_p);
            })));
          }
        }
      } else {
        Wrappers._IResult<AlcorProofKernel._IExpr> _76_valueOrError4 = (this).ExtractExpr(args, BigInteger.Zero);
        if ((_76_valueOrError4).IsFailure()) {
          return (_76_valueOrError4).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _77_hypothesis = (_76_valueOrError4).Extract();
          Alcor._IProofValue _78_reasoning = (args).Select(BigInteger.One);
          if (!((_78_reasoning).is_OneClosure)) {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Second argument of ImpIntro requires a closure, got "), (_78_reasoning).Summary()));
          } else {
            Dafny.ISequence<Dafny.Rune> _79_argName = (_78_reasoning).dtor_argName;
            Alcor._IProofProgram _80_body = (_78_reasoning).dtor_body;
            Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>> _81_proofBuilder = Dafny.Helpers.Id<Func<Alcor._IProofProgram, Dafny.ISequence<Dafny.Rune>, Alcor._IEnvironment, Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>>>((_82_body, _83_argName, _84_environment) => ((System.Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>)((_85_p) => {
              return Dafny.Helpers.Let<Wrappers._IResult<Alcor._IProofValue>, Wrappers._IResult<AlcorProofKernel._IExpr>>(Alcor.__default.ExecuteProof(_82_body, Alcor.Environment.create_EnvCons(_83_argName, Alcor.ProofValue.create_OneProof(_85_p), _84_environment)), _pat_let0_0 => Dafny.Helpers.Let<Wrappers._IResult<Alcor._IProofValue>, Wrappers._IResult<AlcorProofKernel._IExpr>>(_pat_let0_0, _86_valueOrError5 => (((_86_valueOrError5).IsFailure()) ? ((_86_valueOrError5).PropagateFailure<AlcorProofKernel._IExpr>()) : (Dafny.Helpers.Let<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>((_86_valueOrError5).Extract(), _pat_let1_0 => Dafny.Helpers.Let<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>(_pat_let1_0, _87_x => (((_87_x).is_OneProof) ? (Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_87_x).dtor_proof)) : (Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Closure should return a proof, but got "), (_87_x).Summary()))))))))));
            })))(_80_body, _79_argName, environment);
            return (AlcorProofKernel.Proof.ImpIntro(_77_hypothesis, _81_proofBuilder)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_88_p) => {
              return Alcor.ProofValue.create_OneProof(_88_p);
            })));
          }
        }
      }
    }
  }
  public class ProofAxiom_AndIntro : ProofAxiom {
    public ProofAxiom_AndIntro() : base() {
    }
    public override _IProofAxiom DowncastClone() {
      if (this is _IProofAxiom dt) { return dt; }
      return new ProofAxiom_AndIntro();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofAxiom_AndIntro;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofAxiom.AndIntro";
      return s;
    }
  }
  public class ProofAxiom_AndElimLeft : ProofAxiom {
    public ProofAxiom_AndElimLeft() : base() {
    }
    public override _IProofAxiom DowncastClone() {
      if (this is _IProofAxiom dt) { return dt; }
      return new ProofAxiom_AndElimLeft();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofAxiom_AndElimLeft;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofAxiom.AndElimLeft";
      return s;
    }
  }
  public class ProofAxiom_AndElimRight : ProofAxiom {
    public ProofAxiom_AndElimRight() : base() {
    }
    public override _IProofAxiom DowncastClone() {
      if (this is _IProofAxiom dt) { return dt; }
      return new ProofAxiom_AndElimRight();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofAxiom_AndElimRight;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofAxiom.AndElimRight";
      return s;
    }
  }
  public class ProofAxiom_ImpElim : ProofAxiom {
    public ProofAxiom_ImpElim() : base() {
    }
    public override _IProofAxiom DowncastClone() {
      if (this is _IProofAxiom dt) { return dt; }
      return new ProofAxiom_ImpElim();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofAxiom_ImpElim;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofAxiom.ImpElim";
      return s;
    }
  }
  public class ProofAxiom_ImpIntro : ProofAxiom {
    public ProofAxiom_ImpIntro() : base() {
    }
    public override _IProofAxiom DowncastClone() {
      if (this is _IProofAxiom dt) { return dt; }
      return new ProofAxiom_ImpIntro();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofAxiom_ImpIntro;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofAxiom.ImpIntro";
      return s;
    }
  }

  public interface _IType {
    bool is_Ind { get; }
    bool is_Bool { get; }
    bool is_Arrow { get; }
    Alcor._IType dtor_Arrow_a0 { get; }
    Alcor._IType dtor_Arrow_a1 { get; }
    _IType DowncastClone();
  }
  public abstract class Type : _IType {
    public Type() {
    }
    private static readonly Alcor._IType theDefault = create_Ind();
    public static Alcor._IType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Alcor._IType> _TYPE = new Dafny.TypeDescriptor<Alcor._IType>(Alcor.Type.Default());
    public static Dafny.TypeDescriptor<Alcor._IType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IType create_Ind() {
      return new Type_Ind();
    }
    public static _IType create_Bool() {
      return new Type_Bool();
    }
    public static _IType create_Arrow(Alcor._IType _a0, Alcor._IType _a1) {
      return new Type_Arrow(_a0, _a1);
    }
    public bool is_Ind { get { return this is Type_Ind; } }
    public bool is_Bool { get { return this is Type_Bool; } }
    public bool is_Arrow { get { return this is Type_Arrow; } }
    public Alcor._IType dtor_Arrow_a0 {
      get {
        var d = this;
        return ((Type_Arrow)d)._a0;
      }
    }
    public Alcor._IType dtor_Arrow_a1 {
      get {
        var d = this;
        return ((Type_Arrow)d)._a1;
      }
    }
    public abstract _IType DowncastClone();
  }
  public class Type_Ind : Type {
    public Type_Ind() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Ind();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.Type_Ind;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.Type.Ind";
      return s;
    }
  }
  public class Type_Bool : Type {
    public Type_Bool() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Bool();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.Type_Bool;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.Type.Bool";
      return s;
    }
  }
  public class Type_Arrow : Type {
    public readonly Alcor._IType _a0;
    public readonly Alcor._IType _a1;
    public Type_Arrow(Alcor._IType _a0, Alcor._IType _a1) : base() {
      this._a0 = _a0;
      this._a1 = _a1;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Arrow(_a0, _a1);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.Type_Arrow;
      return oth != null && object.Equals(this._a0, oth._a0) && object.Equals(this._a1, oth._a1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.Type.Arrow";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._a1);
      s += ")";
      return s;
    }
  }

  public interface _IProofProgram {
    bool is_ProofVar { get; }
    bool is_ProofExpr { get; }
    bool is_ProofAbs { get; }
    bool is_ProofApp { get; }
    bool is_ProofAxiom { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    AlcorProofKernel._IExpr dtor_expr { get; }
    Alcor._IType dtor_tpe { get; }
    Alcor._IProofProgram dtor_body { get; }
    Alcor._IProofProgram dtor_left { get; }
    Alcor._IProofProgram dtor_right { get; }
    Alcor._IProofAxiom dtor_axiom { get; }
    _IProofProgram DowncastClone();
    Alcor._IProofProgram apply1(Alcor._IProofProgram A);
    Alcor._IProofProgram apply2(Alcor._IProofProgram A, Alcor._IProofProgram B);
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public abstract class ProofProgram : _IProofProgram {
    public ProofProgram() {
    }
    private static readonly Alcor._IProofProgram theDefault = create_ProofVar(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Alcor._IProofProgram Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Alcor._IProofProgram> _TYPE = new Dafny.TypeDescriptor<Alcor._IProofProgram>(Alcor.ProofProgram.Default());
    public static Dafny.TypeDescriptor<Alcor._IProofProgram> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IProofProgram create_ProofVar(Dafny.ISequence<Dafny.Rune> name) {
      return new ProofProgram_ProofVar(name);
    }
    public static _IProofProgram create_ProofExpr(AlcorProofKernel._IExpr expr) {
      return new ProofProgram_ProofExpr(expr);
    }
    public static _IProofProgram create_ProofAbs(Dafny.ISequence<Dafny.Rune> name, Alcor._IType tpe, Alcor._IProofProgram body) {
      return new ProofProgram_ProofAbs(name, tpe, body);
    }
    public static _IProofProgram create_ProofApp(Alcor._IProofProgram left, Alcor._IProofProgram right) {
      return new ProofProgram_ProofApp(left, right);
    }
    public static _IProofProgram create_ProofAxiom(Alcor._IProofAxiom axiom) {
      return new ProofProgram_ProofAxiom(axiom);
    }
    public bool is_ProofVar { get { return this is ProofProgram_ProofVar; } }
    public bool is_ProofExpr { get { return this is ProofProgram_ProofExpr; } }
    public bool is_ProofAbs { get { return this is ProofProgram_ProofAbs; } }
    public bool is_ProofApp { get { return this is ProofProgram_ProofApp; } }
    public bool is_ProofAxiom { get { return this is ProofProgram_ProofAxiom; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is ProofProgram_ProofVar) { return ((ProofProgram_ProofVar)d)._name; }
        return ((ProofProgram_ProofAbs)d)._name;
      }
    }
    public AlcorProofKernel._IExpr dtor_expr {
      get {
        var d = this;
        return ((ProofProgram_ProofExpr)d)._expr;
      }
    }
    public Alcor._IType dtor_tpe {
      get {
        var d = this;
        return ((ProofProgram_ProofAbs)d)._tpe;
      }
    }
    public Alcor._IProofProgram dtor_body {
      get {
        var d = this;
        return ((ProofProgram_ProofAbs)d)._body;
      }
    }
    public Alcor._IProofProgram dtor_left {
      get {
        var d = this;
        return ((ProofProgram_ProofApp)d)._left;
      }
    }
    public Alcor._IProofProgram dtor_right {
      get {
        var d = this;
        return ((ProofProgram_ProofApp)d)._right;
      }
    }
    public Alcor._IProofAxiom dtor_axiom {
      get {
        var d = this;
        return ((ProofProgram_ProofAxiom)d)._axiom;
      }
    }
    public abstract _IProofProgram DowncastClone();
    public Alcor._IProofProgram apply1(Alcor._IProofProgram A) {
      return Alcor.ProofProgram.create_ProofApp(this, A);
    }
    public Alcor._IProofProgram apply2(Alcor._IProofProgram A, Alcor._IProofProgram B) {
      return Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofApp(this, A), B);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      Alcor._IProofProgram _source4 = this;
      if (_source4.is_ProofVar) {
        Dafny.ISequence<Dafny.Rune> _89___mcc_h0 = _source4.dtor_name;
        Dafny.ISequence<Dafny.Rune> _90_name = _89___mcc_h0;
        return _90_name;
      } else if (_source4.is_ProofExpr) {
        AlcorProofKernel._IExpr _91___mcc_h1 = _source4.dtor_expr;
        AlcorProofKernel._IExpr _92_expr = _91___mcc_h1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("``"), (_92_expr)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("``"));
      } else if (_source4.is_ProofAbs) {
        Dafny.ISequence<Dafny.Rune> _93___mcc_h2 = _source4.dtor_name;
        Alcor._IType _94___mcc_h3 = _source4.dtor_tpe;
        Alcor._IProofProgram _95___mcc_h4 = _source4.dtor_body;
        Alcor._IProofProgram _96_body = _95___mcc_h4;
        Alcor._IType _97_tpe = _94___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _98_name = _93___mcc_h2;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\\"), _98_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". ")), (_96_body)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else if (_source4.is_ProofApp) {
        Alcor._IProofProgram _99___mcc_h5 = _source4.dtor_left;
        Alcor._IProofProgram _100___mcc_h6 = _source4.dtor_right;
        Alcor._IProofProgram _101_right = _100___mcc_h6;
        Alcor._IProofProgram _102_left = _99___mcc_h5;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_102_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_101_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        Alcor._IProofAxiom _103___mcc_h7 = _source4.dtor_axiom;
        Alcor._IProofAxiom _104_axiom = _103___mcc_h7;
        return (_104_axiom)._ToString();
      }
    }
  }
  public class ProofProgram_ProofVar : ProofProgram {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public ProofProgram_ProofVar(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IProofProgram DowncastClone() {
      if (this is _IProofProgram dt) { return dt; }
      return new ProofProgram_ProofVar(_name);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofProgram_ProofVar;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofProgram.ProofVar";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ProofProgram_ProofExpr : ProofProgram {
    public readonly AlcorProofKernel._IExpr _expr;
    public ProofProgram_ProofExpr(AlcorProofKernel._IExpr expr) : base() {
      this._expr = expr;
    }
    public override _IProofProgram DowncastClone() {
      if (this is _IProofProgram dt) { return dt; }
      return new ProofProgram_ProofExpr(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofProgram_ProofExpr;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofProgram.ProofExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }
  public class ProofProgram_ProofAbs : ProofProgram {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Alcor._IType _tpe;
    public readonly Alcor._IProofProgram _body;
    public ProofProgram_ProofAbs(Dafny.ISequence<Dafny.Rune> name, Alcor._IType tpe, Alcor._IProofProgram body) : base() {
      this._name = name;
      this._tpe = tpe;
      this._body = body;
    }
    public override _IProofProgram DowncastClone() {
      if (this is _IProofProgram dt) { return dt; }
      return new ProofProgram_ProofAbs(_name, _tpe, _body);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofProgram_ProofAbs;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofProgram.ProofAbs";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class ProofProgram_ProofApp : ProofProgram {
    public readonly Alcor._IProofProgram _left;
    public readonly Alcor._IProofProgram _right;
    public ProofProgram_ProofApp(Alcor._IProofProgram left, Alcor._IProofProgram right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IProofProgram DowncastClone() {
      if (this is _IProofProgram dt) { return dt; }
      return new ProofProgram_ProofApp(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofProgram_ProofApp;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofProgram.ProofApp";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class ProofProgram_ProofAxiom : ProofProgram {
    public readonly Alcor._IProofAxiom _axiom;
    public ProofProgram_ProofAxiom(Alcor._IProofAxiom axiom) : base() {
      this._axiom = axiom;
    }
    public override _IProofProgram DowncastClone() {
      if (this is _IProofProgram dt) { return dt; }
      return new ProofProgram_ProofAxiom(_axiom);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofProgram_ProofAxiom;
      return oth != null && object.Equals(this._axiom, oth._axiom);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._axiom));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofProgram.ProofAxiom";
      s += "(";
      s += Dafny.Helpers.ToString(this._axiom);
      s += ")";
      return s;
    }
  }

  public interface _IProofValue {
    bool is_OneProof { get; }
    bool is_OneExpr { get; }
    bool is_OneClosure { get; }
    bool is_OneClosureAxiom { get; }
    AlcorProofKernel._IExpr dtor_proof { get; }
    AlcorProofKernel._IExpr dtor_expr { get; }
    Dafny.ISequence<Dafny.Rune> dtor_argName { get; }
    Alcor._IType dtor_tpe { get; }
    Alcor._IProofProgram dtor_body { get; }
    Alcor._IEnvironment dtor_environment { get; }
    Dafny.ISequence<Alcor._IProofValue> dtor_args { get; }
    Alcor._IProofAxiom dtor_axiom { get; }
    _IProofValue DowncastClone();
    Dafny.ISequence<Dafny.Rune> Summary();
  }
  public abstract class ProofValue : _IProofValue {
    public ProofValue() {
    }
    private static readonly Alcor._IProofValue theDefault = create_OneProof(AlcorProofKernel.Expr.Default());
    public static Alcor._IProofValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Alcor._IProofValue> _TYPE = new Dafny.TypeDescriptor<Alcor._IProofValue>(Alcor.ProofValue.Default());
    public static Dafny.TypeDescriptor<Alcor._IProofValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IProofValue create_OneProof(AlcorProofKernel._IExpr proof) {
      return new ProofValue_OneProof(proof);
    }
    public static _IProofValue create_OneExpr(AlcorProofKernel._IExpr expr) {
      return new ProofValue_OneExpr(expr);
    }
    public static _IProofValue create_OneClosure(Dafny.ISequence<Dafny.Rune> argName, Alcor._IType tpe, Alcor._IProofProgram body, Alcor._IEnvironment environment) {
      return new ProofValue_OneClosure(argName, tpe, body, environment);
    }
    public static _IProofValue create_OneClosureAxiom(Dafny.ISequence<Alcor._IProofValue> args, Alcor._IProofAxiom axiom) {
      return new ProofValue_OneClosureAxiom(args, axiom);
    }
    public bool is_OneProof { get { return this is ProofValue_OneProof; } }
    public bool is_OneExpr { get { return this is ProofValue_OneExpr; } }
    public bool is_OneClosure { get { return this is ProofValue_OneClosure; } }
    public bool is_OneClosureAxiom { get { return this is ProofValue_OneClosureAxiom; } }
    public AlcorProofKernel._IExpr dtor_proof {
      get {
        var d = this;
        return ((ProofValue_OneProof)d)._proof;
      }
    }
    public AlcorProofKernel._IExpr dtor_expr {
      get {
        var d = this;
        return ((ProofValue_OneExpr)d)._expr;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_argName {
      get {
        var d = this;
        return ((ProofValue_OneClosure)d)._argName;
      }
    }
    public Alcor._IType dtor_tpe {
      get {
        var d = this;
        return ((ProofValue_OneClosure)d)._tpe;
      }
    }
    public Alcor._IProofProgram dtor_body {
      get {
        var d = this;
        return ((ProofValue_OneClosure)d)._body;
      }
    }
    public Alcor._IEnvironment dtor_environment {
      get {
        var d = this;
        return ((ProofValue_OneClosure)d)._environment;
      }
    }
    public Dafny.ISequence<Alcor._IProofValue> dtor_args {
      get {
        var d = this;
        return ((ProofValue_OneClosureAxiom)d)._args;
      }
    }
    public Alcor._IProofAxiom dtor_axiom {
      get {
        var d = this;
        return ((ProofValue_OneClosureAxiom)d)._axiom;
      }
    }
    public abstract _IProofValue DowncastClone();
    public Dafny.ISequence<Dafny.Rune> Summary() {
      if ((this).is_OneProof) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proof");
      } else if ((this).is_OneClosure) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proof closure");
      } else if ((this).is_OneExpr) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expr");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("incomplete axiom instantiation");
      }
    }
  }
  public class ProofValue_OneProof : ProofValue {
    public readonly AlcorProofKernel._IExpr _proof;
    public ProofValue_OneProof(AlcorProofKernel._IExpr proof) : base() {
      this._proof = proof;
    }
    public override _IProofValue DowncastClone() {
      if (this is _IProofValue dt) { return dt; }
      return new ProofValue_OneProof(_proof);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofValue_OneProof;
      return oth != null && object.Equals(this._proof, oth._proof);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._proof));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofValue.OneProof";
      s += "(";
      s += Dafny.Helpers.ToString(this._proof);
      s += ")";
      return s;
    }
  }
  public class ProofValue_OneExpr : ProofValue {
    public readonly AlcorProofKernel._IExpr _expr;
    public ProofValue_OneExpr(AlcorProofKernel._IExpr expr) : base() {
      this._expr = expr;
    }
    public override _IProofValue DowncastClone() {
      if (this is _IProofValue dt) { return dt; }
      return new ProofValue_OneExpr(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofValue_OneExpr;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofValue.OneExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }
  public class ProofValue_OneClosure : ProofValue {
    public readonly Dafny.ISequence<Dafny.Rune> _argName;
    public readonly Alcor._IType _tpe;
    public readonly Alcor._IProofProgram _body;
    public readonly Alcor._IEnvironment _environment;
    public ProofValue_OneClosure(Dafny.ISequence<Dafny.Rune> argName, Alcor._IType tpe, Alcor._IProofProgram body, Alcor._IEnvironment environment) : base() {
      this._argName = argName;
      this._tpe = tpe;
      this._body = body;
      this._environment = environment;
    }
    public override _IProofValue DowncastClone() {
      if (this is _IProofValue dt) { return dt; }
      return new ProofValue_OneClosure(_argName, _tpe, _body, _environment);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofValue_OneClosure;
      return oth != null && object.Equals(this._argName, oth._argName) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._body, oth._body) && object.Equals(this._environment, oth._environment);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._argName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._environment));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofValue.OneClosure";
      s += "(";
      s += this._argName.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._environment);
      s += ")";
      return s;
    }
  }
  public class ProofValue_OneClosureAxiom : ProofValue {
    public readonly Dafny.ISequence<Alcor._IProofValue> _args;
    public readonly Alcor._IProofAxiom _axiom;
    public ProofValue_OneClosureAxiom(Dafny.ISequence<Alcor._IProofValue> args, Alcor._IProofAxiom axiom) : base() {
      this._args = args;
      this._axiom = axiom;
    }
    public override _IProofValue DowncastClone() {
      if (this is _IProofValue dt) { return dt; }
      return new ProofValue_OneClosureAxiom(_args, _axiom);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofValue_OneClosureAxiom;
      return oth != null && object.Equals(this._args, oth._args) && object.Equals(this._axiom, oth._axiom);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._axiom));
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofValue.OneClosureAxiom";
      s += "(";
      s += Dafny.Helpers.ToString(this._args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._axiom);
      s += ")";
      return s;
    }
  }
} // end of namespace Alcor

