// Dafny program GeneratedFromDafny.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
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
    public static BigInteger StringToInt(Dafny.ISequence<Dafny.Rune> s) {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune('-'))) {
        return (BigInteger.Zero) - (Wrappers.__default.StringToInt((s).Drop(BigInteger.One)));
      } else if ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((s).Select((new BigInteger((s).Count)) - (BigInteger.One)))) {
        return ((Wrappers.__default.StringToInt((s).Take((new BigInteger((s).Count)) - (BigInteger.One)))) * (new BigInteger(10))) + (Wrappers.__default.charToInt((s).Select((new BigInteger((s).Count)) - (BigInteger.One))));
      } else {
        return Wrappers.__default.StringToInt((s).Take((new BigInteger((s).Count)) - (BigInteger.One)));
      }
    }
    public static BigInteger charToInt(Dafny.Rune d) {
      if ((d) == (new Dafny.Rune('0'))) {
        return BigInteger.Zero;
      } else if ((d) == (new Dafny.Rune('1'))) {
        return BigInteger.One;
      } else if ((d) == (new Dafny.Rune('2'))) {
        return new BigInteger(2);
      } else if ((d) == (new Dafny.Rune('3'))) {
        return new BigInteger(3);
      } else if ((d) == (new Dafny.Rune('4'))) {
        return new BigInteger(4);
      } else if ((d) == (new Dafny.Rune('5'))) {
        return new BigInteger(5);
      } else if ((d) == (new Dafny.Rune('6'))) {
        return new BigInteger(6);
      } else if ((d) == (new Dafny.Rune('7'))) {
        return new BigInteger(7);
      } else if ((d) == (new Dafny.Rune('8'))) {
        return new BigInteger(8);
      } else {
        return new BigInteger(9);
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

  public partial class __default {
    public static AlcorProofKernel._IIdentifier FreshIdentifier(AlcorProofKernel._IIdentifier id, Dafny.ISet<AlcorProofKernel._IIdentifier> freeVars) {
    TAIL_CALL_START:;
      if ((freeVars).Contains(id)) {
        AlcorProofKernel._IIdentifier _in0 = AlcorProofKernel.Identifier.create((id).dtor_name, ((id).dtor_version) + (BigInteger.One), (id).dtor_lbl);
        Dafny.ISet<AlcorProofKernel._IIdentifier> _in1 = freeVars;
        id = _in0;
        freeVars = _in1;
        goto TAIL_CALL_START;
      } else {
        return id;
      }
    }
  }

  public interface _IIdentifier {
    bool is_Identifier { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    BigInteger dtor_version { get; }
    Dafny.ISequence<Dafny.Rune> dtor_lbl { get; }
    _IIdentifier DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public class Identifier : _IIdentifier {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly BigInteger _version;
    public readonly Dafny.ISequence<Dafny.Rune> _lbl;
    public Identifier(Dafny.ISequence<Dafny.Rune> name, BigInteger version, Dafny.ISequence<Dafny.Rune> lbl) {
      this._name = name;
      this._version = version;
      this._lbl = lbl;
    }
    public _IIdentifier DowncastClone() {
      if (this is _IIdentifier dt) { return dt; }
      return new Identifier(_name, _version, _lbl);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Identifier;
      return oth != null && object.Equals(this._name, oth._name) && this._version == oth._version && object.Equals(this._lbl, oth._lbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._version));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lbl));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Identifier.Identifier";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._version);
      s += ", ";
      s += this._lbl.ToVerbatimString(true);
      s += ")";
      return s;
    }
    private static readonly AlcorProofKernel._IIdentifier theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, BigInteger.Zero, Dafny.Sequence<Dafny.Rune>.Empty);
    public static AlcorProofKernel._IIdentifier Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorProofKernel._IIdentifier> _TYPE = new Dafny.TypeDescriptor<AlcorProofKernel._IIdentifier>(AlcorProofKernel.Identifier.Default());
    public static Dafny.TypeDescriptor<AlcorProofKernel._IIdentifier> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IIdentifier create(Dafny.ISequence<Dafny.Rune> name, BigInteger version, Dafny.ISequence<Dafny.Rune> lbl) {
      return new Identifier(name, version, lbl);
    }
    public static _IIdentifier create_Identifier(Dafny.ISequence<Dafny.Rune> name, BigInteger version, Dafny.ISequence<Dafny.Rune> lbl) {
      return create(name, version, lbl);
    }
    public bool is_Identifier { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public BigInteger dtor_version {
      get {
        return this._version;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_lbl {
      get {
        return this._lbl;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_name, ((!((this).dtor_lbl).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("@"), (this).dtor_lbl)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), ((((this).dtor_version).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("@"), Wrappers.__default.IntToString((this).dtor_version)))));
    }
  }

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
    AlcorProofKernel._IIdentifier dtor_id { get; }
    AlcorProofKernel._IExpr dtor_body { get; }
    _IExpr DowncastClone();
    Dafny.ISet<AlcorProofKernel._IIdentifier> FreeVars();
    AlcorProofKernel._IExpr Bind(AlcorProofKernel._IIdentifier id, AlcorProofKernel._IExpr expr, Dafny.ISet<AlcorProofKernel._IIdentifier> freeVars);
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
    public static _IExpr create_Var(AlcorProofKernel._IIdentifier id) {
      return new Expr_Var(id);
    }
    public static _IExpr create_Abs(AlcorProofKernel._IIdentifier id, AlcorProofKernel._IExpr body) {
      return new Expr_Abs(id, body);
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
    public AlcorProofKernel._IIdentifier dtor_id {
      get {
        var d = this;
        if (d is Expr_Var) { return ((Expr_Var)d)._id; }
        return ((Expr_Abs)d)._id;
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
    public Dafny.ISet<AlcorProofKernel._IIdentifier> FreeVars() {
      if (((this).is_True) || ((this).is_False)) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements();
      } else if ((((((this).is_And) || ((this).is_Imp)) || ((this).is_Eq)) || ((this).is_Or)) || ((this).is_App)) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.Union(((this).dtor_left).FreeVars(), ((this).dtor_right).FreeVars());
      } else if ((this).is_Var) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements((this).dtor_id);
      } else if ((this).is_Abs) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.Difference(((this).dtor_body).FreeVars(), Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements((this).dtor_id));
      } else if ((this).is_Forall) {
        return ((this).dtor_body).FreeVars();
      } else {
        _System._ITuple0 _source0 = _System.Tuple0.create();
        throw new System.Exception("unexpected control point");
      }
    }
    public AlcorProofKernel._IExpr Bind(AlcorProofKernel._IIdentifier id, AlcorProofKernel._IExpr expr, Dafny.ISet<AlcorProofKernel._IIdentifier> freeVars) {
      AlcorProofKernel._IExpr _source1 = this;
      if (_source1.is_True) {
        return this;
      } else if (_source1.is_False) {
        return this;
      } else if (_source1.is_And) {
        AlcorProofKernel._IExpr __mcc_h0 = _source1.dtor_left;
        AlcorProofKernel._IExpr __mcc_h1 = _source1.dtor_right;
        AlcorProofKernel._IExpr right = __mcc_h1;
        AlcorProofKernel._IExpr left = __mcc_h0;
        return AlcorProofKernel.Expr.create_And((left).Bind(id, expr, (expr).FreeVars()), (right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source1.is_Imp) {
        AlcorProofKernel._IExpr __mcc_h2 = _source1.dtor_left;
        AlcorProofKernel._IExpr __mcc_h3 = _source1.dtor_right;
        AlcorProofKernel._IExpr right = __mcc_h3;
        AlcorProofKernel._IExpr left = __mcc_h2;
        return AlcorProofKernel.Expr.create_Imp((left).Bind(id, expr, (expr).FreeVars()), (right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source1.is_Eq) {
        AlcorProofKernel._IExpr __mcc_h4 = _source1.dtor_left;
        AlcorProofKernel._IExpr _10___mcc_h5 = _source1.dtor_right;
        AlcorProofKernel._IExpr _11_right = _10___mcc_h5;
        AlcorProofKernel._IExpr _12_left = __mcc_h4;
        return AlcorProofKernel.Expr.create_Eq((_12_left).Bind(id, expr, (expr).FreeVars()), (_11_right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source1.is_Or) {
        AlcorProofKernel._IExpr _13___mcc_h6 = _source1.dtor_left;
        AlcorProofKernel._IExpr _14___mcc_h7 = _source1.dtor_right;
        AlcorProofKernel._IExpr _15_right = _14___mcc_h7;
        AlcorProofKernel._IExpr _16_left = _13___mcc_h6;
        return AlcorProofKernel.Expr.create_Or((_16_left).Bind(id, expr, (expr).FreeVars()), (_15_right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source1.is_Var) {
        AlcorProofKernel._IIdentifier _17___mcc_h8 = _source1.dtor_id;
        AlcorProofKernel._IIdentifier _18_i = _17___mcc_h8;
        if (object.Equals(_18_i, id)) {
          return expr;
        } else {
          return this;
        }
      } else if (_source1.is_Abs) {
        AlcorProofKernel._IIdentifier _19___mcc_h9 = _source1.dtor_id;
        AlcorProofKernel._IExpr _20___mcc_h10 = _source1.dtor_body;
        AlcorProofKernel._IExpr _21_body = _20___mcc_h10;
        AlcorProofKernel._IIdentifier _22_i = _19___mcc_h9;
        if (object.Equals(_22_i, id)) {
          return this;
        } else if ((freeVars).Contains(_22_i)) {
          AlcorProofKernel._IIdentifier _23_i_k = AlcorProofKernel.__default.FreshIdentifier(_22_i, freeVars);
          AlcorProofKernel._IExpr _24_newAbs = AlcorProofKernel.Expr.create_Abs(_23_i_k, (_21_body).Bind(_22_i, AlcorProofKernel.Expr.create_Var(_23_i_k), (AlcorProofKernel.Expr.create_Var(_23_i_k)).FreeVars()));
          return (_24_newAbs).Bind(id, expr, freeVars);
        } else {
          return AlcorProofKernel.Expr.create_Abs(_22_i, (_21_body).Bind(id, expr, freeVars));
        }
      } else if (_source1.is_App) {
        AlcorProofKernel._IExpr _25___mcc_h11 = _source1.dtor_left;
        AlcorProofKernel._IExpr _26___mcc_h12 = _source1.dtor_right;
        AlcorProofKernel._IExpr _27_right = _26___mcc_h12;
        AlcorProofKernel._IExpr _28_left = _25___mcc_h11;
        return AlcorProofKernel.Expr.create_App((_28_left).Bind(id, expr, (expr).FreeVars()), (_27_right).Bind(id, expr, (expr).FreeVars()));
      } else {
        AlcorProofKernel._IExpr _29___mcc_h13 = _source1.dtor_body;
        AlcorProofKernel._IExpr _30_body = _29___mcc_h13;
        return AlcorProofKernel.Expr.create_Forall((_30_body).Bind(id, expr, (expr).FreeVars()));
      }
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
        return ((this).dtor_id)._ToString();
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      }
    }
    public Dafny.ISequence<Dafny.Rune> ToStringWrap(BigInteger outerPriority) {
      Dafny.ISequence<Dafny.Rune> _31_r = (this)._ToString();
      if ((outerPriority) >= ((this).Priority())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _31_r), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        return _31_r;
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
      BigInteger _32_p = (this).Priority();
      if (((this).is_Imp) && (((this).dtor_right).is_False)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), ((this).dtor_left).ToStringWrap(_32_p));
      } else if (((((this).is_And) || ((this).is_Or)) || ((this).is_Eq)) || ((this).is_Imp)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_left).ToStringWrap(_32_p), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), (this).Operator()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_right).ToStringWrap(_32_p));
      } else if ((this).is_Abs) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\"), ((this).dtor_id)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((this).dtor_body).ToStringWrap((_32_p) + (BigInteger.One)));
      } else if ((this).is_App) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_left).ToStringWrap(_32_p), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_right).ToStringWrap(_32_p));
      } else if ((this).is_Forall) {
        if (((this).dtor_body).is_Abs) {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("forall "), (((this).dtor_body).dtor_id)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" :: ")), (((this).dtor_body).dtor_body).ToStringWrap((_32_p) + (BigInteger.One)));
        } else {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("forall "), ((this).dtor_body).ToStringWrap((_32_p) + (BigInteger.One)));
        }
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
    public readonly AlcorProofKernel._IIdentifier _id;
    public Expr_Var(AlcorProofKernel._IIdentifier id) : base() {
      this._id = id;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Var(_id);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Var;
      return oth != null && object.Equals(this._id, oth._id);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Var";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ")";
      return s;
    }
  }
  public class Expr_Abs : Expr {
    public readonly AlcorProofKernel._IIdentifier _id;
    public readonly AlcorProofKernel._IExpr _body;
    public Expr_Abs(AlcorProofKernel._IIdentifier id, AlcorProofKernel._IExpr body) : base() {
      this._id = id;
      this._body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Abs(_id, _body);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Abs;
      return oth != null && object.Equals(this._id, oth._id) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Abs";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
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
    public static Wrappers._IResult<AlcorProofKernel._IExpr> ImpIntro(AlcorProofKernel._IExpr hypothesis, AlcorProofKernel._IExpr conclusion, Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>> pHypothesis) {
      AlcorProofKernel._IExpr _33_p = hypothesis;
      Wrappers._IResult<AlcorProofKernel._IExpr> _34_valueOrError0 = Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>>(pHypothesis)(_33_p);
      if ((_34_valueOrError0).IsFailure()) {
        return (_34_valueOrError0).PropagateFailure<AlcorProofKernel._IExpr>();
      } else {
        AlcorProofKernel._IExpr _35_result = (_34_valueOrError0).Extract();
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(AlcorProofKernel.Expr.create_Imp(hypothesis, (_35_result)));
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> ForallElim(AlcorProofKernel._IExpr theorem, AlcorProofKernel._IExpr instance) {
      if (!(((theorem)).is_Forall)) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("To apply ForallElim, you need to pass a proven forall expression as the first parameter, but got a proof "), ((theorem))._ToString()));
      } else if (!((((theorem)).dtor_body).is_Abs)) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("To apply ForallElim, the forall must be over a lambda, but got "), (((theorem)).dtor_body)._ToString()));
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(((((theorem)).dtor_body).dtor_body).Bind((((theorem)).dtor_body).dtor_id, instance, (instance).FreeVars()));
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> ForallIntro(AlcorProofKernel._IExpr theorem, AlcorProofKernel._IIdentifier id) {
      return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(AlcorProofKernel.Expr.create_Forall(AlcorProofKernel.Expr.create_Abs(id, (theorem))));
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> ForallRename(AlcorProofKernel._IExpr theorem, AlcorProofKernel._IIdentifier freeVar, AlcorProofKernel._IExpr Body, AlcorProofKernel._IIdentifier Id) {
      if (object.Equals((theorem), AlcorProofKernel.Expr.create_Forall(AlcorProofKernel.Expr.create_Abs(freeVar, (Body).Bind(Id, AlcorProofKernel.Expr.create_Var(freeVar), (AlcorProofKernel.Expr.create_Var(freeVar)).FreeVars()))))) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(AlcorProofKernel.Expr.create_Forall(AlcorProofKernel.Expr.create_Abs(Id, Body)));
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ForallRename is not consistent"));
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
    public static Wrappers._IResult<Alcor._IProofValue> ExecuteProof(Alcor._IProofProgram program, Alcor._IProofEnv environment) {
      Alcor._IProofProgram _source2 = program;
      if (_source2.is_ProofVar) {
        Dafny.ISequence<Dafny.Rune> _36___mcc_h0 = _source2.dtor_name;
        Dafny.ISequence<Dafny.Rune> _37_name = _36___mcc_h0;
        return (environment).Lookup(_37_name);
      } else if (_source2.is_ProofExpr) {
        AlcorProofKernel._IExpr _38___mcc_h1 = _source2.dtor_expr;
        AlcorProofKernel._IExpr _39_expr = _38___mcc_h1;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneExpr(_39_expr));
      } else if (_source2.is_ProofAbs) {
        Dafny.ISequence<Dafny.Rune> _40___mcc_h2 = _source2.dtor_name;
        Alcor._IType _41___mcc_h3 = _source2.dtor_tpe;
        Alcor._IProofProgram _42___mcc_h4 = _source2.dtor_body;
        Alcor._IProofProgram _43_body = _42___mcc_h4;
        Alcor._IType _44_tpe = _41___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _45_name = _40___mcc_h2;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosure(_45_name, _44_tpe, _43_body, environment));
      } else if (_source2.is_ProofApp) {
        Alcor._IProofProgram _46___mcc_h5 = _source2.dtor_left;
        Alcor._IProofProgram _47___mcc_h6 = _source2.dtor_right;
        Alcor._IProofProgram _48_right = _47___mcc_h6;
        Alcor._IProofProgram _49_left = _46___mcc_h5;
        Wrappers._IResult<Alcor._IProofValue> _50_valueOrError0 = Alcor.__default.ExecuteProof(_49_left, environment);
        if ((_50_valueOrError0).IsFailure()) {
          return (_50_valueOrError0).PropagateFailure<Alcor._IProofValue>();
        } else {
          Alcor._IProofValue _51_result = (_50_valueOrError0).Extract();
          if ((_51_result).is_OneClosure) {
            Wrappers._IResult<Alcor._IProofValue> _52_valueOrError1 = Alcor.__default.ExecuteProof(_48_right, environment);
            if ((_52_valueOrError1).IsFailure()) {
              return (_52_valueOrError1).PropagateFailure<Alcor._IProofValue>();
            } else {
              Alcor._IProofValue _53_argument = (_52_valueOrError1).Extract();
              return Alcor.__default.ExecuteProof((_51_result).dtor_body, Alcor.ProofEnv.create_ProofEnvCons((_51_result).dtor_argName, _53_argument, (_51_result).dtor_environment));
            }
          } else if ((_51_result).is_OneClosureAxiom) {
            Wrappers._IResult<Alcor._IProofValue> _54_valueOrError2 = Alcor.__default.ExecuteProof(_48_right, environment);
            if ((_54_valueOrError2).IsFailure()) {
              return (_54_valueOrError2).PropagateFailure<Alcor._IProofValue>();
            } else {
              Alcor._IProofValue _55_argument = (_54_valueOrError2).Extract();
              if ((((_51_result).dtor_axiom).Arity()) == ((new BigInteger(((_51_result).dtor_args).Count)) + (BigInteger.One))) {
                return ((_51_result).dtor_axiom).ApplyArgs(Dafny.Sequence<Alcor._IProofValue>.Concat((_51_result).dtor_args, Dafny.Sequence<Alcor._IProofValue>.FromElements(_55_argument)), environment);
              } else {
                return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosureAxiom(Dafny.Sequence<Alcor._IProofValue>.Concat((_51_result).dtor_args, Dafny.Sequence<Alcor._IProofValue>.FromElements(_55_argument)), (_51_result).dtor_axiom));
              }
            }
          } else {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Left of application was not a closure"));
          }
        }
      } else {
        Alcor._IProofAxiom _56___mcc_h7 = _source2.dtor_axiom;
        Alcor._IProofAxiom _57_axiom = _56___mcc_h7;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosureAxiom(Dafny.Sequence<Alcor._IProofValue>.FromElements(), _57_axiom));
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> CheckProof(Alcor._IProofProgram program, Alcor._IProofEnv environment, AlcorProofKernel._IExpr expected) {
      Wrappers._IResult<Alcor._IProofValue> _58_valueOrError0 = Alcor.__default.ExecuteProof(program, environment);
      if ((_58_valueOrError0).IsFailure()) {
        return (_58_valueOrError0).PropagateFailure<AlcorProofKernel._IExpr>();
      } else {
        Alcor._IProofValue _59_result = (_58_valueOrError0).Extract();
        if (((_59_result).is_OneClosure) || ((_59_result).is_OneClosureAxiom)) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a closure proof")));
        } else if ((_59_result).is_OneExpr) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a simple expression")));
        } else if (!object.Equals(AlcorProofKernel.Proof.GetExpr((_59_result).dtor_proof), expected)) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" but got a proof of ")), (AlcorProofKernel.Proof.GetExpr((_59_result).dtor_proof))._ToString()));
        } else {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_59_result).dtor_proof);
        }
      }
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> checkGoalAgainstExpr(Alcor._IProofValue pv, AlcorProofKernel._IExpr expr, Alcor._IProofProgram pr) {
      if (!((pv).is_OneProof)) {
        return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DummyProofFinder did not generate a proof but "), (pv).Summary()));
      } else {
        AlcorProofKernel._IExpr _60_p = (pv).dtor_proof;
        if (object.Equals(AlcorProofKernel.Proof.GetExpr(_60_p), expr)) {
          return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Success(_System.Tuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>.create(_60_p, pr));
        } else {
          return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DummyProofFinder was looking for a proof of "), (expr)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" but returned a proof of ")), (AlcorProofKernel.Proof.GetExpr(_60_p))._ToString()));
        }
      }
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> AndProofFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      if (!(((expr).dtor_left).is_And)) {
        result = Alcor.__default.CantApplyAndProofFinder;
        return result;
      }
      AlcorProofKernel._IExpr _61_goal;
      _61_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _62_env;
      _62_env = (expr).dtor_left;
      AlcorProofKernel._IExpr _63_A0;
      _63_A0 = (_62_env).dtor_left;
      AlcorProofKernel._IExpr _64_tail;
      _64_tail = (_62_env).dtor_right;
      if ((_63_A0).is_And) {
        if (object.Equals((_63_A0).dtor_left, _61_goal)) {
          Alcor._IProofProgram _65_proofProgram;
          _65_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_62_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _66_r;
          Wrappers._IResult<Alcor._IProofValue> _67_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
          _67_valueOrError0 = Alcor.__default.ExecuteProof(_65_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_67_valueOrError0).IsFailure()) {
            result = (_67_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _66_r = (_67_valueOrError0).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_66_r, expr, _65_proofProgram);
          return result;
        }
        if (object.Equals((_63_A0).dtor_right, _61_goal)) {
          Alcor._IProofProgram _68_proofProgram;
          _68_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_62_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimRight()).apply1((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _69_r;
          Wrappers._IResult<Alcor._IProofValue> _70_valueOrError1 = Wrappers.Result<Alcor._IProofValue>.Default();
          _70_valueOrError1 = Alcor.__default.ExecuteProof(_68_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_70_valueOrError1).IsFailure()) {
            result = (_70_valueOrError1).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _69_r = (_70_valueOrError1).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_69_r, expr, _68_proofProgram);
          return result;
        }
      }
      if ((_64_tail).is_And) {
        AlcorProofKernel._IExpr _71_A1;
        _71_A1 = (_64_tail).dtor_left;
        if (object.Equals(_61_goal, AlcorProofKernel.Expr.create_And(_63_A0, _71_A1))) {
          Alcor._IProofProgram _72_proofProgram;
          _72_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_62_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndIntro()).apply2((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))))));
          Alcor._IProofValue _73_r;
          Wrappers._IResult<Alcor._IProofValue> _74_valueOrError2 = Wrappers.Result<Alcor._IProofValue>.Default();
          _74_valueOrError2 = Alcor.__default.ExecuteProof(_72_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_74_valueOrError2).IsFailure()) {
            result = (_74_valueOrError2).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _73_r = (_74_valueOrError2).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_73_r, expr, _72_proofProgram);
          return result;
        }
        if (object.Equals(_61_goal, AlcorProofKernel.Expr.create_And(_71_A1, _63_A0))) {
          Alcor._IProofProgram _75_proofProgram;
          _75_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_62_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndIntro()).apply2((Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))), (Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _76_r;
          Wrappers._IResult<Alcor._IProofValue> _77_valueOrError3 = Wrappers.Result<Alcor._IProofValue>.Default();
          _77_valueOrError3 = Alcor.__default.ExecuteProof(_75_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_77_valueOrError3).IsFailure()) {
            result = (_77_valueOrError3).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _76_r = (_77_valueOrError3).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_76_r, expr, _75_proofProgram);
          return result;
        }
      }
      result = Alcor.__default.CantApplyAndProofFinder;
      return result;
      return result;
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> LookupProofFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      AlcorProofKernel._IExpr _78_goal;
      _78_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _79_env;
      _79_env = (expr).dtor_left;
      AlcorProofKernel._IExpr _80_envSearch;
      _80_envSearch = _79_env;
      BigInteger _81_i;
      _81_i = BigInteger.Zero;
      while (((_80_envSearch).is_And) && (!object.Equals((_80_envSearch).dtor_left, _78_goal))) {
        _80_envSearch = (_80_envSearch).dtor_right;
        _81_i = (_81_i) + (BigInteger.One);
      }
      if (((_80_envSearch).is_And) && (object.Equals((_80_envSearch).dtor_left, _78_goal))) {
        Alcor._IProofProgram _82_proofElem;
        _82_proofElem = Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"));
        while ((_81_i).Sign != 0) {
          _82_proofElem = Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofAxiom(Alcor.ProofAxiom.create_AndElimRight()), _82_proofElem);
          _81_i = (_81_i) - (BigInteger.One);
        }
        Alcor._IProofProgram _83_proofProgram;
        _83_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_79_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofAxiom(Alcor.ProofAxiom.create_AndElimLeft()), _82_proofElem)));
        Alcor._IProofValue _84_r;
        Wrappers._IResult<Alcor._IProofValue> _85_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
        _85_valueOrError0 = Alcor.__default.ExecuteProof(_83_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
        if ((_85_valueOrError0).IsFailure()) {
          result = (_85_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
          return result;
        }
        _84_r = (_85_valueOrError0).Extract();
        result = Alcor.__default.checkGoalAgainstExpr(_84_r, expr, _83_proofProgram);
        return result;
      }
      result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not apply LookupProofFinder"));
      return result;
      return result;
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> ModusPonensFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      AlcorProofKernel._IExpr _86_goal;
      _86_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _87_env;
      _87_env = (expr).dtor_left;
      if (!((_87_env).is_And)) {
        result = Alcor.__default.CantApplyModusPonensFinder;
        return result;
      }
      AlcorProofKernel._IExpr _88_A0;
      _88_A0 = (_87_env).dtor_left;
      AlcorProofKernel._IExpr _89_tail;
      _89_tail = (_87_env).dtor_right;
      if (!((_89_tail).is_And)) {
        result = Alcor.__default.CantApplyModusPonensFinder;
        return result;
      }
      AlcorProofKernel._IExpr _90_A1;
      _90_A1 = (_89_tail).dtor_left;
      if ((((_88_A0).is_Imp) && (object.Equals((_88_A0).dtor_right, _86_goal))) && (object.Equals(_90_A1, (_88_A0).dtor_left))) {
        Alcor._IProofProgram _91_proofProgram;
        _91_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_87_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))), (Alcor.ProofAxiom.create_ImpElim()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB")), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A")))))));
        Alcor._IProofValue _92_r;
        Wrappers._IResult<Alcor._IProofValue> _93_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
        _93_valueOrError0 = Alcor.__default.ExecuteProof(_91_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
        if ((_93_valueOrError0).IsFailure()) {
          result = (_93_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
          return result;
        }
        _92_r = (_93_valueOrError0).Extract();
        result = Alcor.__default.checkGoalAgainstExpr(_92_r, expr, _91_proofProgram);
        return result;
      }
      if ((((_90_A1).is_Imp) && (object.Equals((_90_A1).dtor_right, _86_goal))) && (object.Equals(_88_A0, (_90_A1).dtor_left))) {
        Alcor._IProofProgram _94_proofProgram;
        _94_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_87_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))), (Alcor.ProofAxiom.create_ImpElim()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB")), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A")))))));
        Alcor._IProofValue _95_r;
        Wrappers._IResult<Alcor._IProofValue> _96_valueOrError1 = Wrappers.Result<Alcor._IProofValue>.Default();
        _96_valueOrError1 = Alcor.__default.ExecuteProof(_94_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
        if ((_96_valueOrError1).IsFailure()) {
          result = (_96_valueOrError1).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
          return result;
        }
        _95_r = (_96_valueOrError1).Extract();
        result = Alcor.__default.checkGoalAgainstExpr(_95_r, expr, _94_proofProgram);
        return result;
      }
      result = Alcor.__default.CantApplyModusPonensFinder;
      return result;
      return result;
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> DummyProofFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>> _97_checkGoal;
      _97_checkGoal = Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>>>>((_98_expr) => ((System.Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>>)((_99_pv, _100_pr) => {
        return Alcor.__default.checkGoalAgainstExpr(_99_pv, _98_expr, _100_pr);
      })))(expr);
      if (!((expr).is_Imp)) {
        result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alcor requires an implication"));
        return result;
      }
      AlcorProofKernel._IExpr _101_goal;
      _101_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _102_env;
      _102_env = (expr).dtor_left;
      if ((_101_goal).is_Imp) {
        Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> _103_proofOfConclusion;
        Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> _out0;
        _out0 = Alcor.__default.DummyProofFinder(AlcorProofKernel.Expr.create_Imp(AlcorProofKernel.Expr.create_And((_101_goal).dtor_left, _102_env), (_101_goal).dtor_right));
        _103_proofOfConclusion = _out0;
        if ((_103_proofOfConclusion).is_Success) {
          Alcor._IProofEnv _104_execEnv;
          _104_execEnv = Alcor.ProofEnv.create_ProofEnvCons(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b"), Alcor.ProofValue.create_OneProof(((_103_proofOfConclusion).dtor_value).dtor__0), Alcor.ProofEnv.create_ProofEnvNil());
          Alcor._IProofProgram _105_proofProgramInner;
          _105_proofProgramInner = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_102_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr((_101_goal).dtor_left), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proofOfA"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_ImpElim()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b")), (Alcor.ProofAxiom.create_AndIntro()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proofOfA")), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))))));
          Alcor._IProofValue _106_r;
          Wrappers._IResult<Alcor._IProofValue> _107_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
          _107_valueOrError0 = Alcor.__default.ExecuteProof(_105_proofProgramInner, _104_execEnv);
          if ((_107_valueOrError0).IsFailure()) {
            result = (_107_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _106_r = (_107_valueOrError0).Extract();
          Alcor._IProofProgram _108_proofProgram;
          _108_proofProgram = Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b"), Alcor.Type.create_Bool(), ((_103_proofOfConclusion).dtor_value).dtor__1, _105_proofProgramInner);
          result = Dafny.Helpers.Id<Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>>>(_97_checkGoal)(_106_r, _108_proofProgram);
          return result;
        }
      }
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> _out1;
      _out1 = Alcor.__default.AndProofFinder(expr);
      result = _out1;
      if ((result).is_Success) {
        return result;
      }
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> _out2;
      _out2 = Alcor.__default.ModusPonensFinder(expr);
      result = _out2;
      if ((result).is_Success) {
        return result;
      }
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> _out3;
      _out3 = Alcor.__default.LookupProofFinder(expr);
      result = _out3;
      if ((result).is_Success) {
        return result;
      }
      result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not find a simple proof of "), (expr)._ToString()));
      return result;
      return result;
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> CantApplyAndProofFinder {
      get {
        return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Can't apply AndElim proof finder"));
      }
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> CantApplyModusPonensFinder {
      get {
        return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Can't apply ModusPonensFinder"));
      }
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
      Alcor._IProofProgram _source3 = this;
      if (_source3.is_ProofVar) {
        Dafny.ISequence<Dafny.Rune> _109___mcc_h0 = _source3.dtor_name;
        Dafny.ISequence<Dafny.Rune> _110_name = _109___mcc_h0;
        return _110_name;
      } else if (_source3.is_ProofExpr) {
        AlcorProofKernel._IExpr _111___mcc_h1 = _source3.dtor_expr;
        AlcorProofKernel._IExpr _112_expr = _111___mcc_h1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("``"), (_112_expr)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("``"));
      } else if (_source3.is_ProofAbs) {
        Dafny.ISequence<Dafny.Rune> _113___mcc_h2 = _source3.dtor_name;
        Alcor._IType _114___mcc_h3 = _source3.dtor_tpe;
        Alcor._IProofProgram _115___mcc_h4 = _source3.dtor_body;
        Alcor._IProofProgram _116_body = _115___mcc_h4;
        Alcor._IType _117_tpe = _114___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _118_name = _113___mcc_h2;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\\"), _118_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". ")), (_116_body)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else if (_source3.is_ProofApp) {
        Alcor._IProofProgram _119___mcc_h5 = _source3.dtor_left;
        Alcor._IProofProgram _120___mcc_h6 = _source3.dtor_right;
        Alcor._IProofProgram _source4 = _119___mcc_h5;
        if (_source4.is_ProofVar) {
          Dafny.ISequence<Dafny.Rune> _121___mcc_h7 = _source4.dtor_name;
          Alcor._IProofProgram _122_right = _120___mcc_h6;
          Alcor._IProofProgram _123_left = _119___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_123_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_122_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else if (_source4.is_ProofExpr) {
          AlcorProofKernel._IExpr _124___mcc_h9 = _source4.dtor_expr;
          Alcor._IProofProgram _125_right = _120___mcc_h6;
          Alcor._IProofProgram _126_left = _119___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_126_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_125_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else if (_source4.is_ProofAbs) {
          Dafny.ISequence<Dafny.Rune> _127___mcc_h11 = _source4.dtor_name;
          Alcor._IType _128___mcc_h12 = _source4.dtor_tpe;
          Alcor._IProofProgram _129___mcc_h13 = _source4.dtor_body;
          Alcor._IProofProgram _130_varContent = _120___mcc_h6;
          Alcor._IProofProgram _131_body = _129___mcc_h13;
          Alcor._IType _132_tpe = _128___mcc_h12;
          Dafny.ISequence<Dafny.Rune> _133_varName = _127___mcc_h11;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("var "), _133_varName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_132_tpe)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" := ")), (_130_varContent)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), (_131_body)._ToString());
        } else if (_source4.is_ProofApp) {
          Alcor._IProofProgram _134___mcc_h17 = _source4.dtor_left;
          Alcor._IProofProgram _135___mcc_h18 = _source4.dtor_right;
          Alcor._IProofProgram _136_right = _120___mcc_h6;
          Alcor._IProofProgram _137_left = _119___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_137_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_136_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          Alcor._IProofAxiom _138___mcc_h21 = _source4.dtor_axiom;
          Alcor._IProofProgram _139_right = _120___mcc_h6;
          Alcor._IProofProgram _140_left = _119___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_140_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_139_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else {
        Alcor._IProofAxiom _141___mcc_h23 = _source3.dtor_axiom;
        Alcor._IProofAxiom _142_axiom = _141___mcc_h23;
        return (_142_axiom)._ToString();
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
    Alcor._IProofEnv dtor_environment { get; }
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
    public static _IProofValue create_OneClosure(Dafny.ISequence<Dafny.Rune> argName, Alcor._IType tpe, Alcor._IProofProgram body, Alcor._IProofEnv environment) {
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
    public Alcor._IProofEnv dtor_environment {
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
    public readonly Alcor._IProofEnv _environment;
    public ProofValue_OneClosure(Dafny.ISequence<Dafny.Rune> argName, Alcor._IType tpe, Alcor._IProofProgram body, Alcor._IProofEnv environment) : base() {
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

  public interface _IProofEnv {
    bool is_ProofEnvNil { get; }
    bool is_ProofEnvCons { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Alcor._IProofValue dtor_value { get; }
    Alcor._IProofEnv dtor_tail { get; }
    _IProofEnv DowncastClone();
    Wrappers._IResult<Alcor._IProofValue> Lookup(Dafny.ISequence<Dafny.Rune> searchName);
  }
  public abstract class ProofEnv : _IProofEnv {
    public ProofEnv() {
    }
    private static readonly Alcor._IProofEnv theDefault = create_ProofEnvNil();
    public static Alcor._IProofEnv Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Alcor._IProofEnv> _TYPE = new Dafny.TypeDescriptor<Alcor._IProofEnv>(Alcor.ProofEnv.Default());
    public static Dafny.TypeDescriptor<Alcor._IProofEnv> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IProofEnv create_ProofEnvNil() {
      return new ProofEnv_ProofEnvNil();
    }
    public static _IProofEnv create_ProofEnvCons(Dafny.ISequence<Dafny.Rune> name, Alcor._IProofValue @value, Alcor._IProofEnv tail) {
      return new ProofEnv_ProofEnvCons(name, @value, tail);
    }
    public bool is_ProofEnvNil { get { return this is ProofEnv_ProofEnvNil; } }
    public bool is_ProofEnvCons { get { return this is ProofEnv_ProofEnvCons; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((ProofEnv_ProofEnvCons)d)._name;
      }
    }
    public Alcor._IProofValue dtor_value {
      get {
        var d = this;
        return ((ProofEnv_ProofEnvCons)d)._value;
      }
    }
    public Alcor._IProofEnv dtor_tail {
      get {
        var d = this;
        return ((ProofEnv_ProofEnvCons)d)._tail;
      }
    }
    public abstract _IProofEnv DowncastClone();
    public Wrappers._IResult<Alcor._IProofValue> Lookup(Dafny.ISequence<Dafny.Rune> searchName) {
      _IProofEnv _this = this;
    TAIL_CALL_START:;
      if ((_this).is_ProofEnvNil) {
        return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Did not find "), searchName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" in the proof environment")));
      } else if (((_this).dtor_name).Equals(searchName)) {
        return Wrappers.Result<Alcor._IProofValue>.create_Success((_this).dtor_value);
      } else {
        var _in2 = (_this).dtor_tail;
        Dafny.ISequence<Dafny.Rune> _in3 = searchName;
        _this = _in2;
        searchName = _in3;
        goto TAIL_CALL_START;
      }
    }
  }
  public class ProofEnv_ProofEnvNil : ProofEnv {
    public ProofEnv_ProofEnvNil() : base() {
    }
    public override _IProofEnv DowncastClone() {
      if (this is _IProofEnv dt) { return dt; }
      return new ProofEnv_ProofEnvNil();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofEnv_ProofEnvNil;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofEnv.ProofEnvNil";
      return s;
    }
  }
  public class ProofEnv_ProofEnvCons : ProofEnv {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Alcor._IProofValue _value;
    public readonly Alcor._IProofEnv _tail;
    public ProofEnv_ProofEnvCons(Dafny.ISequence<Dafny.Rune> name, Alcor._IProofValue @value, Alcor._IProofEnv tail) : base() {
      this._name = name;
      this._value = @value;
      this._tail = tail;
    }
    public override _IProofEnv DowncastClone() {
      if (this is _IProofEnv dt) { return dt; }
      return new ProofEnv_ProofEnvCons(_name, _value, _tail);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofEnv_ProofEnvCons;
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
      string s = "Alcor.ProofEnv.ProofEnvCons";
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
    bool is_ForallElim { get; }
    bool is_ForallIntro { get; }
    _IProofAxiom DowncastClone();
    Alcor._IProofProgram apply1(Alcor._IProofProgram A);
    Alcor._IProofProgram apply2(Alcor._IProofProgram A, Alcor._IProofProgram B);
    Dafny.ISequence<Dafny.Rune> _ToString();
    BigInteger Arity();
    Wrappers._IResult<AlcorProofKernel._IExpr> ExtractProof(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i);
    Wrappers._IResult<AlcorProofKernel._IExpr> ExtractExpr(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i);
    Wrappers._IResult<Alcor._IProofValue> ApplyArgs(Dafny.ISequence<Alcor._IProofValue> args, Alcor._IProofEnv environment);
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
    public static _IProofAxiom create_ForallElim() {
      return new ProofAxiom_ForallElim();
    }
    public static _IProofAxiom create_ForallIntro() {
      return new ProofAxiom_ForallIntro();
    }
    public bool is_AndIntro { get { return this is ProofAxiom_AndIntro; } }
    public bool is_AndElimLeft { get { return this is ProofAxiom_AndElimLeft; } }
    public bool is_AndElimRight { get { return this is ProofAxiom_AndElimRight; } }
    public bool is_ImpElim { get { return this is ProofAxiom_ImpElim; } }
    public bool is_ImpIntro { get { return this is ProofAxiom_ImpIntro; } }
    public bool is_ForallElim { get { return this is ProofAxiom_ForallElim; } }
    public bool is_ForallIntro { get { return this is ProofAxiom_ForallIntro; } }
    public static System.Collections.Generic.IEnumerable<_IProofAxiom> AllSingletonConstructors {
      get {
        yield return ProofAxiom.create_AndIntro();
        yield return ProofAxiom.create_AndElimLeft();
        yield return ProofAxiom.create_AndElimRight();
        yield return ProofAxiom.create_ImpElim();
        yield return ProofAxiom.create_ImpIntro();
        yield return ProofAxiom.create_ForallElim();
        yield return ProofAxiom.create_ForallIntro();
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
      Alcor._IProofAxiom _source5 = this;
      if (_source5.is_AndIntro) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndIntro");
      } else if (_source5.is_AndElimLeft) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndElimLeft");
      } else if (_source5.is_AndElimRight) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndElimRight");
      } else if (_source5.is_ImpElim) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ImpElim");
      } else if (_source5.is_ImpIntro) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ImpIntro");
      } else if (_source5.is_ForallElim) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ForallElim");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ForallIntro");
      }
    }
    public BigInteger Arity() {
      Alcor._IProofAxiom _source6 = this;
      if (_source6.is_AndIntro) {
        return new BigInteger(2);
      } else if (_source6.is_AndElimLeft) {
        return BigInteger.One;
      } else if (_source6.is_AndElimRight) {
        return BigInteger.One;
      } else if (_source6.is_ImpElim) {
        return new BigInteger(2);
      } else if (_source6.is_ImpIntro) {
        return new BigInteger(2);
      } else if (_source6.is_ForallElim) {
        return new BigInteger(2);
      } else {
        return new BigInteger(2);
      }
    }
    public Wrappers._IResult<AlcorProofKernel._IExpr> ExtractProof(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i) {
      Alcor._IProofValue _143_arg = (args).Select(i);
      if ((_143_arg).is_OneProof) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_143_arg).dtor_proof);
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("At index "), Wrappers.__default.IntToString(i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), (this)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", expected proof, but got ")), (_143_arg).Summary()));
      }
    }
    public Wrappers._IResult<AlcorProofKernel._IExpr> ExtractExpr(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i) {
      Alcor._IProofValue _144_arg = (args).Select(i);
      if ((_144_arg).is_OneExpr) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_144_arg).dtor_expr);
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("At index "), Wrappers.__default.IntToString(i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), (this)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", expected expr, but got ")), (_144_arg).Summary()));
      }
    }
    public Wrappers._IResult<Alcor._IProofValue> ApplyArgs(Dafny.ISequence<Alcor._IProofValue> args, Alcor._IProofEnv environment) {
      Alcor._IProofAxiom _source7 = this;
      if (_source7.is_AndIntro) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _145_valueOrError0 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_145_valueOrError0).IsFailure()) {
          return (_145_valueOrError0).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _146_left = (_145_valueOrError0).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _147_valueOrError1 = (this).ExtractProof(args, BigInteger.One);
          if ((_147_valueOrError1).IsFailure()) {
            return (_147_valueOrError1).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _148_right = (_147_valueOrError1).Extract();
            return (AlcorProofKernel.Proof.AndIntro(_146_left, _148_right)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_149_p) => {
              return Alcor.ProofValue.create_OneProof(_149_p);
            })));
          }
        }
      } else if (_source7.is_AndElimLeft) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _150_valueOrError2 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_150_valueOrError2).IsFailure()) {
          return (_150_valueOrError2).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _151_elem = (_150_valueOrError2).Extract();
          return (AlcorProofKernel.Proof.AndElimLeft(_151_elem)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_152_p) => {
            return Alcor.ProofValue.create_OneProof(_152_p);
          })));
        }
      } else if (_source7.is_AndElimRight) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _153_valueOrError3 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_153_valueOrError3).IsFailure()) {
          return (_153_valueOrError3).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _154_elem = (_153_valueOrError3).Extract();
          return (AlcorProofKernel.Proof.AndElimRight(_154_elem)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_155_p) => {
            return Alcor.ProofValue.create_OneProof(_155_p);
          })));
        }
      } else if (_source7.is_ImpElim) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _156_valueOrError6 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_156_valueOrError6).IsFailure()) {
          return (_156_valueOrError6).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _157_left = (_156_valueOrError6).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _158_valueOrError7 = (this).ExtractProof(args, BigInteger.One);
          if ((_158_valueOrError7).IsFailure()) {
            return (_158_valueOrError7).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _159_right = (_158_valueOrError7).Extract();
            return (AlcorProofKernel.Proof.ImpElim(_157_left, _159_right)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_160_p) => {
              return Alcor.ProofValue.create_OneProof(_160_p);
            })));
          }
        }
      } else if (_source7.is_ImpIntro) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _161_valueOrError4 = (this).ExtractExpr(args, BigInteger.Zero);
        if ((_161_valueOrError4).IsFailure()) {
          return (_161_valueOrError4).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _162_hypothesis = (_161_valueOrError4).Extract();
          Alcor._IProofValue _163_reasoning = (args).Select(BigInteger.One);
          if (!((_163_reasoning).is_OneClosure)) {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Second argument of ImpIntro requires a closure, got "), (_163_reasoning).Summary()));
          } else {
            Dafny.ISequence<Dafny.Rune> _164_argName = (_163_reasoning).dtor_argName;
            Alcor._IProofProgram _165_body = (_163_reasoning).dtor_body;
            Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>> _166_proofBuilder = Dafny.Helpers.Id<Func<Alcor._IProofProgram, Dafny.ISequence<Dafny.Rune>, Alcor._IProofEnv, Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>>>((_167_body, _168_argName, _169_environment) => ((System.Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>)((_170_p) => {
              return Dafny.Helpers.Let<Wrappers._IResult<Alcor._IProofValue>, Wrappers._IResult<AlcorProofKernel._IExpr>>(Alcor.__default.ExecuteProof(_167_body, Alcor.ProofEnv.create_ProofEnvCons(_168_argName, Alcor.ProofValue.create_OneProof(_170_p), _169_environment)), _pat_let0_0 => Dafny.Helpers.Let<Wrappers._IResult<Alcor._IProofValue>, Wrappers._IResult<AlcorProofKernel._IExpr>>(_pat_let0_0, _171_valueOrError5 => (((_171_valueOrError5).IsFailure()) ? ((_171_valueOrError5).PropagateFailure<AlcorProofKernel._IExpr>()) : (Dafny.Helpers.Let<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>((_171_valueOrError5).Extract(), _pat_let1_0 => Dafny.Helpers.Let<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>(_pat_let1_0, _172_x => (((_172_x).is_OneProof) ? (Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_172_x).dtor_proof)) : (Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Closure should return a proof, but got "), (_172_x).Summary()))))))))));
            })))(_165_body, _164_argName, environment);
            return (AlcorProofKernel.Proof.ImpIntro(_162_hypothesis, AlcorProofKernel.Expr.create_True(), _166_proofBuilder)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_173_p) => {
              return Alcor.ProofValue.create_OneProof(_173_p);
            })));
          }
        }
      } else if (_source7.is_ForallElim) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _174_valueOrError10 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_174_valueOrError10).IsFailure()) {
          return (_174_valueOrError10).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _175_axiom = (_174_valueOrError10).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _176_valueOrError11 = (this).ExtractExpr(args, BigInteger.One);
          if ((_176_valueOrError11).IsFailure()) {
            return (_176_valueOrError11).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _177_instance = (_176_valueOrError11).Extract();
            return (AlcorProofKernel.Proof.ForallElim(_175_axiom, _177_instance)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_178_p) => {
              return Alcor.ProofValue.create_OneProof(_178_p);
            })));
          }
        }
      } else {
        Wrappers._IResult<AlcorProofKernel._IExpr> _179_valueOrError8 = (this).ExtractExpr(args, BigInteger.Zero);
        if ((_179_valueOrError8).IsFailure()) {
          return (_179_valueOrError8).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _180_v = (_179_valueOrError8).Extract();
          if (!((_180_v).is_Var)) {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ForallIntro needs a var as first argument, but got "), (_180_v)._ToString()));
          } else {
            Wrappers._IResult<AlcorProofKernel._IExpr> _181_valueOrError9 = (this).ExtractProof(args, BigInteger.One);
            if ((_181_valueOrError9).IsFailure()) {
              return (_181_valueOrError9).PropagateFailure<Alcor._IProofValue>();
            } else {
              AlcorProofKernel._IExpr _182_body = (_181_valueOrError9).Extract();
              return (AlcorProofKernel.Proof.ForallIntro(_182_body, (_180_v).dtor_id)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_183_p) => {
                return Alcor.ProofValue.create_OneProof(_183_p);
              })));
            }
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
  public class ProofAxiom_ForallElim : ProofAxiom {
    public ProofAxiom_ForallElim() : base() {
    }
    public override _IProofAxiom DowncastClone() {
      if (this is _IProofAxiom dt) { return dt; }
      return new ProofAxiom_ForallElim();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofAxiom_ForallElim;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofAxiom.ForallElim";
      return s;
    }
  }
  public class ProofAxiom_ForallIntro : ProofAxiom {
    public ProofAxiom_ForallIntro() : base() {
    }
    public override _IProofAxiom DowncastClone() {
      if (this is _IProofAxiom dt) { return dt; }
      return new ProofAxiom_ForallIntro();
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.ProofAxiom_ForallIntro;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int)hash;
    }
    public override string ToString() {
      string s = "Alcor.ProofAxiom.ForallIntro";
      return s;
    }
  }

  public interface _IType {
    bool is_Ind { get; }
    bool is_Bool { get; }
    bool is_Arrow { get; }
    Alcor._IType dtor_left { get; }
    Alcor._IType dtor_right { get; }
    _IType DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString();
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
    public static _IType create_Arrow(Alcor._IType left, Alcor._IType right) {
      return new Type_Arrow(left, right);
    }
    public bool is_Ind { get { return this is Type_Ind; } }
    public bool is_Bool { get { return this is Type_Bool; } }
    public bool is_Arrow { get { return this is Type_Arrow; } }
    public Alcor._IType dtor_left {
      get {
        var d = this;
        return ((Type_Arrow)d)._left;
      }
    }
    public Alcor._IType dtor_right {
      get {
        var d = this;
        return ((Type_Arrow)d)._right;
      }
    }
    public abstract _IType DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      if ((this).is_Ind) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ind");
      } else if ((this).is_Bool) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Bool");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((((this).dtor_left).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), ((this).dtor_left)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))) : (((this).dtor_left)._ToString())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("->")), ((this).dtor_right)._ToString());
      }
    }
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
    public readonly Alcor._IType _left;
    public readonly Alcor._IType _right;
    public Type_Arrow(Alcor._IType left, Alcor._IType right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Arrow(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as Alcor.Type_Arrow;
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
      string s = "Alcor.Type.Arrow";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
} // end of namespace Alcor
namespace EnsureNoRemoval {

  public partial class __default {
    public static void DebugTest() {
      BigInteger _184___v0;
      _184___v0 = Alcor.__default.Debug(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hello"));
    }
  }
} // end of namespace EnsureNoRemoval
namespace AlcorTacticProofChecker {

  public partial class __default {
    public static bool IsProof(AlcorProofKernel._IExpr p) {
      return true;
    }
  }

  public interface _IEnv {
    bool is_EnvNil { get; }
    bool is_EnvCons { get; }
    Dafny.ISequence<Dafny.Rune> dtor_id { get; }
    AlcorProofKernel._IExpr dtor_prop { get; }
    AlcorTacticProofChecker._IEnv dtor_tail { get; }
    _IEnv DowncastClone();
    AlcorProofKernel._IExpr ToExpr();
    bool IsEmpty();
    _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> ElemAt(BigInteger index);
    BigInteger IndexOf(Dafny.ISequence<Dafny.Rune> name);
    AlcorTacticProofChecker._IEnv Drop(BigInteger i);
    AlcorTacticProofChecker._IEnv ReplaceTailAt(BigInteger i, Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv> newTail);
    Dafny.ISequence<Dafny.Rune> _ToString();
    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> FreeVars();
    Dafny.ISequence<Dafny.Rune> FreshVar(Dafny.ISequence<Dafny.Rune> name);
    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> FreshVar__helper2(Dafny.ISequence<Dafny.Rune> name, BigInteger num);
    Dafny.ISequence<Dafny.Rune> FreshVar__helper(Dafny.ISequence<Dafny.Rune> name, BigInteger num, Dafny.ISet<Dafny.ISequence<Dafny.Rune>> freeVars);
    Dafny.ISet<AlcorProofKernel._IIdentifier> FreeIdentifiers();
    AlcorTacticProofChecker._IEnv Rename(Dafny.ISequence<Dafny.Rune> oldName, Dafny.ISequence<Dafny.Rune> newName);
  }
  public abstract class Env : _IEnv {
    public Env() {
    }
    private static readonly AlcorTacticProofChecker._IEnv theDefault = create_EnvNil();
    public static AlcorTacticProofChecker._IEnv Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorTacticProofChecker._IEnv> _TYPE = new Dafny.TypeDescriptor<AlcorTacticProofChecker._IEnv>(AlcorTacticProofChecker.Env.Default());
    public static Dafny.TypeDescriptor<AlcorTacticProofChecker._IEnv> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnv create_EnvNil() {
      return new Env_EnvNil();
    }
    public static _IEnv create_EnvCons(Dafny.ISequence<Dafny.Rune> id, AlcorProofKernel._IExpr prop, AlcorTacticProofChecker._IEnv tail) {
      return new Env_EnvCons(id, prop, tail);
    }
    public bool is_EnvNil { get { return this is Env_EnvNil; } }
    public bool is_EnvCons { get { return this is Env_EnvCons; } }
    public Dafny.ISequence<Dafny.Rune> dtor_id {
      get {
        var d = this;
        return ((Env_EnvCons)d)._id;
      }
    }
    public AlcorProofKernel._IExpr dtor_prop {
      get {
        var d = this;
        return ((Env_EnvCons)d)._prop;
      }
    }
    public AlcorTacticProofChecker._IEnv dtor_tail {
      get {
        var d = this;
        return ((Env_EnvCons)d)._tail;
      }
    }
    public abstract _IEnv DowncastClone();
    public AlcorProofKernel._IExpr ToExpr() {
      if ((this).is_EnvNil) {
        return AlcorProofKernel.Expr.create_True();
      } else {
        return AlcorProofKernel.Expr.create_And((this).dtor_prop, ((this).dtor_tail).ToExpr());
      }
    }
    public bool IsEmpty() {
      return (this).is_EnvNil;
    }
    public _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> ElemAt(BigInteger index) {
      _IEnv _this = this;
    TAIL_CALL_START:;
      if ((index).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr>.create((_this).dtor_id, (_this).dtor_prop);
      } else {
        var _in4 = (_this).dtor_tail;
        BigInteger _in5 = (index) - (BigInteger.One);
        _this = _in4;
        index = _in5;
        goto TAIL_CALL_START;
      }
    }
    public BigInteger IndexOf(Dafny.ISequence<Dafny.Rune> name) {
      if ((this).is_EnvNil) {
        return new BigInteger(-1);
      } else if (((this).dtor_id).Equals(name)) {
        return BigInteger.Zero;
      } else {
        BigInteger _185_tailIndex = ((this).dtor_tail).IndexOf(name);
        if ((_185_tailIndex) == (new BigInteger(-1))) {
          return new BigInteger(-1);
        } else {
          return (BigInteger.One) + (_185_tailIndex);
        }
      }
    }
    public AlcorTacticProofChecker._IEnv Drop(BigInteger i) {
      _IEnv _this = this;
    TAIL_CALL_START:;
      if ((i).Sign == 0) {
        return _this;
      } else {
        var _in6 = (_this).dtor_tail;
        BigInteger _in7 = (i) - (BigInteger.One);
        _this = _in6;
        i = _in7;
        goto TAIL_CALL_START;
      }
    }
    public AlcorTacticProofChecker._IEnv ReplaceTailAt(BigInteger i, Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv> newTail) {
      if ((i).Sign == 0) {
        return Dafny.Helpers.Id<Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>>(newTail)(this);
      } else {
        return AlcorTacticProofChecker.Env.create_EnvCons((this).dtor_id, (this).dtor_prop, ((this).dtor_tail).ReplaceTailAt((i) - (BigInteger.One), newTail));
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      if ((this).is_EnvNil) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        Dafny.ISequence<Dafny.Rune> _186_x = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_prop)._ToString());
        if (!(((this).dtor_tail).is_EnvNil)) {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_tail)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _186_x);
        } else {
          return _186_x;
        }
      }
    }
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> FreeVars() {
      if ((this).is_EnvNil) {
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      } else {
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _187_tailFreeVars = ((this).dtor_tail).FreeVars();
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((this).dtor_id), _187_tailFreeVars);
      }
    }
    public Dafny.ISequence<Dafny.Rune> FreshVar(Dafny.ISequence<Dafny.Rune> name) {
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _188_freeVars = (this).FreeVars();
      if (!(_188_freeVars).Contains(name)) {
        return name;
      } else {
        return (this).FreshVar__helper(name, BigInteger.Zero, _188_freeVars);
      }
    }
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> FreshVar__helper2(Dafny.ISequence<Dafny.Rune> name, BigInteger num) {
      return Dafny.Helpers.Id<Func<BigInteger, Dafny.ISequence<Dafny.Rune>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_189_num, _190_name) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
        foreach (BigInteger _compr_0 in Dafny.Helpers.IntegerRange(BigInteger.Zero, _189_num)) {
          BigInteger _191_i = (BigInteger)_compr_0;
          if (((_191_i).Sign != -1) && ((_191_i) < (_189_num))) {
            _coll0.Add(Dafny.Sequence<Dafny.Rune>.Concat(_190_name, Wrappers.__default.IntToString(_191_i)));
          }
        }
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll0);
      }))())(num, name);
    }
    public Dafny.ISequence<Dafny.Rune> FreshVar__helper(Dafny.ISequence<Dafny.Rune> name, BigInteger num, Dafny.ISet<Dafny.ISequence<Dafny.Rune>> freeVars) {
      _IEnv _this = this;
    TAIL_CALL_START:;
      Dafny.ISequence<Dafny.Rune> _192_candidate = Dafny.Sequence<Dafny.Rune>.Concat(name, Wrappers.__default.IntToString(num));
      if (!(freeVars).Contains(_192_candidate)) {
        return _192_candidate;
      } else {
        var _in8 = _this;
        Dafny.ISequence<Dafny.Rune> _in9 = name;
        BigInteger _in10 = (num) + (BigInteger.One);
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _in11 = freeVars;
        _this = _in8;
        name = _in9;
        num = _in10;
        freeVars = _in11;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISet<AlcorProofKernel._IIdentifier> FreeIdentifiers() {
      Dafny.ISet<AlcorProofKernel._IIdentifier> _193___accumulator = Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements();
      _IEnv _this = this;
    TAIL_CALL_START:;
      if ((_this).is_EnvNil) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.Union(Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements(), _193___accumulator);
      } else {
        Dafny.ISet<AlcorProofKernel._IIdentifier> _194_headIds = ((_this).dtor_prop).FreeVars();
        _193___accumulator = Dafny.Set<AlcorProofKernel._IIdentifier>.Union(_193___accumulator, _194_headIds);
        var _in12 = (_this).dtor_tail;
        _this = _in12;
        goto TAIL_CALL_START;
      }
    }
    public AlcorTacticProofChecker._IEnv Rename(Dafny.ISequence<Dafny.Rune> oldName, Dafny.ISequence<Dafny.Rune> newName) {
      if ((this).is_EnvNil) {
        return this;
      } else if (((this).dtor_id).Equals(oldName)) {
        return AlcorTacticProofChecker.Env.create_EnvCons(newName, (this).dtor_prop, (this).dtor_tail);
      } else {
        return AlcorTacticProofChecker.Env.create_EnvCons((this).dtor_id, (this).dtor_prop, ((this).dtor_tail).Rename(oldName, newName));
      }
    }
  }
  public class Env_EnvNil : Env {
    public Env_EnvNil() : base() {
    }
    public override _IEnv DowncastClone() {
      if (this is _IEnv dt) { return dt; }
      return new Env_EnvNil();
    }
    public override bool Equals(object other) {
      var oth = other as AlcorTacticProofChecker.Env_EnvNil;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorTacticProofChecker.Env.EnvNil";
      return s;
    }
  }
  public class Env_EnvCons : Env {
    public readonly Dafny.ISequence<Dafny.Rune> _id;
    public readonly AlcorProofKernel._IExpr _prop;
    public readonly AlcorTacticProofChecker._IEnv _tail;
    public Env_EnvCons(Dafny.ISequence<Dafny.Rune> id, AlcorProofKernel._IExpr prop, AlcorTacticProofChecker._IEnv tail) : base() {
      this._id = id;
      this._prop = prop;
      this._tail = tail;
    }
    public override _IEnv DowncastClone() {
      if (this is _IEnv dt) { return dt; }
      return new Env_EnvCons(_id, _prop, _tail);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorTacticProofChecker.Env_EnvCons;
      return oth != null && object.Equals(this._id, oth._id) && object.Equals(this._prop, oth._prop) && object.Equals(this._tail, oth._tail);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._prop));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tail));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorTacticProofChecker.Env.EnvCons";
      s += "(";
      s += this._id.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._prop);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tail);
      s += ")";
      return s;
    }
  }

  public interface _ISequent {
    bool is_Sequent { get; }
    AlcorTacticProofChecker._IEnv dtor_env { get; }
    AlcorProofKernel._IExpr dtor_goal { get; }
    _ISequent DowncastClone();
    AlcorProofKernel._IExpr ToExpr(BigInteger envIndex);
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public class Sequent : _ISequent {
    public readonly AlcorTacticProofChecker._IEnv _env;
    public readonly AlcorProofKernel._IExpr _goal;
    public Sequent(AlcorTacticProofChecker._IEnv env, AlcorProofKernel._IExpr goal) {
      this._env = env;
      this._goal = goal;
    }
    public _ISequent DowncastClone() {
      if (this is _ISequent dt) { return dt; }
      return new Sequent(_env, _goal);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorTacticProofChecker.Sequent;
      return oth != null && object.Equals(this._env, oth._env) && object.Equals(this._goal, oth._goal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._env));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._goal));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorTacticProofChecker.Sequent.Sequent";
      s += "(";
      s += Dafny.Helpers.ToString(this._env);
      s += ", ";
      s += Dafny.Helpers.ToString(this._goal);
      s += ")";
      return s;
    }
    private static readonly AlcorTacticProofChecker._ISequent theDefault = create(AlcorTacticProofChecker.Env.Default(), AlcorProofKernel.Expr.Default());
    public static AlcorTacticProofChecker._ISequent Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorTacticProofChecker._ISequent> _TYPE = new Dafny.TypeDescriptor<AlcorTacticProofChecker._ISequent>(AlcorTacticProofChecker.Sequent.Default());
    public static Dafny.TypeDescriptor<AlcorTacticProofChecker._ISequent> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISequent create(AlcorTacticProofChecker._IEnv env, AlcorProofKernel._IExpr goal) {
      return new Sequent(env, goal);
    }
    public static _ISequent create_Sequent(AlcorTacticProofChecker._IEnv env, AlcorProofKernel._IExpr goal) {
      return create(env, goal);
    }
    public bool is_Sequent { get { return true; } }
    public AlcorTacticProofChecker._IEnv dtor_env {
      get {
        return this._env;
      }
    }
    public AlcorProofKernel._IExpr dtor_goal {
      get {
        return this._goal;
      }
    }
    public AlcorProofKernel._IExpr ToExpr(BigInteger envIndex) {
      return AlcorProofKernel.Expr.create_Imp(((this).dtor_env).ToExpr(), (this).dtor_goal);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_env)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n|- ")), ((this).dtor_goal)._ToString());
    }
  }

  public interface _ISequentList {
    bool is_SequentNil { get; }
    bool is_SequentCons { get; }
    AlcorTacticProofChecker._ISequent dtor_head { get; }
    AlcorTacticProofChecker._ISequentList dtor_tail { get; }
    _ISequentList DowncastClone();
    bool IsEmpty();
    AlcorTacticProofChecker._ISequent ElemAt(BigInteger index);
    AlcorProofKernel._IExpr ToExpr();
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public abstract class SequentList : _ISequentList {
    public SequentList() {
    }
    private static readonly AlcorTacticProofChecker._ISequentList theDefault = create_SequentNil();
    public static AlcorTacticProofChecker._ISequentList Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorTacticProofChecker._ISequentList> _TYPE = new Dafny.TypeDescriptor<AlcorTacticProofChecker._ISequentList>(AlcorTacticProofChecker.SequentList.Default());
    public static Dafny.TypeDescriptor<AlcorTacticProofChecker._ISequentList> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISequentList create_SequentNil() {
      return new SequentList_SequentNil();
    }
    public static _ISequentList create_SequentCons(AlcorTacticProofChecker._ISequent head, AlcorTacticProofChecker._ISequentList tail) {
      return new SequentList_SequentCons(head, tail);
    }
    public bool is_SequentNil { get { return this is SequentList_SequentNil; } }
    public bool is_SequentCons { get { return this is SequentList_SequentCons; } }
    public AlcorTacticProofChecker._ISequent dtor_head {
      get {
        var d = this;
        return ((SequentList_SequentCons)d)._head;
      }
    }
    public AlcorTacticProofChecker._ISequentList dtor_tail {
      get {
        var d = this;
        return ((SequentList_SequentCons)d)._tail;
      }
    }
    public abstract _ISequentList DowncastClone();
    public bool IsEmpty() {
      return (this).is_SequentNil;
    }
    public AlcorTacticProofChecker._ISequent ElemAt(BigInteger index) {
      _ISequentList _this = this;
    TAIL_CALL_START:;
      if ((index).Sign == 0) {
        return (_this).dtor_head;
      } else {
        var _in13 = (_this).dtor_tail;
        BigInteger _in14 = (index) - (BigInteger.One);
        _this = _in13;
        index = _in14;
        goto TAIL_CALL_START;
      }
    }
    public AlcorProofKernel._IExpr ToExpr() {
      if ((this).is_SequentNil) {
        return AlcorProofKernel.Expr.create_True();
      } else {
        return AlcorProofKernel.Expr.create_And(((this).dtor_head).ToExpr(BigInteger.Zero), ((this).dtor_tail).ToExpr());
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      Dafny.ISequence<Dafny.Rune> _195___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
      _ISequentList _this = this;
    TAIL_CALL_START:;
      if ((_this).is_SequentNil) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_195___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else {
        _195___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_195___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(((_this).dtor_head)._ToString(), ((((_this).dtor_tail).is_SequentNil) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n\n")))));
        var _in15 = (_this).dtor_tail;
        _this = _in15;
        goto TAIL_CALL_START;
      }
    }
  }
  public class SequentList_SequentNil : SequentList {
    public SequentList_SequentNil() : base() {
    }
    public override _ISequentList DowncastClone() {
      if (this is _ISequentList dt) { return dt; }
      return new SequentList_SequentNil();
    }
    public override bool Equals(object other) {
      var oth = other as AlcorTacticProofChecker.SequentList_SequentNil;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorTacticProofChecker.SequentList.SequentNil";
      return s;
    }
  }
  public class SequentList_SequentCons : SequentList {
    public readonly AlcorTacticProofChecker._ISequent _head;
    public readonly AlcorTacticProofChecker._ISequentList _tail;
    public SequentList_SequentCons(AlcorTacticProofChecker._ISequent head, AlcorTacticProofChecker._ISequentList tail) : base() {
      this._head = head;
      this._tail = tail;
    }
    public override _ISequentList DowncastClone() {
      if (this is _ISequentList dt) { return dt; }
      return new SequentList_SequentCons(_head, _tail);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorTacticProofChecker.SequentList_SequentCons;
      return oth != null && object.Equals(this._head, oth._head) && object.Equals(this._tail, oth._tail);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._head));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tail));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorTacticProofChecker.SequentList.SequentCons";
      s += "(";
      s += Dafny.Helpers.ToString(this._head);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tail);
      s += ")";
      return s;
    }
  }

  public interface _IProofState {
    bool is_Sequents { get; }
    bool is_Error { get; }
    AlcorTacticProofChecker._ISequentList dtor_sequents { get; }
    Dafny.ISequence<Dafny.Rune> dtor_message { get; }
    _IProofState DowncastClone();
    AlcorProofKernel._IExpr ToExpr();
    Dafny.ISequence<Dafny.Rune> _ToString();
    AlcorTacticProofChecker._IProofState ToError(Dafny.ISequence<Dafny.Rune> msg);
  }
  public abstract class ProofState : _IProofState {
    public ProofState() {
    }
    private static readonly AlcorTacticProofChecker._IProofState theDefault = create_Sequents(AlcorTacticProofChecker.SequentList.Default());
    public static AlcorTacticProofChecker._IProofState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorTacticProofChecker._IProofState> _TYPE = new Dafny.TypeDescriptor<AlcorTacticProofChecker._IProofState>(AlcorTacticProofChecker.ProofState.Default());
    public static Dafny.TypeDescriptor<AlcorTacticProofChecker._IProofState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IProofState create_Sequents(AlcorTacticProofChecker._ISequentList sequents) {
      return new ProofState_Sequents(sequents);
    }
    public static _IProofState create_Error(Dafny.ISequence<Dafny.Rune> message) {
      return new ProofState_Error(message);
    }
    public bool is_Sequents { get { return this is ProofState_Sequents; } }
    public bool is_Error { get { return this is ProofState_Error; } }
    public AlcorTacticProofChecker._ISequentList dtor_sequents {
      get {
        var d = this;
        return ((ProofState_Sequents)d)._sequents;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_message {
      get {
        var d = this;
        return ((ProofState_Error)d)._message;
      }
    }
    public abstract _IProofState DowncastClone();
    public AlcorProofKernel._IExpr ToExpr() {
      if ((this).is_Error) {
        return AlcorProofKernel.Expr.create_False();
      } else {
        return ((this).dtor_sequents).ToExpr();
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      if ((this).is_Error) {
        return (this).dtor_message;
      } else {
        return ((this).dtor_sequents)._ToString();
      }
    }
    public AlcorTacticProofChecker._IProofState ToError(Dafny.ISequence<Dafny.Rune> msg) {
      return AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), (this)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n/!\\")), msg));
    }
  }
  public class ProofState_Sequents : ProofState {
    public readonly AlcorTacticProofChecker._ISequentList _sequents;
    public ProofState_Sequents(AlcorTacticProofChecker._ISequentList sequents) : base() {
      this._sequents = sequents;
    }
    public override _IProofState DowncastClone() {
      if (this is _IProofState dt) { return dt; }
      return new ProofState_Sequents(_sequents);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorTacticProofChecker.ProofState_Sequents;
      return oth != null && object.Equals(this._sequents, oth._sequents);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._sequents));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorTacticProofChecker.ProofState.Sequents";
      s += "(";
      s += Dafny.Helpers.ToString(this._sequents);
      s += ")";
      return s;
    }
  }
  public class ProofState_Error : ProofState {
    public readonly Dafny.ISequence<Dafny.Rune> _message;
    public ProofState_Error(Dafny.ISequence<Dafny.Rune> message) : base() {
      this._message = message;
    }
    public override _IProofState DowncastClone() {
      if (this is _IProofState dt) { return dt; }
      return new ProofState_Error(_message);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorTacticProofChecker.ProofState_Error;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorTacticProofChecker.ProofState.Error";
      s += "(";
      s += this._message.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public partial class TacticMode {
    public TacticMode() {
      this.proofState = AlcorTacticProofChecker.ProofState.Default();
      this.proofBuilder = Alcor.ProofProgram.Default();
      this._env = AlcorTacticProofChecker.Env.Default();
      this._goal = AlcorProofKernel.Expr.Default();
    }
    public AlcorTacticProofChecker._IProofState proofState { get; set; }
    public Alcor._IProofProgram proofBuilder { get; set; }
    public void __ctor(AlcorProofKernel._IExpr goal, AlcorTacticProofChecker._IEnv env) {
      (this)._env = env;
      (this)._goal = goal;
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(env, goal), AlcorTacticProofChecker.SequentList.create_SequentNil()));
      AlcorProofKernel._IExpr _196_overallGoal;
      _196_overallGoal = AlcorProofKernel.Expr.create_And(AlcorProofKernel.Expr.create_Imp((env).ToExpr(), goal), AlcorProofKernel.Expr.create_True());
      (this).proofBuilder = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_196_overallGoal), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("goal"), Alcor.Type.create_Ind(), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("goal"))));
      (this).CheckProof();
    }
    public void CheckProof() {
      AlcorProofKernel._IExpr _197_overallGoal;
      _197_overallGoal = AlcorProofKernel.Expr.create_And(AlcorProofKernel.Expr.create_Imp(((this).env).ToExpr(), (this).goal), AlcorProofKernel.Expr.create_True());
      Wrappers._IResult<Alcor._IProofValue> _198_p;
      _198_p = Alcor.__default.ExecuteProof(this.proofBuilder, Alcor.ProofEnv.create_ProofEnvNil());
      if ((_198_p).is_Failure) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[Internal error] "), (_198_p).dtor_msg));
      } else if (!(((_198_p).dtor_value).is_OneProof)) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[Internal error] Expected a proof, got a "), ((_198_p).dtor_value).Summary()));
      } else if (!object.Equals(AlcorProofKernel.Proof.GetExpr(((_198_p).dtor_value).dtor_proof), AlcorProofKernel.Expr.create_Imp((this.proofState).ToExpr(), _197_overallGoal))) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[Internal error] Expected a proof that the proof state implies the overall goal\n"), (AlcorProofKernel.Expr.create_Imp((this.proofState).ToExpr(), _197_overallGoal))._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a proof of\n")), (AlcorProofKernel.Proof.GetExpr(((_198_p).dtor_value).dtor_proof))._ToString()));
      } else {
      }
    }
    public Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> Finish() {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TODO"));
      return result;
      return result;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> Intro(Dafny.ISequence<Dafny.Rune> name) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _199_sequents;
      _199_sequents = (this.proofState).dtor_sequents;
      if ((_199_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out4;
        _out4 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to introduce, proof state is empty. Consider removing this"));
        feedback = _out4;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _200_sequent;
      _200_sequent = (_199_sequents).dtor_head;
      AlcorProofKernel._IIdentifier _201_id;
      _201_id = AlcorProofKernel.Identifier.create(name, BigInteger.Zero, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((((_200_sequent).dtor_goal).is_Forall) && ((((_200_sequent).dtor_goal).dtor_body).is_Abs)) {
        Dafny.ISet<AlcorProofKernel._IIdentifier> _202_freeEnvVars;
        _202_freeEnvVars = ((_200_sequent).dtor_env).FreeIdentifiers();
        AlcorProofKernel._IIdentifier _203_freeVar;
        _203_freeVar = AlcorProofKernel.__default.FreshIdentifier((((_200_sequent).dtor_goal).dtor_body).dtor_id, _202_freeEnvVars);
        var _pat_let_tv0 = _200_sequent;
        var _pat_let_tv1 = _200_sequent;
        var _pat_let_tv2 = _200_sequent;
        var _pat_let_tv3 = _203_freeVar;
        var _pat_let_tv4 = _203_freeVar;
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_199_sequents, _pat_let2_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let2_0, _204_dt__update__tmp_h0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequent>(_pat_let_tv0, _pat_let4_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequent>(_pat_let4_0, _205_dt__update__tmp_h1 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorTacticProofChecker._ISequent>(((((_pat_let_tv1).dtor_goal).dtor_body).dtor_body).Bind((((_pat_let_tv2).dtor_goal).dtor_body).dtor_id, AlcorProofKernel.Expr.create_Var(_pat_let_tv3), (AlcorProofKernel.Expr.create_Var(_pat_let_tv4)).FreeVars()), _pat_let5_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorTacticProofChecker._ISequent>(_pat_let5_0, _206_dt__update_hgoal_h0 => AlcorTacticProofChecker.Sequent.create((_205_dt__update__tmp_h1).dtor_env, _206_dt__update_hgoal_h0))))), _pat_let3_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(_pat_let3_0, _207_dt__update_hhead_h0 => AlcorTacticProofChecker.SequentList.create_SequentCons(_207_dt__update_hhead_h0, (_204_dt__update__tmp_h0).dtor_tail))))));
      } else if (((_200_sequent).dtor_goal).is_Imp) {
        var _pat_let_tv5 = name;
        var _pat_let_tv6 = _200_sequent;
        var _pat_let_tv7 = _200_sequent;
        var _pat_let_tv8 = _200_sequent;
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_199_sequents, _pat_let6_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let6_0, _208_dt__update__tmp_h2 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(AlcorTacticProofChecker.Sequent.create(AlcorTacticProofChecker.Env.create_EnvCons(_pat_let_tv5, ((_pat_let_tv6).dtor_goal).dtor_left, (_pat_let_tv7).dtor_env), ((_pat_let_tv8).dtor_goal).dtor_right), _pat_let7_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(_pat_let7_0, _209_dt__update_hhead_h1 => AlcorTacticProofChecker.SequentList.create_SequentCons(_209_dt__update_hhead_h1, (_208_dt__update__tmp_h2).dtor_tail))))));
      } else {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not apply intro rule"));
      }
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
      } else {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
      }
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> Rename(Dafny.ISequence<Dafny.Rune> previousName, Dafny.ISequence<Dafny.Rune> suggestedName) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      Dafny.ISequence<Dafny.Rune> _210_oldName;
      _210_oldName = previousName;
      Dafny.ISequence<Dafny.Rune> _211_newName;
      _211_newName = suggestedName;
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _212_sequents;
      _212_sequents = (this.proofState).dtor_sequents;
      if ((_212_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out5;
        _out5 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to rename, proof state is empty. Consider removing this"));
        feedback = _out5;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _213_sequent;
      _213_sequent = (_212_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _214_env;
      _214_env = (_213_sequent).dtor_env;
      if ((_214_env).is_EnvNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out6;
        _out6 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to rename, proof state has no environment. Consider removing this"));
        feedback = _out6;
        return feedback;
      }
      if ((_211_newName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        _211_newName = _210_oldName;
        _210_oldName = (_214_env).dtor_id;
      }
      if (!((_214_env).FreeVars()).Contains(_210_oldName)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out7;
        _out7 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("No variable in the environment is named "), _210_oldName));
        feedback = _out7;
        return feedback;
      }
      AlcorTacticProofChecker._IEnv _215_newEnv;
      _215_newEnv = (_214_env).Rename(_210_oldName, _211_newName);
      var _pat_let_tv9 = _212_sequents;
      var _pat_let_tv10 = _215_newEnv;
      var _pat_let_tv11 = _213_sequent;
      (this).proofState = Dafny.Helpers.Let<AlcorTacticProofChecker._IProofState, AlcorTacticProofChecker._IProofState>(this.proofState, _pat_let8_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._IProofState, AlcorTacticProofChecker._IProofState>(_pat_let8_0, _216_dt__update__tmp_h0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._IProofState>(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let_tv9, _pat_let10_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let10_0, _217_dt__update__tmp_h1 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(AlcorTacticProofChecker.Sequent.create(_pat_let_tv10, (_pat_let_tv11).dtor_goal), _pat_let11_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(_pat_let11_0, _218_dt__update_hhead_h0 => AlcorTacticProofChecker.SequentList.create_SequentCons(_218_dt__update_hhead_h0, (_217_dt__update__tmp_h1).dtor_tail))))), _pat_let9_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._IProofState>(_pat_let9_0, _219_dt__update_hsequents_h0 => AlcorTacticProofChecker.ProofState.create_Sequents(_219_dt__update_hsequents_h0)))));
      feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
      return feedback;
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> Cases() {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _220_sequents;
      _220_sequents = (this.proofState).dtor_sequents;
      if ((_220_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out8;
        _out8 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a case split on"));
        feedback = _out8;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _221_sequent;
      _221_sequent = (_220_sequents).dtor_head;
      if (!(((_221_sequent).dtor_goal).is_And)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out9;
        _out9 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot perform a case split on something other than &&"));
        feedback = _out9;
        return feedback;
      }
      AlcorTacticProofChecker._IEnv _222_env;
      _222_env = (_221_sequent).dtor_env;
      AlcorTacticProofChecker._ISequentList _223_newSequents;
      _223_newSequents = AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_222_env, ((_221_sequent).dtor_goal).dtor_left), AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_222_env, AlcorProofKernel.Expr.create_Imp(((_221_sequent).dtor_goal).dtor_left, ((_221_sequent).dtor_goal).dtor_right)), (_220_sequents).dtor_tail));
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(_223_newSequents);
      feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
      return feedback;
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> CasesEnv(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> left, Dafny.ISequence<Dafny.Rune> right) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _224_sequents;
      _224_sequents = (this.proofState).dtor_sequents;
      if ((_224_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out10;
        _out10 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a case split on"));
        feedback = _out10;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _225_sequent;
      _225_sequent = (_224_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _226_env;
      _226_env = (_225_sequent).dtor_env;
      BigInteger _227_i;
      _227_i = (_226_env).IndexOf(name);
      if ((_227_i).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out11;
        _out11 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out11;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs0 = (_226_env).ElemAt(_227_i);
      Dafny.ISequence<Dafny.Rune> _228_envIdentifier = _let_tmp_rhs0.dtor__0;
      AlcorProofKernel._IExpr _229_envElem = _let_tmp_rhs0.dtor__1;
      if (!((_229_envElem).is_And)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out12;
        _out12 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not splittable")));
        feedback = _out12;
        return feedback;
      }
      AlcorTacticProofChecker._IEnv _230_newEnv;
      _230_newEnv = (_226_env).ReplaceTailAt(_227_i, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, AlcorTacticProofChecker._IEnv, BigInteger, Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>>>((_231_right, _232_left, _233_env, _234_i) => ((System.Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>)((_235_previousEnv) => {
        return AlcorTacticProofChecker.Env.create_EnvCons(_231_right, ((_235_previousEnv).dtor_prop).dtor_right, AlcorTacticProofChecker.Env.create_EnvCons(_232_left, ((_235_previousEnv).dtor_prop).dtor_left, (_235_previousEnv).dtor_tail));
      })))(right, left, _226_env, _227_i));
      AlcorTacticProofChecker._ISequentList _236_newSequents;
      _236_newSequents = AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_230_newEnv, (_225_sequent).dtor_goal), (_224_sequents).dtor_tail);
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(_236_newSequents);
      feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
      return feedback;
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> SetFailure(Dafny.ISequence<Dafny.Rune> msg) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(msg);
      feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure(msg);
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> ImpElim(Dafny.ISequence<Dafny.Rune> imp, Dafny.ISequence<Dafny.Rune> hypothesis, Dafny.ISequence<Dafny.Rune> newName) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _237_sequents;
      _237_sequents = (this.proofState).dtor_sequents;
      if ((_237_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out13;
        _out13 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a ImpElim on"));
        feedback = _out13;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _238_sequent;
      _238_sequent = (_237_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _239_env;
      _239_env = (_238_sequent).dtor_env;
      AlcorProofKernel._IExpr _240_goal;
      _240_goal = (_238_sequent).dtor_goal;
      BigInteger _241_iImp;
      _241_iImp = (_239_env).IndexOf(imp);
      if ((_241_iImp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out14;
        _out14 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), imp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out14;
        return feedback;
      }
      BigInteger _242_iHyp;
      _242_iHyp = (_239_env).IndexOf(hypothesis);
      if ((_242_iHyp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out15;
        _out15 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), hypothesis), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out15;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs1 = (_239_env).ElemAt(_241_iImp);
      Dafny.ISequence<Dafny.Rune> _243___v0 = _let_tmp_rhs1.dtor__0;
      AlcorProofKernel._IExpr _244_impExpr = _let_tmp_rhs1.dtor__1;
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs2 = (_239_env).ElemAt(_242_iHyp);
      Dafny.ISequence<Dafny.Rune> _245___v1 = _let_tmp_rhs2.dtor__0;
      AlcorProofKernel._IExpr _246_hypExpr = _let_tmp_rhs2.dtor__1;
      if (!((_244_impExpr).is_Imp)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out16;
        _out16 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), imp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not an implication")));
        feedback = _out16;
        return feedback;
      }
      if (!object.Equals((_244_impExpr).dtor_left, _246_hypExpr)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out17;
        _out17 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), imp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" cannot be applied to ")), hypothesis));
        feedback = _out17;
        return feedback;
      }
      if (object.Equals((_244_impExpr).dtor_right, _240_goal)) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents((_237_sequents).dtor_tail);
      } else {
        Dafny.ISequence<Dafny.Rune> _247_newName;
        _247_newName = (((newName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("h")) : (newName));
        Dafny.ISequence<Dafny.Rune> _248_freeVar;
        _248_freeVar = ((_238_sequent).dtor_env).FreshVar(_247_newName);
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(AlcorTacticProofChecker.Env.create_EnvCons(_248_freeVar, (_244_impExpr).dtor_right, _239_env), _240_goal), (_237_sequents).dtor_tail));
      }
      feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
      return feedback;
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> UseHypothesis(Dafny.ISequence<Dafny.Rune> name) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _249_sequents;
      _249_sequents = (this.proofState).dtor_sequents;
      if ((_249_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out18;
        _out18 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a ImpElim on"));
        feedback = _out18;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _250_sequent;
      _250_sequent = (_249_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _251_env;
      _251_env = (_250_sequent).dtor_env;
      AlcorProofKernel._IExpr _252_goal;
      _252_goal = (_250_sequent).dtor_goal;
      BigInteger _253_iHyp;
      _253_iHyp = (_251_env).IndexOf(name);
      if ((_253_iHyp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out19;
        _out19 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out19;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs3 = (_251_env).ElemAt(_253_iHyp);
      Dafny.ISequence<Dafny.Rune> _254___v2 = _let_tmp_rhs3.dtor__0;
      AlcorProofKernel._IExpr _255_hypExpr = _let_tmp_rhs3.dtor__1;
      if (object.Equals(_255_hypExpr, _252_goal)) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents((_249_sequents).dtor_tail);
      } else {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out20;
        _out20 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The hypothesis "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not the goal")));
        feedback = _out20;
        return feedback;
      }
      feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
      return feedback;
      return feedback;
    }
    public AlcorTacticProofChecker._IEnv _env { get; set; }
    public AlcorTacticProofChecker._IEnv env {
      get {
        return this._env;
      }
    }
    public AlcorProofKernel._IExpr _goal { get; set; }
    public AlcorProofKernel._IExpr goal {
      get {
        return this._goal;
      }
    }
  }
} // end of namespace AlcorTacticProofChecker

namespace Microsoft.Dafny {

} // end of namespace Microsoft.Dafny
namespace Formatting {

  public partial class __default {
    public static System.String ReindentProgramFromFirstToken(Microsoft.Dafny.IToken firstToken, Formatting.IIndentationFormatter reindent) {
      System.String s = default(System.String);
      Microsoft.Dafny.IToken _256_token;
      _256_token = firstToken;
      System.Text.StringBuilder _257_sb;
      System.Text.StringBuilder _nw0 = new System.Text.StringBuilder();
      _257_sb = _nw0;
      while ((_256_token) != (object)((Microsoft.Dafny.IToken)null)) {
        System.String _258_newLeadingTrivia;
        _258_newLeadingTrivia = (reindent).GetNewLeadingTrivia(_256_token);
        System.String _259_newTrailingTrivia;
        _259_newTrailingTrivia = (reindent).GetNewTrailingTrivia(_256_token);
        (_257_sb).Append(_258_newLeadingTrivia);
        (_257_sb).Append(_256_token.val);
        (_257_sb).Append(_259_newTrailingTrivia);
        _256_token = _256_token.Next;
      }
      System.String _out21;
      _out21 = (_257_sb).ToString().ToString();
      s = _out21;
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



