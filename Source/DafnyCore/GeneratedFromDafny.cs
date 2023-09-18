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

  public interface _ISimplificationConfig {
    bool is_SimplificationConfig { get; }
    bool dtor_insideAbs { get; }
    BigInteger dtor_betaDepth { get; }
    _ISimplificationConfig DowncastClone();
  }
  public class SimplificationConfig : _ISimplificationConfig {
    public readonly bool _insideAbs;
    public readonly BigInteger _betaDepth;
    public SimplificationConfig(bool insideAbs, BigInteger betaDepth) {
      this._insideAbs = insideAbs;
      this._betaDepth = betaDepth;
    }
    public _ISimplificationConfig DowncastClone() {
      if (this is _ISimplificationConfig dt) { return dt; }
      return new SimplificationConfig(_insideAbs, _betaDepth);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.SimplificationConfig;
      return oth != null && this._insideAbs == oth._insideAbs && this._betaDepth == oth._betaDepth;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._insideAbs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._betaDepth));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.SimplificationConfig.SimplificationConfig";
      s += "(";
      s += Dafny.Helpers.ToString(this._insideAbs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._betaDepth);
      s += ")";
      return s;
    }
    private static readonly AlcorProofKernel._ISimplificationConfig theDefault = create(false, BigInteger.Zero);
    public static AlcorProofKernel._ISimplificationConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlcorProofKernel._ISimplificationConfig> _TYPE = new Dafny.TypeDescriptor<AlcorProofKernel._ISimplificationConfig>(AlcorProofKernel.SimplificationConfig.Default());
    public static Dafny.TypeDescriptor<AlcorProofKernel._ISimplificationConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISimplificationConfig create(bool insideAbs, BigInteger betaDepth) {
      return new SimplificationConfig(insideAbs, betaDepth);
    }
    public static _ISimplificationConfig create_SimplificationConfig(bool insideAbs, BigInteger betaDepth) {
      return create(insideAbs, betaDepth);
    }
    public bool is_SimplificationConfig { get { return true; } }
    public bool dtor_insideAbs {
      get {
        return this._insideAbs;
      }
    }
    public BigInteger dtor_betaDepth {
      get {
        return this._betaDepth;
      }
    }
  }

  public interface _IExpr {
    bool is_True { get; }
    bool is_False { get; }
    bool is_And { get; }
    bool is_Imp { get; }
    bool is_Or { get; }
    bool is_Var { get; }
    bool is_Abs { get; }
    bool is_App { get; }
    bool is_Forall { get; }
    bool is_Int { get; }
    AlcorProofKernel._IExpr dtor_left { get; }
    AlcorProofKernel._IExpr dtor_right { get; }
    AlcorProofKernel._IIdentifier dtor_id { get; }
    AlcorProofKernel._IExpr dtor_body { get; }
    BigInteger dtor_value { get; }
    _IExpr DowncastClone();
    AlcorProofKernel._IExpr apply(AlcorProofKernel._IExpr expr);
    AlcorProofKernel._IExpr apply2(AlcorProofKernel._IExpr expr1, AlcorProofKernel._IExpr expr2);
    AlcorProofKernel._IExpr simplify(Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr> post, AlcorProofKernel._ISimplificationConfig config);
    Dafny.ISet<AlcorProofKernel._IIdentifier> FreeVars();
    AlcorProofKernel._IExpr Bind(AlcorProofKernel._IIdentifier id, AlcorProofKernel._IExpr expr, Dafny.ISet<AlcorProofKernel._IIdentifier> freeVars);
    Dafny.ISequence<Dafny.Rune> Operator();
    Dafny.ISequence<Dafny.Rune> ToStringWrap(BigInteger outerPriority);
    bool InlineOperator();
    BigInteger LeftPriority();
    BigInteger RightPriority();
    BigInteger Priority();
    bool IfThenElse_q();
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
    public static _IExpr create_Int(BigInteger @value) {
      return new Expr_Int(@value);
    }
    public bool is_True { get { return this is Expr_True; } }
    public bool is_False { get { return this is Expr_False; } }
    public bool is_And { get { return this is Expr_And; } }
    public bool is_Imp { get { return this is Expr_Imp; } }
    public bool is_Or { get { return this is Expr_Or; } }
    public bool is_Var { get { return this is Expr_Var; } }
    public bool is_Abs { get { return this is Expr_Abs; } }
    public bool is_App { get { return this is Expr_App; } }
    public bool is_Forall { get { return this is Expr_Forall; } }
    public bool is_Int { get { return this is Expr_Int; } }
    public AlcorProofKernel._IExpr dtor_left {
      get {
        var d = this;
        if (d is Expr_And) { return ((Expr_And)d)._left; }
        if (d is Expr_Imp) { return ((Expr_Imp)d)._left; }
        if (d is Expr_Or) { return ((Expr_Or)d)._left; }
        return ((Expr_App)d)._left;
      }
    }
    public AlcorProofKernel._IExpr dtor_right {
      get {
        var d = this;
        if (d is Expr_And) { return ((Expr_And)d)._right; }
        if (d is Expr_Imp) { return ((Expr_Imp)d)._right; }
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
    public BigInteger dtor_value {
      get {
        var d = this;
        return ((Expr_Int)d)._value;
      }
    }
    public abstract _IExpr DowncastClone();
    public static AlcorProofKernel._IExpr Not(AlcorProofKernel._IExpr expr) {
      return AlcorProofKernel.Expr.create_Imp(expr, AlcorProofKernel.Expr.create_False());
    }
    public AlcorProofKernel._IExpr apply(AlcorProofKernel._IExpr expr) {
      return AlcorProofKernel.Expr.create_App(this, expr);
    }
    public AlcorProofKernel._IExpr apply2(AlcorProofKernel._IExpr expr1, AlcorProofKernel._IExpr expr2) {
      return AlcorProofKernel.Expr.create_App(AlcorProofKernel.Expr.create_App(this, expr1), expr2);
    }
    public static AlcorProofKernel._IExpr ifthenelse(AlcorProofKernel._IExpr cond, AlcorProofKernel._IExpr thn, AlcorProofKernel._IExpr els) {
      return AlcorProofKernel.Expr.create_And(AlcorProofKernel.Expr.create_Imp(cond, thn), AlcorProofKernel.Expr.create_Imp(AlcorProofKernel.Expr.Not(cond), els));
    }
    public AlcorProofKernel._IExpr simplify(Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr> post, AlcorProofKernel._ISimplificationConfig config) {
      var _pat_let_tv0 = post;
      var _pat_let_tv1 = config;
      var _pat_let_tv2 = post;
      var _pat_let_tv3 = config;
      var _pat_let_tv4 = post;
      var _pat_let_tv5 = config;
      var _pat_let_tv6 = post;
      var _pat_let_tv7 = config;
      var _pat_let_tv8 = post;
      var _pat_let_tv9 = config;
      var _pat_let_tv10 = post;
      var _pat_let_tv11 = config;
      var _pat_let_tv12 = post;
      var _pat_let_tv13 = config;
      var _pat_let_tv14 = post;
      var _pat_let_tv15 = config;
      var _pat_let_tv16 = post;
      var _pat_let_tv17 = config;
      var _pat_let_tv18 = post;
      var _pat_let_tv19 = config;
      var _pat_let_tv20 = config;
      var _pat_let_tv21 = post;
      var _pat_let_tv22 = config;
      var _pat_let_tv23 = post;
      var _pat_let_tv24 = config;
      var _pat_let_tv25 = post;
      var _pat_let_tv26 = config;
      var _pat_let_tv27 = config;
      var _pat_let_tv28 = post;
      var _pat_let_tv29 = config;
      if (((config).dtor_betaDepth).Sign == 0) {
        return this;
      } else {
        AlcorProofKernel._IExpr res = ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source0) => {
          if (_source0.is_True) {
            return this;
          } else if (_source0.is_False) {
            return this;
          } else if (_source0.is_And) {
            AlcorProofKernel._IExpr __mcc_h0 = _source0.dtor_left;
            AlcorProofKernel._IExpr __mcc_h1 = _source0.dtor_right;
            return Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(__mcc_h1, _pat_let0_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let0_0, right => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(__mcc_h0, _pat_let1_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let1_0, left => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((left).simplify(_pat_let_tv0, _pat_let_tv1), _pat_let2_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let2_0, lSimp => (((lSimp).is_True) ? ((right).simplify(_pat_let_tv2, _pat_let_tv3)) : ((((lSimp).is_False) ? (AlcorProofKernel.Expr.create_False()) : (Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((right).simplify(_pat_let_tv4, _pat_let_tv5), _pat_let3_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let3_0, rSimp => (((rSimp).is_True) ? (lSimp) : ((((rSimp).is_False) ? (AlcorProofKernel.Expr.create_False()) : (AlcorProofKernel.Expr.create_And(rSimp, rSimp)))))))))))))))));
          } else if (_source0.is_Imp) {
            AlcorProofKernel._IExpr __mcc_h2 = _source0.dtor_left;
            AlcorProofKernel._IExpr __mcc_h3 = _source0.dtor_right;
            return Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(__mcc_h3, _pat_let4_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let4_0, _10_right => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(__mcc_h2, _pat_let5_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let5_0, _11_left => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((_11_left).simplify(_pat_let_tv6, _pat_let_tv7), _pat_let6_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let6_0, _12_lSimp => (((_12_lSimp).is_True) ? ((_10_right).simplify(_pat_let_tv8, _pat_let_tv9)) : ((((_12_lSimp).is_False) ? (AlcorProofKernel.Expr.create_True()) : (Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((_10_right).simplify(_pat_let_tv10, _pat_let_tv11), _pat_let7_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let7_0, _13_rSimp => (((_13_rSimp).is_True) ? (AlcorProofKernel.Expr.create_True()) : (AlcorProofKernel.Expr.create_Imp(_12_lSimp, _13_rSimp)))))))))))))));
          } else if (_source0.is_Or) {
            AlcorProofKernel._IExpr _14___mcc_h4 = _source0.dtor_left;
            AlcorProofKernel._IExpr _15___mcc_h5 = _source0.dtor_right;
            return Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_15___mcc_h5, _pat_let8_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let8_0, _16_right => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_14___mcc_h4, _pat_let9_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let9_0, _17_left => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((_17_left).simplify(_pat_let_tv12, _pat_let_tv13), _pat_let10_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let10_0, _18_lSimp => (((_18_lSimp).is_False) ? ((_16_right).simplify(_pat_let_tv14, _pat_let_tv15)) : ((((_18_lSimp).is_True) ? (AlcorProofKernel.Expr.create_True()) : (Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((_16_right).simplify(_pat_let_tv16, _pat_let_tv17), _pat_let11_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let11_0, _19_rSimp => (((_19_rSimp).is_True) ? (AlcorProofKernel.Expr.create_True()) : ((((_19_rSimp).is_False) ? (_18_lSimp) : (AlcorProofKernel.Expr.create_Or(_18_lSimp, _19_rSimp)))))))))))))))));
          } else if (_source0.is_Var) {
            AlcorProofKernel._IIdentifier _20___mcc_h6 = _source0.dtor_id;
            return this;
          } else if (_source0.is_Abs) {
            AlcorProofKernel._IIdentifier _21___mcc_h7 = _source0.dtor_id;
            AlcorProofKernel._IExpr _22___mcc_h8 = _source0.dtor_body;
            return Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_22___mcc_h8, _pat_let12_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let12_0, _23_body => Dafny.Helpers.Let<AlcorProofKernel._IIdentifier, AlcorProofKernel._IExpr>(_21___mcc_h7, _pat_let13_0 => Dafny.Helpers.Let<AlcorProofKernel._IIdentifier, AlcorProofKernel._IExpr>(_pat_let13_0, _24_id => (((_pat_let_tv20).dtor_insideAbs) ? (AlcorProofKernel.Expr.create_Abs(_24_id, (_23_body).simplify(_pat_let_tv18, _pat_let_tv19))) : (this))))));
          } else if (_source0.is_App) {
            AlcorProofKernel._IExpr _25___mcc_h9 = _source0.dtor_left;
            AlcorProofKernel._IExpr _26___mcc_h10 = _source0.dtor_right;
            return Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_26___mcc_h10, _pat_let14_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let14_0, _27_right => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_25___mcc_h9, _pat_let15_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let15_0, _28_left => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((_28_left).simplify(_pat_let_tv21, _pat_let_tv22), _pat_let16_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let16_0, _29_lSimp => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>((_27_right).simplify(_pat_let_tv23, _pat_let_tv24), _pat_let17_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let17_0, _30_rSimp => (((_29_lSimp).is_Abs) ? ((((_29_lSimp).dtor_body).Bind((_29_lSimp).dtor_id, _30_rSimp, (_30_rSimp).FreeVars())).simplify(_pat_let_tv25, Dafny.Helpers.Let<AlcorProofKernel._ISimplificationConfig, AlcorProofKernel._ISimplificationConfig>(_pat_let_tv26, _pat_let18_0 => Dafny.Helpers.Let<AlcorProofKernel._ISimplificationConfig, AlcorProofKernel._ISimplificationConfig>(_pat_let18_0, _31_dt__update__tmp_h0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._ISimplificationConfig>(((_pat_let_tv27).dtor_betaDepth) - (BigInteger.One), _pat_let19_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._ISimplificationConfig>(_pat_let19_0, _32_dt__update_hbetaDepth_h0 => AlcorProofKernel.SimplificationConfig.create((_31_dt__update__tmp_h0).dtor_insideAbs, _32_dt__update_hbetaDepth_h0))))))) : (AlcorProofKernel.Expr.create_App(_29_lSimp, _30_rSimp)))))))))));
          } else if (_source0.is_Forall) {
            AlcorProofKernel._IExpr _33___mcc_h11 = _source0.dtor_body;
            return Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_33___mcc_h11, _pat_let20_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let20_0, _34_body => AlcorProofKernel.Expr.create_Forall((_34_body).simplify(_pat_let_tv28, _pat_let_tv29))));
          } else {
            BigInteger _35___mcc_h12 = _source0.dtor_value;
            return this;
          }
        }))(this);
        AlcorProofKernel._IExpr _36_res = ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source1) => {
          if (_source1.is_True) {
            return res;
          } else if (_source1.is_False) {
            return res;
          } else if (_source1.is_And) {
            AlcorProofKernel._IExpr _37___mcc_h13 = _source1.dtor_left;
            AlcorProofKernel._IExpr _38___mcc_h14 = _source1.dtor_right;
            return res;
          } else if (_source1.is_Imp) {
            AlcorProofKernel._IExpr _39___mcc_h17 = _source1.dtor_left;
            AlcorProofKernel._IExpr _40___mcc_h18 = _source1.dtor_right;
            return res;
          } else if (_source1.is_Or) {
            AlcorProofKernel._IExpr _41___mcc_h21 = _source1.dtor_left;
            AlcorProofKernel._IExpr _42___mcc_h22 = _source1.dtor_right;
            return res;
          } else if (_source1.is_Var) {
            AlcorProofKernel._IIdentifier _43___mcc_h25 = _source1.dtor_id;
            return res;
          } else if (_source1.is_Abs) {
            AlcorProofKernel._IIdentifier _44___mcc_h27 = _source1.dtor_id;
            AlcorProofKernel._IExpr _45___mcc_h28 = _source1.dtor_body;
            return res;
          } else if (_source1.is_App) {
            AlcorProofKernel._IExpr _46___mcc_h31 = _source1.dtor_left;
            AlcorProofKernel._IExpr _47___mcc_h32 = _source1.dtor_right;
            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source2) => {
              if (_source2.is_True) {
                return res;
              } else if (_source2.is_False) {
                return res;
              } else if (_source2.is_And) {
                AlcorProofKernel._IExpr _48___mcc_h35 = _source2.dtor_left;
                AlcorProofKernel._IExpr _49___mcc_h36 = _source2.dtor_right;
                return res;
              } else if (_source2.is_Imp) {
                AlcorProofKernel._IExpr _50___mcc_h39 = _source2.dtor_left;
                AlcorProofKernel._IExpr _51___mcc_h40 = _source2.dtor_right;
                return res;
              } else if (_source2.is_Or) {
                AlcorProofKernel._IExpr _52___mcc_h43 = _source2.dtor_left;
                AlcorProofKernel._IExpr _53___mcc_h44 = _source2.dtor_right;
                return res;
              } else if (_source2.is_Var) {
                AlcorProofKernel._IIdentifier _54___mcc_h47 = _source2.dtor_id;
                return res;
              } else if (_source2.is_Abs) {
                AlcorProofKernel._IIdentifier _55___mcc_h49 = _source2.dtor_id;
                AlcorProofKernel._IExpr _56___mcc_h50 = _source2.dtor_body;
                return res;
              } else if (_source2.is_App) {
                AlcorProofKernel._IExpr _57___mcc_h53 = _source2.dtor_left;
                AlcorProofKernel._IExpr _58___mcc_h54 = _source2.dtor_right;
                return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source3) => {
                  if (_source3.is_True) {
                    return res;
                  } else if (_source3.is_False) {
                    return res;
                  } else if (_source3.is_And) {
                    AlcorProofKernel._IExpr _59___mcc_h57 = _source3.dtor_left;
                    AlcorProofKernel._IExpr _60___mcc_h58 = _source3.dtor_right;
                    return res;
                  } else if (_source3.is_Imp) {
                    AlcorProofKernel._IExpr _61___mcc_h61 = _source3.dtor_left;
                    AlcorProofKernel._IExpr _62___mcc_h62 = _source3.dtor_right;
                    return res;
                  } else if (_source3.is_Or) {
                    AlcorProofKernel._IExpr _63___mcc_h65 = _source3.dtor_left;
                    AlcorProofKernel._IExpr _64___mcc_h66 = _source3.dtor_right;
                    return res;
                  } else if (_source3.is_Var) {
                    AlcorProofKernel._IIdentifier _65___mcc_h69 = _source3.dtor_id;
                    return ((System.Func<AlcorProofKernel._IIdentifier, AlcorProofKernel._IExpr>)((_source4) => {
                      Dafny.ISequence<Dafny.Rune> _66___mcc_h71 = _source4.dtor_name;
                      BigInteger _67___mcc_h72 = _source4.dtor_version;
                      Dafny.ISequence<Dafny.Rune> _68___mcc_h73 = _source4.dtor_lbl;
                      return (((_67___mcc_h72).Sign == 0) ? (((object.Equals(_68___mcc_h73, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_47___mcc_h32, _pat_let21_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let21_0, _69_right => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_58___mcc_h54, _pat_let22_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let22_0, _70_left => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr>(_66___mcc_h71, _pat_let23_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr>(_pat_let23_0, _71_operator => ((System.Func<_System._ITuple3<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>, AlcorProofKernel._IExpr>)((_source5) => {
                        Dafny.ISequence<Dafny.Rune> _72___mcc_h97 = _source5.dtor__0;
                        AlcorProofKernel._IExpr _73___mcc_h98 = _source5.dtor__1;
                        AlcorProofKernel._IExpr _74___mcc_h99 = _source5.dtor__2;
                        return ((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source6) => {
                          if (_source6.is_True) {
                            return res;
                          } else if (_source6.is_False) {
                            return res;
                          } else if (_source6.is_And) {
                            AlcorProofKernel._IExpr _75___mcc_h103 = _source6.dtor_left;
                            AlcorProofKernel._IExpr _76___mcc_h104 = _source6.dtor_right;
                            return res;
                          } else if (_source6.is_Imp) {
                            AlcorProofKernel._IExpr _77___mcc_h107 = _source6.dtor_left;
                            AlcorProofKernel._IExpr _78___mcc_h108 = _source6.dtor_right;
                            return res;
                          } else if (_source6.is_Or) {
                            AlcorProofKernel._IExpr _79___mcc_h111 = _source6.dtor_left;
                            AlcorProofKernel._IExpr _80___mcc_h112 = _source6.dtor_right;
                            return res;
                          } else if (_source6.is_Var) {
                            AlcorProofKernel._IIdentifier _81___mcc_h115 = _source6.dtor_id;
                            return res;
                          } else if (_source6.is_Abs) {
                            AlcorProofKernel._IIdentifier _82___mcc_h117 = _source6.dtor_id;
                            AlcorProofKernel._IExpr _83___mcc_h118 = _source6.dtor_body;
                            return res;
                          } else if (_source6.is_App) {
                            AlcorProofKernel._IExpr _84___mcc_h121 = _source6.dtor_left;
                            AlcorProofKernel._IExpr _85___mcc_h122 = _source6.dtor_right;
                            return res;
                          } else if (_source6.is_Forall) {
                            AlcorProofKernel._IExpr _86___mcc_h125 = _source6.dtor_body;
                            return res;
                          } else {
                            BigInteger _87___mcc_h127 = _source6.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source7) => {
                              if (_source7.is_True) {
                                return res;
                              } else if (_source7.is_False) {
                                return res;
                              } else if (_source7.is_And) {
                                AlcorProofKernel._IExpr _88___mcc_h129 = _source7.dtor_left;
                                AlcorProofKernel._IExpr _89___mcc_h130 = _source7.dtor_right;
                                return res;
                              } else if (_source7.is_Imp) {
                                AlcorProofKernel._IExpr _90___mcc_h133 = _source7.dtor_left;
                                AlcorProofKernel._IExpr _91___mcc_h134 = _source7.dtor_right;
                                return res;
                              } else if (_source7.is_Or) {
                                AlcorProofKernel._IExpr _92___mcc_h137 = _source7.dtor_left;
                                AlcorProofKernel._IExpr _93___mcc_h138 = _source7.dtor_right;
                                return res;
                              } else if (_source7.is_Var) {
                                AlcorProofKernel._IIdentifier _94___mcc_h141 = _source7.dtor_id;
                                return res;
                              } else if (_source7.is_Abs) {
                                AlcorProofKernel._IIdentifier _95___mcc_h143 = _source7.dtor_id;
                                AlcorProofKernel._IExpr _96___mcc_h144 = _source7.dtor_body;
                                return res;
                              } else if (_source7.is_App) {
                                AlcorProofKernel._IExpr _97___mcc_h147 = _source7.dtor_left;
                                AlcorProofKernel._IExpr _98___mcc_h148 = _source7.dtor_right;
                                return res;
                              } else if (_source7.is_Forall) {
                                AlcorProofKernel._IExpr _99___mcc_h151 = _source7.dtor_body;
                                return res;
                              } else {
                                BigInteger _100___mcc_h153 = _source7.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_100___mcc_h153, _pat_let24_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let24_0, _101_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_87___mcc_h127, _pat_let25_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let25_0, _102_l => (((_101_r).Sign == 1) ? (AlcorProofKernel.Expr.create_Int(Dafny.Helpers.EuclideanModulus(_102_l, _101_r))) : (res))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source8) => {
                          if (_source8.is_True) {
                            return res;
                          } else if (_source8.is_False) {
                            return res;
                          } else if (_source8.is_And) {
                            AlcorProofKernel._IExpr _103___mcc_h155 = _source8.dtor_left;
                            AlcorProofKernel._IExpr _104___mcc_h156 = _source8.dtor_right;
                            return res;
                          } else if (_source8.is_Imp) {
                            AlcorProofKernel._IExpr _105___mcc_h159 = _source8.dtor_left;
                            AlcorProofKernel._IExpr _106___mcc_h160 = _source8.dtor_right;
                            return res;
                          } else if (_source8.is_Or) {
                            AlcorProofKernel._IExpr _107___mcc_h163 = _source8.dtor_left;
                            AlcorProofKernel._IExpr _108___mcc_h164 = _source8.dtor_right;
                            return res;
                          } else if (_source8.is_Var) {
                            AlcorProofKernel._IIdentifier _109___mcc_h167 = _source8.dtor_id;
                            return res;
                          } else if (_source8.is_Abs) {
                            AlcorProofKernel._IIdentifier _110___mcc_h169 = _source8.dtor_id;
                            AlcorProofKernel._IExpr _111___mcc_h170 = _source8.dtor_body;
                            return res;
                          } else if (_source8.is_App) {
                            AlcorProofKernel._IExpr _112___mcc_h173 = _source8.dtor_left;
                            AlcorProofKernel._IExpr _113___mcc_h174 = _source8.dtor_right;
                            return res;
                          } else if (_source8.is_Forall) {
                            AlcorProofKernel._IExpr _114___mcc_h177 = _source8.dtor_body;
                            return res;
                          } else {
                            BigInteger _115___mcc_h179 = _source8.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source9) => {
                              if (_source9.is_True) {
                                return res;
                              } else if (_source9.is_False) {
                                return res;
                              } else if (_source9.is_And) {
                                AlcorProofKernel._IExpr _116___mcc_h181 = _source9.dtor_left;
                                AlcorProofKernel._IExpr _117___mcc_h182 = _source9.dtor_right;
                                return res;
                              } else if (_source9.is_Imp) {
                                AlcorProofKernel._IExpr _118___mcc_h185 = _source9.dtor_left;
                                AlcorProofKernel._IExpr _119___mcc_h186 = _source9.dtor_right;
                                return res;
                              } else if (_source9.is_Or) {
                                AlcorProofKernel._IExpr _120___mcc_h189 = _source9.dtor_left;
                                AlcorProofKernel._IExpr _121___mcc_h190 = _source9.dtor_right;
                                return res;
                              } else if (_source9.is_Var) {
                                AlcorProofKernel._IIdentifier _122___mcc_h193 = _source9.dtor_id;
                                return res;
                              } else if (_source9.is_Abs) {
                                AlcorProofKernel._IIdentifier _123___mcc_h195 = _source9.dtor_id;
                                AlcorProofKernel._IExpr _124___mcc_h196 = _source9.dtor_body;
                                return res;
                              } else if (_source9.is_App) {
                                AlcorProofKernel._IExpr _125___mcc_h199 = _source9.dtor_left;
                                AlcorProofKernel._IExpr _126___mcc_h200 = _source9.dtor_right;
                                return res;
                              } else if (_source9.is_Forall) {
                                AlcorProofKernel._IExpr _127___mcc_h203 = _source9.dtor_body;
                                return res;
                              } else {
                                BigInteger _128___mcc_h205 = _source9.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_128___mcc_h205, _pat_let26_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let26_0, _129_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_115___mcc_h179, _pat_let27_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let27_0, _130_l => AlcorProofKernel.Expr.create_Int((_130_l) * (_129_r))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source10) => {
                          if (_source10.is_True) {
                            return res;
                          } else if (_source10.is_False) {
                            return res;
                          } else if (_source10.is_And) {
                            AlcorProofKernel._IExpr _131___mcc_h207 = _source10.dtor_left;
                            AlcorProofKernel._IExpr _132___mcc_h208 = _source10.dtor_right;
                            return res;
                          } else if (_source10.is_Imp) {
                            AlcorProofKernel._IExpr _133___mcc_h211 = _source10.dtor_left;
                            AlcorProofKernel._IExpr _134___mcc_h212 = _source10.dtor_right;
                            return res;
                          } else if (_source10.is_Or) {
                            AlcorProofKernel._IExpr _135___mcc_h215 = _source10.dtor_left;
                            AlcorProofKernel._IExpr _136___mcc_h216 = _source10.dtor_right;
                            return res;
                          } else if (_source10.is_Var) {
                            AlcorProofKernel._IIdentifier _137___mcc_h219 = _source10.dtor_id;
                            return res;
                          } else if (_source10.is_Abs) {
                            AlcorProofKernel._IIdentifier _138___mcc_h221 = _source10.dtor_id;
                            AlcorProofKernel._IExpr _139___mcc_h222 = _source10.dtor_body;
                            return res;
                          } else if (_source10.is_App) {
                            AlcorProofKernel._IExpr _140___mcc_h225 = _source10.dtor_left;
                            AlcorProofKernel._IExpr _141___mcc_h226 = _source10.dtor_right;
                            return res;
                          } else if (_source10.is_Forall) {
                            AlcorProofKernel._IExpr _142___mcc_h229 = _source10.dtor_body;
                            return res;
                          } else {
                            BigInteger _143___mcc_h231 = _source10.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source11) => {
                              if (_source11.is_True) {
                                return res;
                              } else if (_source11.is_False) {
                                return res;
                              } else if (_source11.is_And) {
                                AlcorProofKernel._IExpr _144___mcc_h233 = _source11.dtor_left;
                                AlcorProofKernel._IExpr _145___mcc_h234 = _source11.dtor_right;
                                return res;
                              } else if (_source11.is_Imp) {
                                AlcorProofKernel._IExpr _146___mcc_h237 = _source11.dtor_left;
                                AlcorProofKernel._IExpr _147___mcc_h238 = _source11.dtor_right;
                                return res;
                              } else if (_source11.is_Or) {
                                AlcorProofKernel._IExpr _148___mcc_h241 = _source11.dtor_left;
                                AlcorProofKernel._IExpr _149___mcc_h242 = _source11.dtor_right;
                                return res;
                              } else if (_source11.is_Var) {
                                AlcorProofKernel._IIdentifier _150___mcc_h245 = _source11.dtor_id;
                                return res;
                              } else if (_source11.is_Abs) {
                                AlcorProofKernel._IIdentifier _151___mcc_h247 = _source11.dtor_id;
                                AlcorProofKernel._IExpr _152___mcc_h248 = _source11.dtor_body;
                                return res;
                              } else if (_source11.is_App) {
                                AlcorProofKernel._IExpr _153___mcc_h251 = _source11.dtor_left;
                                AlcorProofKernel._IExpr _154___mcc_h252 = _source11.dtor_right;
                                return res;
                              } else if (_source11.is_Forall) {
                                AlcorProofKernel._IExpr _155___mcc_h255 = _source11.dtor_body;
                                return res;
                              } else {
                                BigInteger _156___mcc_h257 = _source11.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_156___mcc_h257, _pat_let28_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let28_0, _157_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_143___mcc_h231, _pat_let29_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let29_0, _158_l => (((_157_r).Sign != 0) ? (AlcorProofKernel.Expr.create_Int(Dafny.Helpers.EuclideanDivision(_158_l, _157_r))) : (res))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source12) => {
                          if (_source12.is_True) {
                            return res;
                          } else if (_source12.is_False) {
                            return res;
                          } else if (_source12.is_And) {
                            AlcorProofKernel._IExpr _159___mcc_h259 = _source12.dtor_left;
                            AlcorProofKernel._IExpr _160___mcc_h260 = _source12.dtor_right;
                            return res;
                          } else if (_source12.is_Imp) {
                            AlcorProofKernel._IExpr _161___mcc_h263 = _source12.dtor_left;
                            AlcorProofKernel._IExpr _162___mcc_h264 = _source12.dtor_right;
                            return res;
                          } else if (_source12.is_Or) {
                            AlcorProofKernel._IExpr _163___mcc_h267 = _source12.dtor_left;
                            AlcorProofKernel._IExpr _164___mcc_h268 = _source12.dtor_right;
                            return res;
                          } else if (_source12.is_Var) {
                            AlcorProofKernel._IIdentifier _165___mcc_h271 = _source12.dtor_id;
                            return res;
                          } else if (_source12.is_Abs) {
                            AlcorProofKernel._IIdentifier _166___mcc_h273 = _source12.dtor_id;
                            AlcorProofKernel._IExpr _167___mcc_h274 = _source12.dtor_body;
                            return res;
                          } else if (_source12.is_App) {
                            AlcorProofKernel._IExpr _168___mcc_h277 = _source12.dtor_left;
                            AlcorProofKernel._IExpr _169___mcc_h278 = _source12.dtor_right;
                            return res;
                          } else if (_source12.is_Forall) {
                            AlcorProofKernel._IExpr _170___mcc_h281 = _source12.dtor_body;
                            return res;
                          } else {
                            BigInteger _171___mcc_h283 = _source12.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source13) => {
                              if (_source13.is_True) {
                                return res;
                              } else if (_source13.is_False) {
                                return res;
                              } else if (_source13.is_And) {
                                AlcorProofKernel._IExpr _172___mcc_h285 = _source13.dtor_left;
                                AlcorProofKernel._IExpr _173___mcc_h286 = _source13.dtor_right;
                                return res;
                              } else if (_source13.is_Imp) {
                                AlcorProofKernel._IExpr _174___mcc_h289 = _source13.dtor_left;
                                AlcorProofKernel._IExpr _175___mcc_h290 = _source13.dtor_right;
                                return res;
                              } else if (_source13.is_Or) {
                                AlcorProofKernel._IExpr _176___mcc_h293 = _source13.dtor_left;
                                AlcorProofKernel._IExpr _177___mcc_h294 = _source13.dtor_right;
                                return res;
                              } else if (_source13.is_Var) {
                                AlcorProofKernel._IIdentifier _178___mcc_h297 = _source13.dtor_id;
                                return res;
                              } else if (_source13.is_Abs) {
                                AlcorProofKernel._IIdentifier _179___mcc_h299 = _source13.dtor_id;
                                AlcorProofKernel._IExpr _180___mcc_h300 = _source13.dtor_body;
                                return res;
                              } else if (_source13.is_App) {
                                AlcorProofKernel._IExpr _181___mcc_h303 = _source13.dtor_left;
                                AlcorProofKernel._IExpr _182___mcc_h304 = _source13.dtor_right;
                                return res;
                              } else if (_source13.is_Forall) {
                                AlcorProofKernel._IExpr _183___mcc_h307 = _source13.dtor_body;
                                return res;
                              } else {
                                BigInteger _184___mcc_h309 = _source13.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_184___mcc_h309, _pat_let30_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let30_0, _185_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_171___mcc_h283, _pat_let31_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let31_0, _186_l => AlcorProofKernel.Expr.create_Int((_186_l) + (_185_r))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source14) => {
                          if (_source14.is_True) {
                            return res;
                          } else if (_source14.is_False) {
                            return res;
                          } else if (_source14.is_And) {
                            AlcorProofKernel._IExpr _187___mcc_h311 = _source14.dtor_left;
                            AlcorProofKernel._IExpr _188___mcc_h312 = _source14.dtor_right;
                            return res;
                          } else if (_source14.is_Imp) {
                            AlcorProofKernel._IExpr _189___mcc_h315 = _source14.dtor_left;
                            AlcorProofKernel._IExpr _190___mcc_h316 = _source14.dtor_right;
                            return res;
                          } else if (_source14.is_Or) {
                            AlcorProofKernel._IExpr _191___mcc_h319 = _source14.dtor_left;
                            AlcorProofKernel._IExpr _192___mcc_h320 = _source14.dtor_right;
                            return res;
                          } else if (_source14.is_Var) {
                            AlcorProofKernel._IIdentifier _193___mcc_h323 = _source14.dtor_id;
                            return res;
                          } else if (_source14.is_Abs) {
                            AlcorProofKernel._IIdentifier _194___mcc_h325 = _source14.dtor_id;
                            AlcorProofKernel._IExpr _195___mcc_h326 = _source14.dtor_body;
                            return res;
                          } else if (_source14.is_App) {
                            AlcorProofKernel._IExpr _196___mcc_h329 = _source14.dtor_left;
                            AlcorProofKernel._IExpr _197___mcc_h330 = _source14.dtor_right;
                            return res;
                          } else if (_source14.is_Forall) {
                            AlcorProofKernel._IExpr _198___mcc_h333 = _source14.dtor_body;
                            return res;
                          } else {
                            BigInteger _199___mcc_h335 = _source14.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source15) => {
                              if (_source15.is_True) {
                                return res;
                              } else if (_source15.is_False) {
                                return res;
                              } else if (_source15.is_And) {
                                AlcorProofKernel._IExpr _200___mcc_h337 = _source15.dtor_left;
                                AlcorProofKernel._IExpr _201___mcc_h338 = _source15.dtor_right;
                                return res;
                              } else if (_source15.is_Imp) {
                                AlcorProofKernel._IExpr _202___mcc_h341 = _source15.dtor_left;
                                AlcorProofKernel._IExpr _203___mcc_h342 = _source15.dtor_right;
                                return res;
                              } else if (_source15.is_Or) {
                                AlcorProofKernel._IExpr _204___mcc_h345 = _source15.dtor_left;
                                AlcorProofKernel._IExpr _205___mcc_h346 = _source15.dtor_right;
                                return res;
                              } else if (_source15.is_Var) {
                                AlcorProofKernel._IIdentifier _206___mcc_h349 = _source15.dtor_id;
                                return res;
                              } else if (_source15.is_Abs) {
                                AlcorProofKernel._IIdentifier _207___mcc_h351 = _source15.dtor_id;
                                AlcorProofKernel._IExpr _208___mcc_h352 = _source15.dtor_body;
                                return res;
                              } else if (_source15.is_App) {
                                AlcorProofKernel._IExpr _209___mcc_h355 = _source15.dtor_left;
                                AlcorProofKernel._IExpr _210___mcc_h356 = _source15.dtor_right;
                                return res;
                              } else if (_source15.is_Forall) {
                                AlcorProofKernel._IExpr _211___mcc_h359 = _source15.dtor_body;
                                return res;
                              } else {
                                BigInteger _212___mcc_h361 = _source15.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_212___mcc_h361, _pat_let32_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let32_0, _213_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_199___mcc_h335, _pat_let33_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let33_0, _214_l => AlcorProofKernel.Expr.create_Int((_214_l) - (_213_r))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source16) => {
                          if (_source16.is_True) {
                            return res;
                          } else if (_source16.is_False) {
                            return res;
                          } else if (_source16.is_And) {
                            AlcorProofKernel._IExpr _215___mcc_h363 = _source16.dtor_left;
                            AlcorProofKernel._IExpr _216___mcc_h364 = _source16.dtor_right;
                            return res;
                          } else if (_source16.is_Imp) {
                            AlcorProofKernel._IExpr _217___mcc_h367 = _source16.dtor_left;
                            AlcorProofKernel._IExpr _218___mcc_h368 = _source16.dtor_right;
                            return res;
                          } else if (_source16.is_Or) {
                            AlcorProofKernel._IExpr _219___mcc_h371 = _source16.dtor_left;
                            AlcorProofKernel._IExpr _220___mcc_h372 = _source16.dtor_right;
                            return res;
                          } else if (_source16.is_Var) {
                            AlcorProofKernel._IIdentifier _221___mcc_h375 = _source16.dtor_id;
                            return res;
                          } else if (_source16.is_Abs) {
                            AlcorProofKernel._IIdentifier _222___mcc_h377 = _source16.dtor_id;
                            AlcorProofKernel._IExpr _223___mcc_h378 = _source16.dtor_body;
                            return res;
                          } else if (_source16.is_App) {
                            AlcorProofKernel._IExpr _224___mcc_h381 = _source16.dtor_left;
                            AlcorProofKernel._IExpr _225___mcc_h382 = _source16.dtor_right;
                            return res;
                          } else if (_source16.is_Forall) {
                            AlcorProofKernel._IExpr _226___mcc_h385 = _source16.dtor_body;
                            return res;
                          } else {
                            BigInteger _227___mcc_h387 = _source16.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source17) => {
                              if (_source17.is_True) {
                                return res;
                              } else if (_source17.is_False) {
                                return res;
                              } else if (_source17.is_And) {
                                AlcorProofKernel._IExpr _228___mcc_h389 = _source17.dtor_left;
                                AlcorProofKernel._IExpr _229___mcc_h390 = _source17.dtor_right;
                                return res;
                              } else if (_source17.is_Imp) {
                                AlcorProofKernel._IExpr _230___mcc_h393 = _source17.dtor_left;
                                AlcorProofKernel._IExpr _231___mcc_h394 = _source17.dtor_right;
                                return res;
                              } else if (_source17.is_Or) {
                                AlcorProofKernel._IExpr _232___mcc_h397 = _source17.dtor_left;
                                AlcorProofKernel._IExpr _233___mcc_h398 = _source17.dtor_right;
                                return res;
                              } else if (_source17.is_Var) {
                                AlcorProofKernel._IIdentifier _234___mcc_h401 = _source17.dtor_id;
                                return res;
                              } else if (_source17.is_Abs) {
                                AlcorProofKernel._IIdentifier _235___mcc_h403 = _source17.dtor_id;
                                AlcorProofKernel._IExpr _236___mcc_h404 = _source17.dtor_body;
                                return res;
                              } else if (_source17.is_App) {
                                AlcorProofKernel._IExpr _237___mcc_h407 = _source17.dtor_left;
                                AlcorProofKernel._IExpr _238___mcc_h408 = _source17.dtor_right;
                                return res;
                              } else if (_source17.is_Forall) {
                                AlcorProofKernel._IExpr _239___mcc_h411 = _source17.dtor_body;
                                return res;
                              } else {
                                BigInteger _240___mcc_h413 = _source17.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_240___mcc_h413, _pat_let34_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let34_0, _241_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_227___mcc_h387, _pat_let35_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let35_0, _242_l => (((_242_l) > (_241_r)) ? (AlcorProofKernel.Expr.create_True()) : (AlcorProofKernel.Expr.create_False()))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source18) => {
                          if (_source18.is_True) {
                            return res;
                          } else if (_source18.is_False) {
                            return res;
                          } else if (_source18.is_And) {
                            AlcorProofKernel._IExpr _243___mcc_h415 = _source18.dtor_left;
                            AlcorProofKernel._IExpr _244___mcc_h416 = _source18.dtor_right;
                            return res;
                          } else if (_source18.is_Imp) {
                            AlcorProofKernel._IExpr _245___mcc_h419 = _source18.dtor_left;
                            AlcorProofKernel._IExpr _246___mcc_h420 = _source18.dtor_right;
                            return res;
                          } else if (_source18.is_Or) {
                            AlcorProofKernel._IExpr _247___mcc_h423 = _source18.dtor_left;
                            AlcorProofKernel._IExpr _248___mcc_h424 = _source18.dtor_right;
                            return res;
                          } else if (_source18.is_Var) {
                            AlcorProofKernel._IIdentifier _249___mcc_h427 = _source18.dtor_id;
                            return res;
                          } else if (_source18.is_Abs) {
                            AlcorProofKernel._IIdentifier _250___mcc_h429 = _source18.dtor_id;
                            AlcorProofKernel._IExpr _251___mcc_h430 = _source18.dtor_body;
                            return res;
                          } else if (_source18.is_App) {
                            AlcorProofKernel._IExpr _252___mcc_h433 = _source18.dtor_left;
                            AlcorProofKernel._IExpr _253___mcc_h434 = _source18.dtor_right;
                            return res;
                          } else if (_source18.is_Forall) {
                            AlcorProofKernel._IExpr _254___mcc_h437 = _source18.dtor_body;
                            return res;
                          } else {
                            BigInteger _255___mcc_h439 = _source18.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source19) => {
                              if (_source19.is_True) {
                                return res;
                              } else if (_source19.is_False) {
                                return res;
                              } else if (_source19.is_And) {
                                AlcorProofKernel._IExpr _256___mcc_h441 = _source19.dtor_left;
                                AlcorProofKernel._IExpr _257___mcc_h442 = _source19.dtor_right;
                                return res;
                              } else if (_source19.is_Imp) {
                                AlcorProofKernel._IExpr _258___mcc_h445 = _source19.dtor_left;
                                AlcorProofKernel._IExpr _259___mcc_h446 = _source19.dtor_right;
                                return res;
                              } else if (_source19.is_Or) {
                                AlcorProofKernel._IExpr _260___mcc_h449 = _source19.dtor_left;
                                AlcorProofKernel._IExpr _261___mcc_h450 = _source19.dtor_right;
                                return res;
                              } else if (_source19.is_Var) {
                                AlcorProofKernel._IIdentifier _262___mcc_h453 = _source19.dtor_id;
                                return res;
                              } else if (_source19.is_Abs) {
                                AlcorProofKernel._IIdentifier _263___mcc_h455 = _source19.dtor_id;
                                AlcorProofKernel._IExpr _264___mcc_h456 = _source19.dtor_body;
                                return res;
                              } else if (_source19.is_App) {
                                AlcorProofKernel._IExpr _265___mcc_h459 = _source19.dtor_left;
                                AlcorProofKernel._IExpr _266___mcc_h460 = _source19.dtor_right;
                                return res;
                              } else if (_source19.is_Forall) {
                                AlcorProofKernel._IExpr _267___mcc_h463 = _source19.dtor_body;
                                return res;
                              } else {
                                BigInteger _268___mcc_h465 = _source19.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_268___mcc_h465, _pat_let36_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let36_0, _269_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_255___mcc_h439, _pat_let37_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let37_0, _270_l => (((_270_l) < (_269_r)) ? (AlcorProofKernel.Expr.create_True()) : (AlcorProofKernel.Expr.create_False()))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source20) => {
                          if (_source20.is_True) {
                            return res;
                          } else if (_source20.is_False) {
                            return res;
                          } else if (_source20.is_And) {
                            AlcorProofKernel._IExpr _271___mcc_h467 = _source20.dtor_left;
                            AlcorProofKernel._IExpr _272___mcc_h468 = _source20.dtor_right;
                            return res;
                          } else if (_source20.is_Imp) {
                            AlcorProofKernel._IExpr _273___mcc_h471 = _source20.dtor_left;
                            AlcorProofKernel._IExpr _274___mcc_h472 = _source20.dtor_right;
                            return res;
                          } else if (_source20.is_Or) {
                            AlcorProofKernel._IExpr _275___mcc_h475 = _source20.dtor_left;
                            AlcorProofKernel._IExpr _276___mcc_h476 = _source20.dtor_right;
                            return res;
                          } else if (_source20.is_Var) {
                            AlcorProofKernel._IIdentifier _277___mcc_h479 = _source20.dtor_id;
                            return res;
                          } else if (_source20.is_Abs) {
                            AlcorProofKernel._IIdentifier _278___mcc_h481 = _source20.dtor_id;
                            AlcorProofKernel._IExpr _279___mcc_h482 = _source20.dtor_body;
                            return res;
                          } else if (_source20.is_App) {
                            AlcorProofKernel._IExpr _280___mcc_h485 = _source20.dtor_left;
                            AlcorProofKernel._IExpr _281___mcc_h486 = _source20.dtor_right;
                            return res;
                          } else if (_source20.is_Forall) {
                            AlcorProofKernel._IExpr _282___mcc_h489 = _source20.dtor_body;
                            return res;
                          } else {
                            BigInteger _283___mcc_h491 = _source20.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source21) => {
                              if (_source21.is_True) {
                                return res;
                              } else if (_source21.is_False) {
                                return res;
                              } else if (_source21.is_And) {
                                AlcorProofKernel._IExpr _284___mcc_h493 = _source21.dtor_left;
                                AlcorProofKernel._IExpr _285___mcc_h494 = _source21.dtor_right;
                                return res;
                              } else if (_source21.is_Imp) {
                                AlcorProofKernel._IExpr _286___mcc_h497 = _source21.dtor_left;
                                AlcorProofKernel._IExpr _287___mcc_h498 = _source21.dtor_right;
                                return res;
                              } else if (_source21.is_Or) {
                                AlcorProofKernel._IExpr _288___mcc_h501 = _source21.dtor_left;
                                AlcorProofKernel._IExpr _289___mcc_h502 = _source21.dtor_right;
                                return res;
                              } else if (_source21.is_Var) {
                                AlcorProofKernel._IIdentifier _290___mcc_h505 = _source21.dtor_id;
                                return res;
                              } else if (_source21.is_Abs) {
                                AlcorProofKernel._IIdentifier _291___mcc_h507 = _source21.dtor_id;
                                AlcorProofKernel._IExpr _292___mcc_h508 = _source21.dtor_body;
                                return res;
                              } else if (_source21.is_App) {
                                AlcorProofKernel._IExpr _293___mcc_h511 = _source21.dtor_left;
                                AlcorProofKernel._IExpr _294___mcc_h512 = _source21.dtor_right;
                                return res;
                              } else if (_source21.is_Forall) {
                                AlcorProofKernel._IExpr _295___mcc_h515 = _source21.dtor_body;
                                return res;
                              } else {
                                BigInteger _296___mcc_h517 = _source21.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_296___mcc_h517, _pat_let38_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let38_0, _297_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_283___mcc_h491, _pat_let39_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let39_0, _298_l => (((_298_l) >= (_297_r)) ? (AlcorProofKernel.Expr.create_True()) : (AlcorProofKernel.Expr.create_False()))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) ? (((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source22) => {
                          if (_source22.is_True) {
                            return res;
                          } else if (_source22.is_False) {
                            return res;
                          } else if (_source22.is_And) {
                            AlcorProofKernel._IExpr _299___mcc_h519 = _source22.dtor_left;
                            AlcorProofKernel._IExpr _300___mcc_h520 = _source22.dtor_right;
                            return res;
                          } else if (_source22.is_Imp) {
                            AlcorProofKernel._IExpr _301___mcc_h523 = _source22.dtor_left;
                            AlcorProofKernel._IExpr _302___mcc_h524 = _source22.dtor_right;
                            return res;
                          } else if (_source22.is_Or) {
                            AlcorProofKernel._IExpr _303___mcc_h527 = _source22.dtor_left;
                            AlcorProofKernel._IExpr _304___mcc_h528 = _source22.dtor_right;
                            return res;
                          } else if (_source22.is_Var) {
                            AlcorProofKernel._IIdentifier _305___mcc_h531 = _source22.dtor_id;
                            return res;
                          } else if (_source22.is_Abs) {
                            AlcorProofKernel._IIdentifier _306___mcc_h533 = _source22.dtor_id;
                            AlcorProofKernel._IExpr _307___mcc_h534 = _source22.dtor_body;
                            return res;
                          } else if (_source22.is_App) {
                            AlcorProofKernel._IExpr _308___mcc_h537 = _source22.dtor_left;
                            AlcorProofKernel._IExpr _309___mcc_h538 = _source22.dtor_right;
                            return res;
                          } else if (_source22.is_Forall) {
                            AlcorProofKernel._IExpr _310___mcc_h541 = _source22.dtor_body;
                            return res;
                          } else {
                            BigInteger _311___mcc_h543 = _source22.dtor_value;
                            return ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_source23) => {
                              if (_source23.is_True) {
                                return res;
                              } else if (_source23.is_False) {
                                return res;
                              } else if (_source23.is_And) {
                                AlcorProofKernel._IExpr _312___mcc_h545 = _source23.dtor_left;
                                AlcorProofKernel._IExpr _313___mcc_h546 = _source23.dtor_right;
                                return res;
                              } else if (_source23.is_Imp) {
                                AlcorProofKernel._IExpr _314___mcc_h549 = _source23.dtor_left;
                                AlcorProofKernel._IExpr _315___mcc_h550 = _source23.dtor_right;
                                return res;
                              } else if (_source23.is_Or) {
                                AlcorProofKernel._IExpr _316___mcc_h553 = _source23.dtor_left;
                                AlcorProofKernel._IExpr _317___mcc_h554 = _source23.dtor_right;
                                return res;
                              } else if (_source23.is_Var) {
                                AlcorProofKernel._IIdentifier _318___mcc_h557 = _source23.dtor_id;
                                return res;
                              } else if (_source23.is_Abs) {
                                AlcorProofKernel._IIdentifier _319___mcc_h559 = _source23.dtor_id;
                                AlcorProofKernel._IExpr _320___mcc_h560 = _source23.dtor_body;
                                return res;
                              } else if (_source23.is_App) {
                                AlcorProofKernel._IExpr _321___mcc_h563 = _source23.dtor_left;
                                AlcorProofKernel._IExpr _322___mcc_h564 = _source23.dtor_right;
                                return res;
                              } else if (_source23.is_Forall) {
                                AlcorProofKernel._IExpr _323___mcc_h567 = _source23.dtor_body;
                                return res;
                              } else {
                                BigInteger _324___mcc_h569 = _source23.dtor_value;
                                return Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_324___mcc_h569, _pat_let40_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let40_0, _325_r => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_311___mcc_h543, _pat_let41_0 => Dafny.Helpers.Let<BigInteger, AlcorProofKernel._IExpr>(_pat_let41_0, _326_l => (((_326_l) <= (_325_r)) ? (AlcorProofKernel.Expr.create_True()) : (AlcorProofKernel.Expr.create_False()))))));
                              }
                            }))(_74___mcc_h99);
                          }
                        }))(_73___mcc_h98)) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) ? (Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_74___mcc_h99, _pat_let42_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let42_0, _327_r => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_73___mcc_h98, _pat_let43_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let43_0, _328_l => ((object.Equals(_328_l, _327_r)) ? (AlcorProofKernel.Expr.create_True()) : (res))))))) : (((object.Equals(_72___mcc_h97, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="))) ? (Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_74___mcc_h99, _pat_let44_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let44_0, _329_r => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_73___mcc_h98, _pat_let45_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>(_pat_let45_0, _330_l => ((object.Equals(_330_l, _329_r)) ? (AlcorProofKernel.Expr.create_False()) : (res))))))) : (res))))))))))))))))))))));
                      }))(_System.Tuple3<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>.create(_71_operator, _70_left, _69_right))))))))) : (res))) : (res));
                    }))(_65___mcc_h69);
                  } else if (_source3.is_Abs) {
                    AlcorProofKernel._IIdentifier _331___mcc_h77 = _source3.dtor_id;
                    AlcorProofKernel._IExpr _332___mcc_h78 = _source3.dtor_body;
                    return res;
                  } else if (_source3.is_App) {
                    AlcorProofKernel._IExpr _333___mcc_h81 = _source3.dtor_left;
                    AlcorProofKernel._IExpr _334___mcc_h82 = _source3.dtor_right;
                    return res;
                  } else if (_source3.is_Forall) {
                    AlcorProofKernel._IExpr _335___mcc_h85 = _source3.dtor_body;
                    return res;
                  } else {
                    BigInteger _336___mcc_h87 = _source3.dtor_value;
                    return res;
                  }
                }))(_57___mcc_h53);
              } else if (_source2.is_Forall) {
                AlcorProofKernel._IExpr _337___mcc_h89 = _source2.dtor_body;
                return res;
              } else {
                BigInteger _338___mcc_h91 = _source2.dtor_value;
                return res;
              }
            }))(_46___mcc_h31);
          } else if (_source1.is_Forall) {
            AlcorProofKernel._IExpr _339___mcc_h93 = _source1.dtor_body;
            return res;
          } else {
            BigInteger _340___mcc_h95 = _source1.dtor_value;
            return res;
          }
        }))(res);
        return Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>>(post)(_36_res);
      }
    }
    public Dafny.ISet<AlcorProofKernel._IIdentifier> FreeVars() {
      if ((((this).is_True) || ((this).is_False)) || ((this).is_Int)) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements();
      } else if (((((this).is_And) || ((this).is_Imp)) || ((this).is_Or)) || ((this).is_App)) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.Union(((this).dtor_left).FreeVars(), ((this).dtor_right).FreeVars());
      } else if ((this).is_Var) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements((this).dtor_id);
      } else if ((this).is_Abs) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.Difference(((this).dtor_body).FreeVars(), Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements((this).dtor_id));
      } else if ((this).is_Forall) {
        return ((this).dtor_body).FreeVars();
      } else {
        _System._ITuple0 _source24 = _System.Tuple0.create();
        throw new System.Exception("unexpected control point");
      }
    }
    public AlcorProofKernel._IExpr Bind(AlcorProofKernel._IIdentifier id, AlcorProofKernel._IExpr expr, Dafny.ISet<AlcorProofKernel._IIdentifier> freeVars) {
      AlcorProofKernel._IExpr _source25 = this;
      if (_source25.is_True) {
        return this;
      } else if (_source25.is_False) {
        return this;
      } else if (_source25.is_And) {
        AlcorProofKernel._IExpr _341___mcc_h0 = _source25.dtor_left;
        AlcorProofKernel._IExpr _342___mcc_h1 = _source25.dtor_right;
        AlcorProofKernel._IExpr _343_right = _342___mcc_h1;
        AlcorProofKernel._IExpr _344_left = _341___mcc_h0;
        return AlcorProofKernel.Expr.create_And((_344_left).Bind(id, expr, (expr).FreeVars()), (_343_right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source25.is_Imp) {
        AlcorProofKernel._IExpr _345___mcc_h2 = _source25.dtor_left;
        AlcorProofKernel._IExpr _346___mcc_h3 = _source25.dtor_right;
        AlcorProofKernel._IExpr _347_right = _346___mcc_h3;
        AlcorProofKernel._IExpr _348_left = _345___mcc_h2;
        return AlcorProofKernel.Expr.create_Imp((_348_left).Bind(id, expr, (expr).FreeVars()), (_347_right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source25.is_Or) {
        AlcorProofKernel._IExpr _349___mcc_h4 = _source25.dtor_left;
        AlcorProofKernel._IExpr _350___mcc_h5 = _source25.dtor_right;
        AlcorProofKernel._IExpr _351_right = _350___mcc_h5;
        AlcorProofKernel._IExpr _352_left = _349___mcc_h4;
        return AlcorProofKernel.Expr.create_Or((_352_left).Bind(id, expr, (expr).FreeVars()), (_351_right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source25.is_Var) {
        AlcorProofKernel._IIdentifier _353___mcc_h6 = _source25.dtor_id;
        AlcorProofKernel._IIdentifier _354_i = _353___mcc_h6;
        if (object.Equals(_354_i, id)) {
          return expr;
        } else {
          return this;
        }
      } else if (_source25.is_Abs) {
        AlcorProofKernel._IIdentifier _355___mcc_h7 = _source25.dtor_id;
        AlcorProofKernel._IExpr _356___mcc_h8 = _source25.dtor_body;
        AlcorProofKernel._IExpr _357_body = _356___mcc_h8;
        AlcorProofKernel._IIdentifier _358_i = _355___mcc_h7;
        if (object.Equals(_358_i, id)) {
          return this;
        } else if ((freeVars).Contains(_358_i)) {
          AlcorProofKernel._IIdentifier _359_i_k = AlcorProofKernel.__default.FreshIdentifier(_358_i, freeVars);
          AlcorProofKernel._IExpr _360_newAbs = AlcorProofKernel.Expr.create_Abs(_359_i_k, (_357_body).Bind(_358_i, AlcorProofKernel.Expr.create_Var(_359_i_k), (AlcorProofKernel.Expr.create_Var(_359_i_k)).FreeVars()));
          return (_360_newAbs).Bind(id, expr, freeVars);
        } else {
          return AlcorProofKernel.Expr.create_Abs(_358_i, (_357_body).Bind(id, expr, freeVars));
        }
      } else if (_source25.is_App) {
        AlcorProofKernel._IExpr _361___mcc_h9 = _source25.dtor_left;
        AlcorProofKernel._IExpr _362___mcc_h10 = _source25.dtor_right;
        AlcorProofKernel._IExpr _363_right = _362___mcc_h10;
        AlcorProofKernel._IExpr _364_left = _361___mcc_h9;
        return AlcorProofKernel.Expr.create_App((_364_left).Bind(id, expr, (expr).FreeVars()), (_363_right).Bind(id, expr, (expr).FreeVars()));
      } else if (_source25.is_Forall) {
        AlcorProofKernel._IExpr _365___mcc_h11 = _source25.dtor_body;
        AlcorProofKernel._IExpr _366_body = _365___mcc_h11;
        return AlcorProofKernel.Expr.create_Forall((_366_body).Bind(id, expr, (expr).FreeVars()));
      } else {
        BigInteger _367___mcc_h12 = _source25.dtor_value;
        return this;
      }
    }
    public Dafny.ISequence<Dafny.Rune> Operator() {
      if ((this).is_And) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&");
      } else if ((this).is_Or) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||");
      } else if ((this).is_Imp) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("==>");
      } else if ((this).is_False) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false");
      } else if ((this).is_True) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true");
      } else if ((this).is_Int) {
        return Wrappers.__default.IntToString((this).dtor_value);
      } else {
        return ((this).dtor_id)._ToString();
      }
    }
    public Dafny.ISequence<Dafny.Rune> ToStringWrap(BigInteger outerPriority) {
      Dafny.ISequence<Dafny.Rune> _368_r = (this)._ToString();
      if ((outerPriority) > ((this).Priority())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _368_r), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        return _368_r;
      }
    }
    public bool InlineOperator() {
      return ((this).is_Var) && (((System.Func<AlcorProofKernel._IIdentifier, bool>)((_source26) => {
        Dafny.ISequence<Dafny.Rune> _369___mcc_h0 = _source26.dtor_name;
        BigInteger _370___mcc_h1 = _source26.dtor_version;
        Dafny.ISequence<Dafny.Rune> _371___mcc_h2 = _source26.dtor_lbl;
        return (((_370___mcc_h1).Sign == 0) ? (((object.Equals(_371___mcc_h2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_369___mcc_h0, _pat_let46_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let46_0, _372_s => ((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) ? (true) : (((object.Equals(_372_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="))) ? (true) : (false))))))))))))))))))))))))))))) : (false))) : (false));
      }))((this).dtor_id));
    }
    public BigInteger LeftPriority() {
      if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"))) {
        return new BigInteger(18);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) {
        return new BigInteger(18);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
        return new BigInteger(15);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
        return new BigInteger(13);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
        return new BigInteger(13);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) {
        return new BigInteger(11);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
        return new BigInteger(11);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
        return new BigInteger(9);
      } else {
        return new BigInteger(9);
      }
    }
    public BigInteger RightPriority() {
      if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"))) {
        return new BigInteger(18);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) {
        return new BigInteger(18);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
        return new BigInteger(15);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
        return new BigInteger(14);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
        return new BigInteger(14);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) {
        return new BigInteger(12);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
        return new BigInteger(12);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) {
        return new BigInteger(9);
      } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
        return new BigInteger(9);
      } else {
        return new BigInteger(9);
      }
    }
    public BigInteger Priority() {
      if ((((this).is_False) || ((this).is_True)) || ((this).is_Int)) {
        return new BigInteger(100);
      } else if ((this).is_Var) {
        if ((this).InlineOperator()) {
          if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"))) {
            return new BigInteger(18);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) {
            return new BigInteger(18);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            return new BigInteger(15);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
            return new BigInteger(13);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            return new BigInteger(13);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) {
            return new BigInteger(11);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
            return new BigInteger(11);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) {
            return new BigInteger(9);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
            return new BigInteger(9);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) {
            return new BigInteger(9);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) {
            return new BigInteger(9);
          } else if (object.Equals(((this).dtor_id).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
            return new BigInteger(9);
          } else {
            return new BigInteger(9);
          }
        } else {
          return new BigInteger(100);
        }
      } else if ((this).IfThenElse_q()) {
        return new BigInteger(3);
      } else if ((this).is_App) {
        return new BigInteger(99);
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
        return new BigInteger(3);
      } else {
        return BigInteger.Zero;
      }
    }
    public bool IfThenElse_q() {
      return ((((this).is_And) && (((this).dtor_left).is_Imp)) && (((this).dtor_right).is_Imp)) && (object.Equals(((this).dtor_right).dtor_left, AlcorProofKernel.Expr.Not(((this).dtor_left).dtor_left)));
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      if ((this).IfThenElse_q()) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), (((this).dtor_left).dtor_left)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" then ")), (((this).dtor_left).dtor_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" else ")), (((this).dtor_right).dtor_right)._ToString());
      } else {
        BigInteger _373_p = (this).Priority();
        if (((this).is_Imp) && (((this).dtor_right).is_False)) {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), ((this).dtor_left).ToStringWrap(_373_p));
        } else if ((((this).is_And) || ((this).is_Or)) || ((this).is_Imp)) {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_left).ToStringWrap(_373_p), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), (this).Operator()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_right).ToStringWrap(_373_p));
        } else if ((this).is_Abs) {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\\"), ((this).dtor_id)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((this).dtor_body).ToStringWrap((_373_p) + (BigInteger.One)));
        } else if ((this).is_App) {
          if ((((this).dtor_left).is_App) && ((((this).dtor_left).dtor_left).InlineOperator())) {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((((this).dtor_left).dtor_right).ToStringWrap((((this).dtor_left).dtor_left).LeftPriority()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), (((this).dtor_left).dtor_left)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_right).ToStringWrap((((this).dtor_left).dtor_left).RightPriority()));
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_left).ToStringWrap(_373_p), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), ((this).dtor_right).ToStringWrap(BigInteger.Zero)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
        } else if ((this).is_Forall) {
          if (((this).dtor_body).is_Abs) {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("forall "), (((this).dtor_body).dtor_id)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" :: ")), (((this).dtor_body).dtor_body).ToStringWrap((_373_p) + (BigInteger.One)));
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("forall "), ((this).dtor_body).ToStringWrap((_373_p) + (BigInteger.One)));
          }
        } else {
          return (this).Operator();
        }
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
      hash = ((hash << 5) + hash) + 4;
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
      hash = ((hash << 5) + hash) + 5;
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
      hash = ((hash << 5) + hash) + 6;
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
      hash = ((hash << 5) + hash) + 7;
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
      hash = ((hash << 5) + hash) + 8;
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
  public class Expr_Int : Expr {
    public readonly BigInteger _value;
    public Expr_Int(BigInteger @value) : base() {
      this._value = @value;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Int(_value);
    }
    public override bool Equals(object other) {
      var oth = other as AlcorProofKernel.Expr_Int;
      return oth != null && this._value == oth._value;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int)hash;
    }
    public override string ToString() {
      string s = "AlcorProofKernel.Expr.Int";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
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
      AlcorProofKernel._IExpr _374_p = hypothesis;
      Wrappers._IResult<AlcorProofKernel._IExpr> _375_valueOrError0 = Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>>(pHypothesis)(_374_p);
      if ((_375_valueOrError0).IsFailure()) {
        return (_375_valueOrError0).PropagateFailure<AlcorProofKernel._IExpr>();
      } else {
        AlcorProofKernel._IExpr _376_result = (_375_valueOrError0).Extract();
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success(AlcorProofKernel.Expr.create_Imp(hypothesis, (_376_result)));
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
      Alcor._IProofProgram _source27 = program;
      if (_source27.is_ProofVar) {
        Dafny.ISequence<Dafny.Rune> _377___mcc_h0 = _source27.dtor_name;
        Dafny.ISequence<Dafny.Rune> _378_name = _377___mcc_h0;
        return (environment).Lookup(_378_name);
      } else if (_source27.is_ProofExpr) {
        AlcorProofKernel._IExpr _379___mcc_h1 = _source27.dtor_expr;
        AlcorProofKernel._IExpr _380_expr = _379___mcc_h1;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneExpr(_380_expr));
      } else if (_source27.is_ProofAbs) {
        Dafny.ISequence<Dafny.Rune> _381___mcc_h2 = _source27.dtor_name;
        Alcor._IType _382___mcc_h3 = _source27.dtor_tpe;
        Alcor._IProofProgram _383___mcc_h4 = _source27.dtor_body;
        Alcor._IProofProgram _384_body = _383___mcc_h4;
        Alcor._IType _385_tpe = _382___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _386_name = _381___mcc_h2;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosure(_386_name, _385_tpe, _384_body, environment));
      } else if (_source27.is_ProofApp) {
        Alcor._IProofProgram _387___mcc_h5 = _source27.dtor_left;
        Alcor._IProofProgram _388___mcc_h6 = _source27.dtor_right;
        Alcor._IProofProgram _389_right = _388___mcc_h6;
        Alcor._IProofProgram _390_left = _387___mcc_h5;
        Wrappers._IResult<Alcor._IProofValue> _391_valueOrError0 = Alcor.__default.ExecuteProof(_390_left, environment);
        if ((_391_valueOrError0).IsFailure()) {
          return (_391_valueOrError0).PropagateFailure<Alcor._IProofValue>();
        } else {
          Alcor._IProofValue _392_result = (_391_valueOrError0).Extract();
          if ((_392_result).is_OneClosure) {
            Wrappers._IResult<Alcor._IProofValue> _393_valueOrError1 = Alcor.__default.ExecuteProof(_389_right, environment);
            if ((_393_valueOrError1).IsFailure()) {
              return (_393_valueOrError1).PropagateFailure<Alcor._IProofValue>();
            } else {
              Alcor._IProofValue _394_argument = (_393_valueOrError1).Extract();
              return Alcor.__default.ExecuteProof((_392_result).dtor_body, Alcor.ProofEnv.create_ProofEnvCons((_392_result).dtor_argName, _394_argument, (_392_result).dtor_environment));
            }
          } else if ((_392_result).is_OneClosureAxiom) {
            Wrappers._IResult<Alcor._IProofValue> _395_valueOrError2 = Alcor.__default.ExecuteProof(_389_right, environment);
            if ((_395_valueOrError2).IsFailure()) {
              return (_395_valueOrError2).PropagateFailure<Alcor._IProofValue>();
            } else {
              Alcor._IProofValue _396_argument = (_395_valueOrError2).Extract();
              if ((((_392_result).dtor_axiom).Arity()) == ((new BigInteger(((_392_result).dtor_args).Count)) + (BigInteger.One))) {
                return ((_392_result).dtor_axiom).ApplyArgs(Dafny.Sequence<Alcor._IProofValue>.Concat((_392_result).dtor_args, Dafny.Sequence<Alcor._IProofValue>.FromElements(_396_argument)), environment);
              } else {
                return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosureAxiom(Dafny.Sequence<Alcor._IProofValue>.Concat((_392_result).dtor_args, Dafny.Sequence<Alcor._IProofValue>.FromElements(_396_argument)), (_392_result).dtor_axiom));
              }
            }
          } else {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Left of application was not a closure"));
          }
        }
      } else {
        Alcor._IProofAxiom _397___mcc_h7 = _source27.dtor_axiom;
        Alcor._IProofAxiom _398_axiom = _397___mcc_h7;
        return Wrappers.Result<Alcor._IProofValue>.create_Success(Alcor.ProofValue.create_OneClosureAxiom(Dafny.Sequence<Alcor._IProofValue>.FromElements(), _398_axiom));
      }
    }
    public static Wrappers._IResult<AlcorProofKernel._IExpr> CheckProof(Alcor._IProofProgram program, Alcor._IProofEnv environment, AlcorProofKernel._IExpr expected) {
      Wrappers._IResult<Alcor._IProofValue> _399_valueOrError0 = Alcor.__default.ExecuteProof(program, environment);
      if ((_399_valueOrError0).IsFailure()) {
        return (_399_valueOrError0).PropagateFailure<AlcorProofKernel._IExpr>();
      } else {
        Alcor._IProofValue _400_result = (_399_valueOrError0).Extract();
        if (((_400_result).is_OneClosure) || ((_400_result).is_OneClosureAxiom)) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a closure proof")));
        } else if ((_400_result).is_OneExpr) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a simple expression")));
        } else if (!object.Equals(AlcorProofKernel.Proof.GetExpr((_400_result).dtor_proof), expected)) {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected a proof of "), (expected)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" but got a proof of ")), (AlcorProofKernel.Proof.GetExpr((_400_result).dtor_proof))._ToString()));
        } else {
          return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_400_result).dtor_proof);
        }
      }
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> checkGoalAgainstExpr(Alcor._IProofValue pv, AlcorProofKernel._IExpr expr, Alcor._IProofProgram pr) {
      if (!((pv).is_OneProof)) {
        return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DummyProofFinder did not generate a proof but "), (pv).Summary()));
      } else {
        AlcorProofKernel._IExpr _401_p = (pv).dtor_proof;
        if (object.Equals(AlcorProofKernel.Proof.GetExpr(_401_p), expr)) {
          return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Success(_System.Tuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>.create(_401_p, pr));
        } else {
          return Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DummyProofFinder was looking for a proof of "), (expr)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" but returned a proof of ")), (AlcorProofKernel.Proof.GetExpr(_401_p))._ToString()));
        }
      }
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> AndProofFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      if (!(((expr).dtor_left).is_And)) {
        result = Alcor.__default.CantApplyAndProofFinder;
        return result;
      }
      AlcorProofKernel._IExpr _402_goal;
      _402_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _403_env;
      _403_env = (expr).dtor_left;
      AlcorProofKernel._IExpr _404_A0;
      _404_A0 = (_403_env).dtor_left;
      AlcorProofKernel._IExpr _405_tail;
      _405_tail = (_403_env).dtor_right;
      if ((_404_A0).is_And) {
        if (object.Equals((_404_A0).dtor_left, _402_goal)) {
          Alcor._IProofProgram _406_proofProgram;
          _406_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_403_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _407_r;
          Wrappers._IResult<Alcor._IProofValue> _408_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
          _408_valueOrError0 = Alcor.__default.ExecuteProof(_406_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_408_valueOrError0).IsFailure()) {
            result = (_408_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _407_r = (_408_valueOrError0).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_407_r, expr, _406_proofProgram);
          return result;
        }
        if (object.Equals((_404_A0).dtor_right, _402_goal)) {
          Alcor._IProofProgram _409_proofProgram;
          _409_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_403_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimRight()).apply1((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _410_r;
          Wrappers._IResult<Alcor._IProofValue> _411_valueOrError1 = Wrappers.Result<Alcor._IProofValue>.Default();
          _411_valueOrError1 = Alcor.__default.ExecuteProof(_409_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_411_valueOrError1).IsFailure()) {
            result = (_411_valueOrError1).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _410_r = (_411_valueOrError1).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_410_r, expr, _409_proofProgram);
          return result;
        }
      }
      if ((_405_tail).is_And) {
        AlcorProofKernel._IExpr _412_A1;
        _412_A1 = (_405_tail).dtor_left;
        if (object.Equals(_402_goal, AlcorProofKernel.Expr.create_And(_404_A0, _412_A1))) {
          Alcor._IProofProgram _413_proofProgram;
          _413_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_403_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndIntro()).apply2((Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))))));
          Alcor._IProofValue _414_r;
          Wrappers._IResult<Alcor._IProofValue> _415_valueOrError2 = Wrappers.Result<Alcor._IProofValue>.Default();
          _415_valueOrError2 = Alcor.__default.ExecuteProof(_413_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_415_valueOrError2).IsFailure()) {
            result = (_415_valueOrError2).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _414_r = (_415_valueOrError2).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_414_r, expr, _413_proofProgram);
          return result;
        }
        if (object.Equals(_402_goal, AlcorProofKernel.Expr.create_And(_412_A1, _404_A0))) {
          Alcor._IProofProgram _416_proofProgram;
          _416_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_403_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndIntro()).apply2((Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))), (Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))));
          Alcor._IProofValue _417_r;
          Wrappers._IResult<Alcor._IProofValue> _418_valueOrError3 = Wrappers.Result<Alcor._IProofValue>.Default();
          _418_valueOrError3 = Alcor.__default.ExecuteProof(_416_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
          if ((_418_valueOrError3).IsFailure()) {
            result = (_418_valueOrError3).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _417_r = (_418_valueOrError3).Extract();
          result = Alcor.__default.checkGoalAgainstExpr(_417_r, expr, _416_proofProgram);
          return result;
        }
      }
      result = Alcor.__default.CantApplyAndProofFinder;
      return result;
      return result;
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> LookupProofFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      AlcorProofKernel._IExpr _419_goal;
      _419_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _420_env;
      _420_env = (expr).dtor_left;
      AlcorProofKernel._IExpr _421_envSearch;
      _421_envSearch = _420_env;
      BigInteger _422_i;
      _422_i = BigInteger.Zero;
      while (((_421_envSearch).is_And) && (!object.Equals((_421_envSearch).dtor_left, _419_goal))) {
        _421_envSearch = (_421_envSearch).dtor_right;
        _422_i = (_422_i) + (BigInteger.One);
      }
      if (((_421_envSearch).is_And) && (object.Equals((_421_envSearch).dtor_left, _419_goal))) {
        Alcor._IProofProgram _423_proofElem;
        _423_proofElem = Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"));
        while ((_422_i).Sign != 0) {
          _423_proofElem = Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofAxiom(Alcor.ProofAxiom.create_AndElimRight()), _423_proofElem);
          _422_i = (_422_i) - (BigInteger.One);
        }
        Alcor._IProofProgram _424_proofProgram;
        _424_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_420_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), Alcor.ProofProgram.create_ProofApp(Alcor.ProofProgram.create_ProofAxiom(Alcor.ProofAxiom.create_AndElimLeft()), _423_proofElem)));
        Alcor._IProofValue _425_r;
        Wrappers._IResult<Alcor._IProofValue> _426_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
        _426_valueOrError0 = Alcor.__default.ExecuteProof(_424_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
        if ((_426_valueOrError0).IsFailure()) {
          result = (_426_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
          return result;
        }
        _425_r = (_426_valueOrError0).Extract();
        result = Alcor.__default.checkGoalAgainstExpr(_425_r, expr, _424_proofProgram);
        return result;
      }
      result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not apply LookupProofFinder"));
      return result;
      return result;
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> ModusPonensFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      AlcorProofKernel._IExpr _427_goal;
      _427_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _428_env;
      _428_env = (expr).dtor_left;
      if (!((_428_env).is_And)) {
        result = Alcor.__default.CantApplyModusPonensFinder;
        return result;
      }
      AlcorProofKernel._IExpr _429_A0;
      _429_A0 = (_428_env).dtor_left;
      AlcorProofKernel._IExpr _430_tail;
      _430_tail = (_428_env).dtor_right;
      if (!((_430_tail).is_And)) {
        result = Alcor.__default.CantApplyModusPonensFinder;
        return result;
      }
      AlcorProofKernel._IExpr _431_A1;
      _431_A1 = (_430_tail).dtor_left;
      if ((((_429_A0).is_Imp) && (object.Equals((_429_A0).dtor_right, _427_goal))) && (object.Equals(_431_A1, (_429_A0).dtor_left))) {
        Alcor._IProofProgram _432_proofProgram;
        _432_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_428_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))), (Alcor.ProofAxiom.create_ImpElim()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB")), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A")))))));
        Alcor._IProofValue _433_r;
        Wrappers._IResult<Alcor._IProofValue> _434_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
        _434_valueOrError0 = Alcor.__default.ExecuteProof(_432_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
        if ((_434_valueOrError0).IsFailure()) {
          result = (_434_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
          return result;
        }
        _433_r = (_434_valueOrError0).Extract();
        result = Alcor.__default.checkGoalAgainstExpr(_433_r, expr, _432_proofProgram);
        return result;
      }
      if ((((_431_A1).is_Imp) && (object.Equals((_431_A1).dtor_right, _427_goal))) && (object.Equals(_429_A0, (_431_A1).dtor_left))) {
        Alcor._IProofProgram _435_proofProgram;
        _435_proofProgram = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_428_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))), Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_AndElimLeft()).apply1((Alcor.ProofAxiom.create_AndElimRight()).apply1(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env")))), (Alcor.ProofAxiom.create_ImpElim()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AtoB")), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("A")))))));
        Alcor._IProofValue _436_r;
        Wrappers._IResult<Alcor._IProofValue> _437_valueOrError1 = Wrappers.Result<Alcor._IProofValue>.Default();
        _437_valueOrError1 = Alcor.__default.ExecuteProof(_435_proofProgram, Alcor.ProofEnv.create_ProofEnvNil());
        if ((_437_valueOrError1).IsFailure()) {
          result = (_437_valueOrError1).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
          return result;
        }
        _436_r = (_437_valueOrError1).Extract();
        result = Alcor.__default.checkGoalAgainstExpr(_436_r, expr, _435_proofProgram);
        return result;
      }
      result = Alcor.__default.CantApplyModusPonensFinder;
      return result;
      return result;
    }
    public static Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> DummyProofFinder(AlcorProofKernel._IExpr expr) {
      Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.Default();
      Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>> _438_checkGoal;
      _438_checkGoal = Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>>>>((_439_expr) => ((System.Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>>)((_440_pv, _441_pr) => {
        return Alcor.__default.checkGoalAgainstExpr(_440_pv, _439_expr, _441_pr);
      })))(expr);
      if (!((expr).is_Imp)) {
        result = Wrappers.Result<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>.create_Failure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alcor requires an implication"));
        return result;
      }
      AlcorProofKernel._IExpr _442_goal;
      _442_goal = (expr).dtor_right;
      AlcorProofKernel._IExpr _443_env;
      _443_env = (expr).dtor_left;
      if ((_442_goal).is_Imp) {
        Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> _444_proofOfConclusion;
        Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>> _out0;
        _out0 = Alcor.__default.DummyProofFinder(AlcorProofKernel.Expr.create_Imp(AlcorProofKernel.Expr.create_And((_442_goal).dtor_left, _443_env), (_442_goal).dtor_right));
        _444_proofOfConclusion = _out0;
        if ((_444_proofOfConclusion).is_Success) {
          Alcor._IProofEnv _445_execEnv;
          _445_execEnv = Alcor.ProofEnv.create_ProofEnvCons(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b"), Alcor.ProofValue.create_OneProof(((_444_proofOfConclusion).dtor_value).dtor__0), Alcor.ProofEnv.create_ProofEnvNil());
          Alcor._IProofProgram _446_proofProgramInner;
          _446_proofProgramInner = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_443_env), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr((_442_goal).dtor_left), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proofOfA"), Alcor.Type.create_Ind(), (Alcor.ProofAxiom.create_ImpElim()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b")), (Alcor.ProofAxiom.create_AndIntro()).apply2(Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("proofOfA")), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("env"))))))));
          Alcor._IProofValue _447_r;
          Wrappers._IResult<Alcor._IProofValue> _448_valueOrError0 = Wrappers.Result<Alcor._IProofValue>.Default();
          _448_valueOrError0 = Alcor.__default.ExecuteProof(_446_proofProgramInner, _445_execEnv);
          if ((_448_valueOrError0).IsFailure()) {
            result = (_448_valueOrError0).PropagateFailure<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>();
            return result;
          }
          _447_r = (_448_valueOrError0).Extract();
          Alcor._IProofProgram _449_proofProgram;
          _449_proofProgram = Alcor.__default.Let(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a_x_imp_b"), Alcor.Type.create_Bool(), ((_444_proofOfConclusion).dtor_value).dtor__1, _446_proofProgramInner);
          result = Dafny.Helpers.Id<Func<Alcor._IProofValue, Alcor._IProofProgram, Wrappers._IResult<_System._ITuple2<AlcorProofKernel._IExpr, Alcor._IProofProgram>>>>(_438_checkGoal)(_447_r, _449_proofProgram);
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
      Alcor._IProofProgram _source28 = this;
      if (_source28.is_ProofVar) {
        Dafny.ISequence<Dafny.Rune> _450___mcc_h0 = _source28.dtor_name;
        Dafny.ISequence<Dafny.Rune> _451_name = _450___mcc_h0;
        return _451_name;
      } else if (_source28.is_ProofExpr) {
        AlcorProofKernel._IExpr _452___mcc_h1 = _source28.dtor_expr;
        AlcorProofKernel._IExpr _453_expr = _452___mcc_h1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("``"), (_453_expr)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("``"));
      } else if (_source28.is_ProofAbs) {
        Dafny.ISequence<Dafny.Rune> _454___mcc_h2 = _source28.dtor_name;
        Alcor._IType _455___mcc_h3 = _source28.dtor_tpe;
        Alcor._IProofProgram _456___mcc_h4 = _source28.dtor_body;
        Alcor._IProofProgram _457_body = _456___mcc_h4;
        Alcor._IType _458_tpe = _455___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _459_name = _454___mcc_h2;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\\"), _459_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". ")), (_457_body)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else if (_source28.is_ProofApp) {
        Alcor._IProofProgram _460___mcc_h5 = _source28.dtor_left;
        Alcor._IProofProgram _461___mcc_h6 = _source28.dtor_right;
        Alcor._IProofProgram _source29 = _460___mcc_h5;
        if (_source29.is_ProofVar) {
          Dafny.ISequence<Dafny.Rune> _462___mcc_h7 = _source29.dtor_name;
          Alcor._IProofProgram _463_right = _461___mcc_h6;
          Alcor._IProofProgram _464_left = _460___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_464_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_463_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else if (_source29.is_ProofExpr) {
          AlcorProofKernel._IExpr _465___mcc_h9 = _source29.dtor_expr;
          Alcor._IProofProgram _466_right = _461___mcc_h6;
          Alcor._IProofProgram _467_left = _460___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_467_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_466_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else if (_source29.is_ProofAbs) {
          Dafny.ISequence<Dafny.Rune> _468___mcc_h11 = _source29.dtor_name;
          Alcor._IType _469___mcc_h12 = _source29.dtor_tpe;
          Alcor._IProofProgram _470___mcc_h13 = _source29.dtor_body;
          Alcor._IProofProgram _471_varContent = _461___mcc_h6;
          Alcor._IProofProgram _472_body = _470___mcc_h13;
          Alcor._IType _473_tpe = _469___mcc_h12;
          Dafny.ISequence<Dafny.Rune> _474_varName = _468___mcc_h11;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("var "), _474_varName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_473_tpe)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" := ")), (_471_varContent)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), (_472_body)._ToString());
        } else if (_source29.is_ProofApp) {
          Alcor._IProofProgram _475___mcc_h17 = _source29.dtor_left;
          Alcor._IProofProgram _476___mcc_h18 = _source29.dtor_right;
          Alcor._IProofProgram _477_right = _461___mcc_h6;
          Alcor._IProofProgram _478_left = _460___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_478_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_477_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          Alcor._IProofAxiom _479___mcc_h21 = _source29.dtor_axiom;
          Alcor._IProofProgram _480_right = _461___mcc_h6;
          Alcor._IProofProgram _481_left = _460___mcc_h5;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_481_left)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_480_right)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else {
        Alcor._IProofAxiom _482___mcc_h23 = _source28.dtor_axiom;
        Alcor._IProofAxiom _483_axiom = _482___mcc_h23;
        return (_483_axiom)._ToString();
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
      Alcor._IProofAxiom _source30 = this;
      if (_source30.is_AndIntro) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndIntro");
      } else if (_source30.is_AndElimLeft) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndElimLeft");
      } else if (_source30.is_AndElimRight) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AndElimRight");
      } else if (_source30.is_ImpElim) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ImpElim");
      } else if (_source30.is_ImpIntro) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ImpIntro");
      } else if (_source30.is_ForallElim) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ForallElim");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ForallIntro");
      }
    }
    public BigInteger Arity() {
      Alcor._IProofAxiom _source31 = this;
      if (_source31.is_AndIntro) {
        return new BigInteger(2);
      } else if (_source31.is_AndElimLeft) {
        return BigInteger.One;
      } else if (_source31.is_AndElimRight) {
        return BigInteger.One;
      } else if (_source31.is_ImpElim) {
        return new BigInteger(2);
      } else if (_source31.is_ImpIntro) {
        return new BigInteger(2);
      } else if (_source31.is_ForallElim) {
        return new BigInteger(2);
      } else {
        return new BigInteger(2);
      }
    }
    public Wrappers._IResult<AlcorProofKernel._IExpr> ExtractProof(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i) {
      Alcor._IProofValue _484_arg = (args).Select(i);
      if ((_484_arg).is_OneProof) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_484_arg).dtor_proof);
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("At index "), Wrappers.__default.IntToString(i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), (this)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", expected proof, but got ")), (_484_arg).Summary()));
      }
    }
    public Wrappers._IResult<AlcorProofKernel._IExpr> ExtractExpr(Dafny.ISequence<Alcor._IProofValue> args, BigInteger i) {
      Alcor._IProofValue _485_arg = (args).Select(i);
      if ((_485_arg).is_OneExpr) {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_485_arg).dtor_expr);
      } else {
        return Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("At index "), Wrappers.__default.IntToString(i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), (this)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", expected expr, but got ")), (_485_arg).Summary()));
      }
    }
    public Wrappers._IResult<Alcor._IProofValue> ApplyArgs(Dafny.ISequence<Alcor._IProofValue> args, Alcor._IProofEnv environment) {
      Alcor._IProofAxiom _source32 = this;
      if (_source32.is_AndIntro) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _486_valueOrError0 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_486_valueOrError0).IsFailure()) {
          return (_486_valueOrError0).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _487_left = (_486_valueOrError0).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _488_valueOrError1 = (this).ExtractProof(args, BigInteger.One);
          if ((_488_valueOrError1).IsFailure()) {
            return (_488_valueOrError1).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _489_right = (_488_valueOrError1).Extract();
            return (AlcorProofKernel.Proof.AndIntro(_487_left, _489_right)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_490_p) => {
              return Alcor.ProofValue.create_OneProof(_490_p);
            })));
          }
        }
      } else if (_source32.is_AndElimLeft) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _491_valueOrError2 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_491_valueOrError2).IsFailure()) {
          return (_491_valueOrError2).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _492_elem = (_491_valueOrError2).Extract();
          return (AlcorProofKernel.Proof.AndElimLeft(_492_elem)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_493_p) => {
            return Alcor.ProofValue.create_OneProof(_493_p);
          })));
        }
      } else if (_source32.is_AndElimRight) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _494_valueOrError3 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_494_valueOrError3).IsFailure()) {
          return (_494_valueOrError3).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _495_elem = (_494_valueOrError3).Extract();
          return (AlcorProofKernel.Proof.AndElimRight(_495_elem)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_496_p) => {
            return Alcor.ProofValue.create_OneProof(_496_p);
          })));
        }
      } else if (_source32.is_ImpElim) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _497_valueOrError6 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_497_valueOrError6).IsFailure()) {
          return (_497_valueOrError6).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _498_left = (_497_valueOrError6).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _499_valueOrError7 = (this).ExtractProof(args, BigInteger.One);
          if ((_499_valueOrError7).IsFailure()) {
            return (_499_valueOrError7).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _500_right = (_499_valueOrError7).Extract();
            return (AlcorProofKernel.Proof.ImpElim(_498_left, _500_right)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_501_p) => {
              return Alcor.ProofValue.create_OneProof(_501_p);
            })));
          }
        }
      } else if (_source32.is_ImpIntro) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _502_valueOrError4 = (this).ExtractExpr(args, BigInteger.Zero);
        if ((_502_valueOrError4).IsFailure()) {
          return (_502_valueOrError4).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _503_hypothesis = (_502_valueOrError4).Extract();
          Alcor._IProofValue _504_reasoning = (args).Select(BigInteger.One);
          if (!((_504_reasoning).is_OneClosure)) {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Second argument of ImpIntro requires a closure, got "), (_504_reasoning).Summary()));
          } else {
            Dafny.ISequence<Dafny.Rune> _505_argName = (_504_reasoning).dtor_argName;
            Alcor._IProofProgram _506_body = (_504_reasoning).dtor_body;
            Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>> _507_proofBuilder = Dafny.Helpers.Id<Func<Alcor._IProofProgram, Dafny.ISequence<Dafny.Rune>, Alcor._IProofEnv, Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>>>((_508_body, _509_argName, _510_environment) => ((System.Func<AlcorProofKernel._IExpr, Wrappers._IResult<AlcorProofKernel._IExpr>>)((_511_p) => {
              return Dafny.Helpers.Let<Wrappers._IResult<Alcor._IProofValue>, Wrappers._IResult<AlcorProofKernel._IExpr>>(Alcor.__default.ExecuteProof(_508_body, Alcor.ProofEnv.create_ProofEnvCons(_509_argName, Alcor.ProofValue.create_OneProof(_511_p), _510_environment)), _pat_let47_0 => Dafny.Helpers.Let<Wrappers._IResult<Alcor._IProofValue>, Wrappers._IResult<AlcorProofKernel._IExpr>>(_pat_let47_0, _512_valueOrError5 => (((_512_valueOrError5).IsFailure()) ? ((_512_valueOrError5).PropagateFailure<AlcorProofKernel._IExpr>()) : (Dafny.Helpers.Let<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>((_512_valueOrError5).Extract(), _pat_let48_0 => Dafny.Helpers.Let<Alcor._IProofValue, Wrappers._IResult<AlcorProofKernel._IExpr>>(_pat_let48_0, _513_x => (((_513_x).is_OneProof) ? (Wrappers.Result<AlcorProofKernel._IExpr>.create_Success((_513_x).dtor_proof)) : (Wrappers.Result<AlcorProofKernel._IExpr>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Closure should return a proof, but got "), (_513_x).Summary()))))))))));
            })))(_506_body, _505_argName, environment);
            return (AlcorProofKernel.Proof.ImpIntro(_503_hypothesis, AlcorProofKernel.Expr.create_True(), _507_proofBuilder)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_514_p) => {
              return Alcor.ProofValue.create_OneProof(_514_p);
            })));
          }
        }
      } else if (_source32.is_ForallElim) {
        Wrappers._IResult<AlcorProofKernel._IExpr> _515_valueOrError10 = (this).ExtractProof(args, BigInteger.Zero);
        if ((_515_valueOrError10).IsFailure()) {
          return (_515_valueOrError10).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _516_axiom = (_515_valueOrError10).Extract();
          Wrappers._IResult<AlcorProofKernel._IExpr> _517_valueOrError11 = (this).ExtractExpr(args, BigInteger.One);
          if ((_517_valueOrError11).IsFailure()) {
            return (_517_valueOrError11).PropagateFailure<Alcor._IProofValue>();
          } else {
            AlcorProofKernel._IExpr _518_instance = (_517_valueOrError11).Extract();
            return (AlcorProofKernel.Proof.ForallElim(_516_axiom, _518_instance)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_519_p) => {
              return Alcor.ProofValue.create_OneProof(_519_p);
            })));
          }
        }
      } else {
        Wrappers._IResult<AlcorProofKernel._IExpr> _520_valueOrError8 = (this).ExtractExpr(args, BigInteger.Zero);
        if ((_520_valueOrError8).IsFailure()) {
          return (_520_valueOrError8).PropagateFailure<Alcor._IProofValue>();
        } else {
          AlcorProofKernel._IExpr _521_v = (_520_valueOrError8).Extract();
          if (!((_521_v).is_Var)) {
            return Wrappers.Result<Alcor._IProofValue>.create_Failure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ForallIntro needs a var as first argument, but got "), (_521_v)._ToString()));
          } else {
            Wrappers._IResult<AlcorProofKernel._IExpr> _522_valueOrError9 = (this).ExtractProof(args, BigInteger.One);
            if ((_522_valueOrError9).IsFailure()) {
              return (_522_valueOrError9).PropagateFailure<Alcor._IProofValue>();
            } else {
              AlcorProofKernel._IExpr _523_body = (_522_valueOrError9).Extract();
              return (AlcorProofKernel.Proof.ForallIntro(_523_body, (_521_v).dtor_id)).Map<Alcor._IProofValue>(((System.Func<AlcorProofKernel._IExpr, Alcor._IProofValue>)((_524_p) => {
                return Alcor.ProofValue.create_OneProof(_524_p);
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
      BigInteger _525___v0;
      _525___v0 = Alcor.__default.Debug(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hello"));
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
        BigInteger _526_tailIndex = ((this).dtor_tail).IndexOf(name);
        if ((_526_tailIndex) == (new BigInteger(-1))) {
          return new BigInteger(-1);
        } else {
          return (BigInteger.One) + (_526_tailIndex);
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
        Dafny.ISequence<Dafny.Rune> _527_x = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_prop)._ToString());
        if (!(((this).dtor_tail).is_EnvNil)) {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_tail)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _527_x);
        } else {
          return _527_x;
        }
      }
    }
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> FreeVars() {
      if ((this).is_EnvNil) {
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      } else {
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _528_tailFreeVars = ((this).dtor_tail).FreeVars();
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((this).dtor_id), _528_tailFreeVars);
      }
    }
    public Dafny.ISequence<Dafny.Rune> FreshVar(Dafny.ISequence<Dafny.Rune> name) {
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _529_freeVars = (this).FreeVars();
      if (!(_529_freeVars).Contains(name)) {
        return name;
      } else {
        return (this).FreshVar__helper(name, BigInteger.Zero, _529_freeVars);
      }
    }
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> FreshVar__helper2(Dafny.ISequence<Dafny.Rune> name, BigInteger num) {
      return Dafny.Helpers.Id<Func<BigInteger, Dafny.ISequence<Dafny.Rune>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_530_num, _531_name) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
        foreach (BigInteger _compr_0 in Dafny.Helpers.IntegerRange(BigInteger.Zero, _530_num)) {
          BigInteger _532_i = (BigInteger)_compr_0;
          if (((_532_i).Sign != -1) && ((_532_i) < (_530_num))) {
            _coll0.Add(Dafny.Sequence<Dafny.Rune>.Concat(_531_name, Wrappers.__default.IntToString(_532_i)));
          }
        }
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll0);
      }))())(num, name);
    }
    public Dafny.ISequence<Dafny.Rune> FreshVar__helper(Dafny.ISequence<Dafny.Rune> name, BigInteger num, Dafny.ISet<Dafny.ISequence<Dafny.Rune>> freeVars) {
      _IEnv _this = this;
    TAIL_CALL_START:;
      Dafny.ISequence<Dafny.Rune> _533_candidate = Dafny.Sequence<Dafny.Rune>.Concat(name, Wrappers.__default.IntToString(num));
      if (!(freeVars).Contains(_533_candidate)) {
        return _533_candidate;
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
      Dafny.ISet<AlcorProofKernel._IIdentifier> _534___accumulator = Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements();
      _IEnv _this = this;
    TAIL_CALL_START:;
      if ((_this).is_EnvNil) {
        return Dafny.Set<AlcorProofKernel._IIdentifier>.Union(Dafny.Set<AlcorProofKernel._IIdentifier>.FromElements(), _534___accumulator);
      } else {
        Dafny.ISet<AlcorProofKernel._IIdentifier> _535_headIds = ((_this).dtor_prop).FreeVars();
        _534___accumulator = Dafny.Set<AlcorProofKernel._IIdentifier>.Union(_534___accumulator, _535_headIds);
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
      Dafny.ISequence<Dafny.Rune> _536___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
      _ISequentList _this = this;
    TAIL_CALL_START:;
      if ((_this).is_SequentNil) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_536___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else {
        _536___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_536___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(((_this).dtor_head)._ToString(), ((((_this).dtor_tail).is_SequentNil) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n\n")))));
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
      AlcorProofKernel._IExpr _537_overallGoal;
      _537_overallGoal = AlcorProofKernel.Expr.create_And(AlcorProofKernel.Expr.create_Imp((env).ToExpr(), goal), AlcorProofKernel.Expr.create_True());
      (this).proofBuilder = (Alcor.ProofAxiom.create_ImpIntro()).apply2(Alcor.ProofProgram.create_ProofExpr(_537_overallGoal), Alcor.ProofProgram.create_ProofAbs(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("goal"), Alcor.Type.create_Ind(), Alcor.ProofProgram.create_ProofVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("goal"))));
      (this).CheckProof();
    }
    public void CheckProof() {
      AlcorProofKernel._IExpr _538_overallGoal;
      _538_overallGoal = AlcorProofKernel.Expr.create_And(AlcorProofKernel.Expr.create_Imp(((this).env).ToExpr(), (this).goal), AlcorProofKernel.Expr.create_True());
      Wrappers._IResult<Alcor._IProofValue> _539_p;
      _539_p = Alcor.__default.ExecuteProof(this.proofBuilder, Alcor.ProofEnv.create_ProofEnvNil());
      if ((_539_p).is_Failure) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[Internal error] "), (_539_p).dtor_msg));
      } else if (!(((_539_p).dtor_value).is_OneProof)) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[Internal error] Expected a proof, got a "), ((_539_p).dtor_value).Summary()));
      } else if (!object.Equals(AlcorProofKernel.Proof.GetExpr(((_539_p).dtor_value).dtor_proof), AlcorProofKernel.Expr.create_Imp((this.proofState).ToExpr(), _538_overallGoal))) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[Internal error] Expected a proof that the proof state implies the overall goal\n"), (AlcorProofKernel.Expr.create_Imp((this.proofState).ToExpr(), _538_overallGoal))._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", got a proof of\n")), (AlcorProofKernel.Proof.GetExpr(((_539_p).dtor_value).dtor_proof))._ToString()));
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
      AlcorTacticProofChecker._ISequentList _540_sequents;
      _540_sequents = (this.proofState).dtor_sequents;
      if ((_540_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out4;
        _out4 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to introduce, proof state is empty. Consider removing this"));
        feedback = _out4;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _541_sequent;
      _541_sequent = (_540_sequents).dtor_head;
      AlcorProofKernel._IIdentifier _542_id;
      _542_id = AlcorProofKernel.Identifier.create(name, BigInteger.Zero, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((((_541_sequent).dtor_goal).is_Forall) && ((((_541_sequent).dtor_goal).dtor_body).is_Abs)) {
        Dafny.ISet<AlcorProofKernel._IIdentifier> _543_freeEnvVars;
        _543_freeEnvVars = ((_541_sequent).dtor_env).FreeIdentifiers();
        AlcorProofKernel._IIdentifier _544_freeVar;
        _544_freeVar = AlcorProofKernel.__default.FreshIdentifier((((_541_sequent).dtor_goal).dtor_body).dtor_id, _543_freeEnvVars);
        var _pat_let_tv30 = _541_sequent;
        var _pat_let_tv31 = _541_sequent;
        var _pat_let_tv32 = _541_sequent;
        var _pat_let_tv33 = _544_freeVar;
        var _pat_let_tv34 = _544_freeVar;
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_540_sequents, _pat_let49_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let49_0, _545_dt__update__tmp_h0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequent>(_pat_let_tv30, _pat_let51_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequent>(_pat_let51_0, _546_dt__update__tmp_h1 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorTacticProofChecker._ISequent>(((((_pat_let_tv31).dtor_goal).dtor_body).dtor_body).Bind((((_pat_let_tv32).dtor_goal).dtor_body).dtor_id, AlcorProofKernel.Expr.create_Var(_pat_let_tv33), (AlcorProofKernel.Expr.create_Var(_pat_let_tv34)).FreeVars()), _pat_let52_0 => Dafny.Helpers.Let<AlcorProofKernel._IExpr, AlcorTacticProofChecker._ISequent>(_pat_let52_0, _547_dt__update_hgoal_h0 => AlcorTacticProofChecker.Sequent.create((_546_dt__update__tmp_h1).dtor_env, _547_dt__update_hgoal_h0))))), _pat_let50_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(_pat_let50_0, _548_dt__update_hhead_h0 => AlcorTacticProofChecker.SequentList.create_SequentCons(_548_dt__update_hhead_h0, (_545_dt__update__tmp_h0).dtor_tail))))));
      } else if (((_541_sequent).dtor_goal).is_Imp) {
        var _pat_let_tv35 = name;
        var _pat_let_tv36 = _541_sequent;
        var _pat_let_tv37 = _541_sequent;
        var _pat_let_tv38 = _541_sequent;
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_540_sequents, _pat_let53_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let53_0, _549_dt__update__tmp_h2 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(AlcorTacticProofChecker.Sequent.create(AlcorTacticProofChecker.Env.create_EnvCons(_pat_let_tv35, ((_pat_let_tv36).dtor_goal).dtor_left, (_pat_let_tv37).dtor_env), ((_pat_let_tv38).dtor_goal).dtor_right), _pat_let54_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(_pat_let54_0, _550_dt__update_hhead_h1 => AlcorTacticProofChecker.SequentList.create_SequentCons(_550_dt__update_hhead_h1, (_549_dt__update__tmp_h2).dtor_tail))))));
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
      Dafny.ISequence<Dafny.Rune> _551_oldName;
      _551_oldName = previousName;
      Dafny.ISequence<Dafny.Rune> _552_newName;
      _552_newName = suggestedName;
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _553_sequents;
      _553_sequents = (this.proofState).dtor_sequents;
      if ((_553_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out5;
        _out5 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to rename, proof state is empty. Consider removing this"));
        feedback = _out5;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _554_sequent;
      _554_sequent = (_553_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _555_env;
      _555_env = (_554_sequent).dtor_env;
      if ((_555_env).is_EnvNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out6;
        _out6 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to rename, proof state has no environment. Consider removing this"));
        feedback = _out6;
        return feedback;
      }
      if ((_552_newName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        _552_newName = _551_oldName;
        _551_oldName = (_555_env).dtor_id;
      }
      if (!((_555_env).FreeVars()).Contains(_551_oldName)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out7;
        _out7 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("No variable in the environment is named "), _551_oldName));
        feedback = _out7;
        return feedback;
      }
      AlcorTacticProofChecker._IEnv _556_newEnv;
      _556_newEnv = (_555_env).Rename(_551_oldName, _552_newName);
      var _pat_let_tv39 = _553_sequents;
      var _pat_let_tv40 = _556_newEnv;
      var _pat_let_tv41 = _554_sequent;
      (this).proofState = Dafny.Helpers.Let<AlcorTacticProofChecker._IProofState, AlcorTacticProofChecker._IProofState>(this.proofState, _pat_let55_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._IProofState, AlcorTacticProofChecker._IProofState>(_pat_let55_0, _557_dt__update__tmp_h0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._IProofState>(Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let_tv39, _pat_let57_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._ISequentList>(_pat_let57_0, _558_dt__update__tmp_h1 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(AlcorTacticProofChecker.Sequent.create(_pat_let_tv40, (_pat_let_tv41).dtor_goal), _pat_let58_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequent, AlcorTacticProofChecker._ISequentList>(_pat_let58_0, _559_dt__update_hhead_h0 => AlcorTacticProofChecker.SequentList.create_SequentCons(_559_dt__update_hhead_h0, (_558_dt__update__tmp_h1).dtor_tail))))), _pat_let56_0 => Dafny.Helpers.Let<AlcorTacticProofChecker._ISequentList, AlcorTacticProofChecker._IProofState>(_pat_let56_0, _560_dt__update_hsequents_h0 => AlcorTacticProofChecker.ProofState.create_Sequents(_560_dt__update_hsequents_h0)))));
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
      AlcorTacticProofChecker._ISequentList _561_sequents;
      _561_sequents = (this.proofState).dtor_sequents;
      if ((_561_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out8;
        _out8 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a case split on"));
        feedback = _out8;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _562_sequent;
      _562_sequent = (_561_sequents).dtor_head;
      if (!(((_562_sequent).dtor_goal).is_And)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out9;
        _out9 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot perform a case split on something other than &&"));
        feedback = _out9;
        return feedback;
      }
      AlcorTacticProofChecker._IEnv _563_env;
      _563_env = (_562_sequent).dtor_env;
      AlcorTacticProofChecker._ISequentList _564_newSequents;
      _564_newSequents = AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_563_env, ((_562_sequent).dtor_goal).dtor_left), AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_563_env, AlcorProofKernel.Expr.create_Imp(((_562_sequent).dtor_goal).dtor_left, ((_562_sequent).dtor_goal).dtor_right)), (_561_sequents).dtor_tail));
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(_564_newSequents);
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
      AlcorTacticProofChecker._ISequentList _565_sequents;
      _565_sequents = (this.proofState).dtor_sequents;
      if ((_565_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out10;
        _out10 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a case split on"));
        feedback = _out10;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _566_sequent;
      _566_sequent = (_565_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _567_env;
      _567_env = (_566_sequent).dtor_env;
      BigInteger _568_i;
      _568_i = (_567_env).IndexOf(name);
      if ((_568_i).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out11;
        _out11 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out11;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs0 = (_567_env).ElemAt(_568_i);
      Dafny.ISequence<Dafny.Rune> _569_envIdentifier = _let_tmp_rhs0.dtor__0;
      AlcorProofKernel._IExpr _570_envElem = _let_tmp_rhs0.dtor__1;
      if (!((_570_envElem).is_And)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out12;
        _out12 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not splittable")));
        feedback = _out12;
        return feedback;
      }
      AlcorTacticProofChecker._IEnv _571_newEnv;
      _571_newEnv = (_567_env).ReplaceTailAt(_568_i, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, AlcorTacticProofChecker._IEnv, BigInteger, Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>>>((_572_right, _573_left, _574_env, _575_i) => ((System.Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>)((_576_previousEnv) => {
        return AlcorTacticProofChecker.Env.create_EnvCons(_572_right, ((_576_previousEnv).dtor_prop).dtor_right, AlcorTacticProofChecker.Env.create_EnvCons(_573_left, ((_576_previousEnv).dtor_prop).dtor_left, (_576_previousEnv).dtor_tail));
      })))(right, left, _567_env, _568_i));
      AlcorTacticProofChecker._ISequentList _577_newSequents;
      _577_newSequents = AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_571_newEnv, (_566_sequent).dtor_goal), (_565_sequents).dtor_tail);
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(_577_newSequents);
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
      AlcorTacticProofChecker._ISequentList _578_sequents;
      _578_sequents = (this.proofState).dtor_sequents;
      if ((_578_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out13;
        _out13 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a ImpElim on"));
        feedback = _out13;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _579_sequent;
      _579_sequent = (_578_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _580_env;
      _580_env = (_579_sequent).dtor_env;
      AlcorProofKernel._IExpr _581_goal;
      _581_goal = (_579_sequent).dtor_goal;
      BigInteger _582_iImp;
      _582_iImp = (_580_env).IndexOf(imp);
      if ((_582_iImp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out14;
        _out14 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), imp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out14;
        return feedback;
      }
      BigInteger _583_iHyp;
      _583_iHyp = (_580_env).IndexOf(hypothesis);
      if ((_583_iHyp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out15;
        _out15 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), hypothesis), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out15;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs1 = (_580_env).ElemAt(_582_iImp);
      Dafny.ISequence<Dafny.Rune> _584___v8 = _let_tmp_rhs1.dtor__0;
      AlcorProofKernel._IExpr _585_impExpr = _let_tmp_rhs1.dtor__1;
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs2 = (_580_env).ElemAt(_583_iHyp);
      Dafny.ISequence<Dafny.Rune> _586___v9 = _let_tmp_rhs2.dtor__0;
      AlcorProofKernel._IExpr _587_hypExpr = _let_tmp_rhs2.dtor__1;
      if (!((_585_impExpr).is_Imp)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out16;
        _out16 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), imp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not an implication")));
        feedback = _out16;
        return feedback;
      }
      if (!object.Equals((_585_impExpr).dtor_left, _587_hypExpr)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out17;
        _out17 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), imp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" cannot be applied to ")), hypothesis));
        feedback = _out17;
        return feedback;
      }
      if (object.Equals((_585_impExpr).dtor_right, _581_goal)) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents((_578_sequents).dtor_tail);
      } else {
        Dafny.ISequence<Dafny.Rune> _588_newName;
        _588_newName = (((newName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("h")) : (newName));
        Dafny.ISequence<Dafny.Rune> _589_freeVar;
        _589_freeVar = ((_579_sequent).dtor_env).FreshVar(_588_newName);
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(AlcorTacticProofChecker.Env.create_EnvCons(_589_freeVar, (_585_impExpr).dtor_right, _580_env), _581_goal), (_578_sequents).dtor_tail));
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
      AlcorTacticProofChecker._ISequentList _590_sequents;
      _590_sequents = (this.proofState).dtor_sequents;
      if ((_590_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out18;
        _out18 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a ImpElim on"));
        feedback = _out18;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _591_sequent;
      _591_sequent = (_590_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _592_env;
      _592_env = (_591_sequent).dtor_env;
      AlcorProofKernel._IExpr _593_goal;
      _593_goal = (_591_sequent).dtor_goal;
      BigInteger _594_iHyp;
      _594_iHyp = (_592_env).IndexOf(name);
      if ((_594_iHyp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out19;
        _out19 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out19;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs3 = (_592_env).ElemAt(_594_iHyp);
      Dafny.ISequence<Dafny.Rune> _595___v10 = _let_tmp_rhs3.dtor__0;
      AlcorProofKernel._IExpr _596_hypExpr = _let_tmp_rhs3.dtor__1;
      if (object.Equals(_596_hypExpr, _593_goal)) {
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents((_590_sequents).dtor_tail);
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
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> ForallElim(Dafny.ISequence<Dafny.Rune> name, AlcorProofKernel._IExpr expr, Dafny.ISequence<Dafny.Rune> newName) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _597_sequents;
      _597_sequents = (this.proofState).dtor_sequents;
      if ((_597_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out21;
        _out21 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to perform a ForallElim on"));
        feedback = _out21;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _598_sequent;
      _598_sequent = (_597_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _599_env;
      _599_env = (_598_sequent).dtor_env;
      AlcorProofKernel._IExpr _600_goal;
      _600_goal = (_598_sequent).dtor_goal;
      BigInteger _601_iHyp;
      _601_iHyp = (_599_env).IndexOf(name);
      if ((_601_iHyp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out22;
        _out22 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out22;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs4 = (_599_env).ElemAt(_601_iHyp);
      Dafny.ISequence<Dafny.Rune> _602___v11 = _let_tmp_rhs4.dtor__0;
      AlcorProofKernel._IExpr _603_hypExpr = _let_tmp_rhs4.dtor__1;
      if (!((_603_hypExpr).is_Forall)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out23;
        _out23 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a forall")));
        feedback = _out23;
        return feedback;
      }
      AlcorProofKernel._IExpr _604_abs;
      _604_abs = (_603_hypExpr).dtor_body;
      if (!((_604_abs).is_Abs)) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out24;
        _out24 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a forall with a variable, named predicates not supported yet")));
        feedback = _out24;
        return feedback;
      }
      AlcorProofKernel._IExpr _605_instantiated;
      _605_instantiated = ((_604_abs).dtor_body).Bind((_604_abs).dtor_id, expr, (expr).FreeVars());
      Dafny.ISequence<Dafny.Rune> _606_newName;
      _606_newName = (((newName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("h")) : (newName));
      Dafny.ISequence<Dafny.Rune> _607_freeVar;
      _607_freeVar = ((_598_sequent).dtor_env).FreshVar(_606_newName);
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(AlcorTacticProofChecker.Env.create_EnvCons(_606_newName, _605_instantiated, _599_env), _600_goal), (_597_sequents).dtor_tail));
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out25;
      _out25 = (this).Simplify(_606_newName, BigInteger.Zero);
      feedback = _out25;
      return feedback;
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> Simplify(Dafny.ISequence<Dafny.Rune> name, BigInteger replaceDepth) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _608_sequents;
      _608_sequents = (this.proofState).dtor_sequents;
      if ((_608_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out26;
        _out26 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to simplify"));
        feedback = _out26;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _609_sequent;
      _609_sequent = (_608_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _610_env;
      _610_env = (_609_sequent).dtor_env;
      AlcorProofKernel._IExpr _611_goal;
      _611_goal = (_609_sequent).dtor_goal;
      if (!(name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        BigInteger _612_iHyp;
        _612_iHyp = (_610_env).IndexOf(name);
        if ((_612_iHyp).Sign == -1) {
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out27;
          _out27 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
          feedback = _out27;
          return feedback;
        }
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs5 = (_610_env).ElemAt(_612_iHyp);
        Dafny.ISequence<Dafny.Rune> _613___v12 = _let_tmp_rhs5.dtor__0;
        AlcorProofKernel._IExpr _614_hypExpr = _let_tmp_rhs5.dtor__1;
        AlcorProofKernel._ISimplificationConfig _615_config;
        _615_config = AlcorProofKernel.SimplificationConfig.create(false, BigInteger.One);
        AlcorProofKernel._IExpr _616_newHypExpr;
        _616_newHypExpr = (_614_hypExpr).simplify(((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_617_x) => {
          return _617_x;
        })), _615_config);
        AlcorTacticProofChecker._IEnv _618_newEnv;
        _618_newEnv = (_610_env).ReplaceTailAt(_612_iHyp, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr, AlcorTacticProofChecker._IEnv, BigInteger, Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>>>((_619_name, _620_newHypExpr, _621_env, _622_iHyp) => ((System.Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>)((_623_oldTail) => {
          return AlcorTacticProofChecker.Env.create_EnvCons(_619_name, _620_newHypExpr, (_623_oldTail).dtor_tail);
        })))(name, _616_newHypExpr, _610_env, _612_iHyp));
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_618_newEnv, _611_goal), (_608_sequents).dtor_tail));
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
        return feedback;
      } else {
        AlcorProofKernel._ISimplificationConfig _624_config;
        _624_config = AlcorProofKernel.SimplificationConfig.create(false, BigInteger.One);
        AlcorProofKernel._IExpr _625_newGoal;
        _625_newGoal = (_611_goal).simplify(((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_626_x) => {
          return _626_x;
        })), _624_config);
        (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_610_env, _625_newGoal), (_608_sequents).dtor_tail));
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Success((this.proofState)._ToString());
        return feedback;
      }
      return feedback;
    }
    public Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> Definition(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> nameDefinition) {
      Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.Default();
      if ((this.proofState).is_Error) {
        feedback = Wrappers.Result<Dafny.ISequence<Dafny.Rune>>.create_Failure((this.proofState).dtor_message);
        return feedback;
      }
      AlcorTacticProofChecker._ISequentList _627_sequents;
      _627_sequents = (this.proofState).dtor_sequents;
      if ((_627_sequents).is_SequentNil) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out28;
        _out28 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Nothing to simplify"));
        feedback = _out28;
        return feedback;
      }
      AlcorTacticProofChecker._ISequent _628_sequent;
      _628_sequent = (_627_sequents).dtor_head;
      AlcorTacticProofChecker._IEnv _629_env;
      _629_env = (_628_sequent).dtor_env;
      AlcorProofKernel._IExpr _630_goal;
      _630_goal = (_628_sequent).dtor_goal;
      BigInteger _631_iHyp;
      _631_iHyp = (_629_env).IndexOf(name);
      if ((_631_iHyp).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out29;
        _out29 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out29;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs6 = (_629_env).ElemAt(_631_iHyp);
      Dafny.ISequence<Dafny.Rune> _632___v13 = _let_tmp_rhs6.dtor__0;
      AlcorProofKernel._IExpr _633_hypExpr = _let_tmp_rhs6.dtor__1;
      BigInteger _634_iDef;
      _634_iDef = (_629_env).IndexOf(nameDefinition);
      if ((_634_iDef).Sign == -1) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out30;
        _out30 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" not found in the environment")));
        feedback = _out30;
        return feedback;
      }
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr> _let_tmp_rhs7 = (_629_env).ElemAt(_634_iDef);
      Dafny.ISequence<Dafny.Rune> _635___v14 = _let_tmp_rhs7.dtor__0;
      AlcorProofKernel._IExpr _636_defExpr = _let_tmp_rhs7.dtor__1;
      AlcorProofKernel._IExpr _637_left = AlcorProofKernel.Expr.Default();
      AlcorProofKernel._IExpr _638_right = AlcorProofKernel.Expr.Default();
      AlcorProofKernel._IExpr _source33 = _636_defExpr;
      if (_source33.is_True) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out31;
        _out31 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out31;
        return feedback;
      } else if (_source33.is_False) {
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out32;
        _out32 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out32;
        return feedback;
      } else if (_source33.is_And) {
        AlcorProofKernel._IExpr _639___mcc_h0 = _source33.dtor_left;
        AlcorProofKernel._IExpr _640___mcc_h1 = _source33.dtor_right;
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out33;
        _out33 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out33;
        return feedback;
      } else if (_source33.is_Imp) {
        AlcorProofKernel._IExpr _641___mcc_h4 = _source33.dtor_left;
        AlcorProofKernel._IExpr _642___mcc_h5 = _source33.dtor_right;
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out34;
        _out34 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out34;
        return feedback;
      } else if (_source33.is_Or) {
        AlcorProofKernel._IExpr _643___mcc_h8 = _source33.dtor_left;
        AlcorProofKernel._IExpr _644___mcc_h9 = _source33.dtor_right;
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out35;
        _out35 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out35;
        return feedback;
      } else if (_source33.is_Var) {
        AlcorProofKernel._IIdentifier _645___mcc_h12 = _source33.dtor_id;
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out36;
        _out36 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out36;
        return feedback;
      } else if (_source33.is_Abs) {
        AlcorProofKernel._IIdentifier _646___mcc_h14 = _source33.dtor_id;
        AlcorProofKernel._IExpr _647___mcc_h15 = _source33.dtor_body;
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out37;
        _out37 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out37;
        return feedback;
      } else if (_source33.is_App) {
        AlcorProofKernel._IExpr _648___mcc_h18 = _source33.dtor_left;
        AlcorProofKernel._IExpr _649___mcc_h19 = _source33.dtor_right;
        AlcorProofKernel._IExpr _source34 = _648___mcc_h18;
        if (_source34.is_True) {
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out38;
          _out38 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out38;
          return feedback;
        } else if (_source34.is_False) {
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out39;
          _out39 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out39;
          return feedback;
        } else if (_source34.is_And) {
          AlcorProofKernel._IExpr _650___mcc_h22 = _source34.dtor_left;
          AlcorProofKernel._IExpr _651___mcc_h23 = _source34.dtor_right;
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out40;
          _out40 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out40;
          return feedback;
        } else if (_source34.is_Imp) {
          AlcorProofKernel._IExpr _652___mcc_h26 = _source34.dtor_left;
          AlcorProofKernel._IExpr _653___mcc_h27 = _source34.dtor_right;
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out41;
          _out41 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out41;
          return feedback;
        } else if (_source34.is_Or) {
          AlcorProofKernel._IExpr _654___mcc_h30 = _source34.dtor_left;
          AlcorProofKernel._IExpr _655___mcc_h31 = _source34.dtor_right;
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out42;
          _out42 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out42;
          return feedback;
        } else if (_source34.is_Var) {
          AlcorProofKernel._IIdentifier _656___mcc_h34 = _source34.dtor_id;
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out43;
          _out43 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out43;
          return feedback;
        } else if (_source34.is_Abs) {
          AlcorProofKernel._IIdentifier _657___mcc_h36 = _source34.dtor_id;
          AlcorProofKernel._IExpr _658___mcc_h37 = _source34.dtor_body;
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out44;
          _out44 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out44;
          return feedback;
        } else if (_source34.is_App) {
          AlcorProofKernel._IExpr _659___mcc_h40 = _source34.dtor_left;
          AlcorProofKernel._IExpr _660___mcc_h41 = _source34.dtor_right;
          AlcorProofKernel._IExpr _source35 = _659___mcc_h40;
          if (_source35.is_True) {
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out45;
            _out45 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out45;
            return feedback;
          } else if (_source35.is_False) {
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out46;
            _out46 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out46;
            return feedback;
          } else if (_source35.is_And) {
            AlcorProofKernel._IExpr _661___mcc_h44 = _source35.dtor_left;
            AlcorProofKernel._IExpr _662___mcc_h45 = _source35.dtor_right;
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out47;
            _out47 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out47;
            return feedback;
          } else if (_source35.is_Imp) {
            AlcorProofKernel._IExpr _663___mcc_h48 = _source35.dtor_left;
            AlcorProofKernel._IExpr _664___mcc_h49 = _source35.dtor_right;
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out48;
            _out48 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out48;
            return feedback;
          } else if (_source35.is_Or) {
            AlcorProofKernel._IExpr _665___mcc_h52 = _source35.dtor_left;
            AlcorProofKernel._IExpr _666___mcc_h53 = _source35.dtor_right;
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out49;
            _out49 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out49;
            return feedback;
          } else if (_source35.is_Var) {
            AlcorProofKernel._IIdentifier _667___mcc_h56 = _source35.dtor_id;
            AlcorProofKernel._IIdentifier _source36 = _667___mcc_h56;
            Dafny.ISequence<Dafny.Rune> _668___mcc_h58 = _source36.dtor_name;
            BigInteger _669___mcc_h59 = _source36.dtor_version;
            Dafny.ISequence<Dafny.Rune> _670___mcc_h60 = _source36.dtor_lbl;
            if (object.Equals(_668___mcc_h58, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
              if ((_669___mcc_h59).Sign == 0) {
                if (object.Equals(_670___mcc_h60, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                  AlcorProofKernel._IExpr _671_r = _649___mcc_h19;
                  AlcorProofKernel._IExpr _672_l = _660___mcc_h41;
                  AlcorProofKernel._IExpr _rhs0 = _672_l;
                  AlcorProofKernel._IExpr _rhs1 = _671_r;
                  _637_left = _rhs0;
                  _638_right = _rhs1;
                } else {
                  Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out50;
                  _out50 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
                  feedback = _out50;
                  return feedback;
                }
              } else {
                Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out51;
                _out51 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
                feedback = _out51;
                return feedback;
              }
            } else {
              Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out52;
              _out52 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
              feedback = _out52;
              return feedback;
            }
          } else if (_source35.is_Abs) {
            AlcorProofKernel._IIdentifier _673___mcc_h64 = _source35.dtor_id;
            AlcorProofKernel._IExpr _674___mcc_h65 = _source35.dtor_body;
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out53;
            _out53 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out53;
            return feedback;
          } else if (_source35.is_App) {
            AlcorProofKernel._IExpr _675___mcc_h68 = _source35.dtor_left;
            AlcorProofKernel._IExpr _676___mcc_h69 = _source35.dtor_right;
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out54;
            _out54 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out54;
            return feedback;
          } else if (_source35.is_Forall) {
            AlcorProofKernel._IExpr _677___mcc_h72 = _source35.dtor_body;
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out55;
            _out55 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out55;
            return feedback;
          } else {
            BigInteger _678___mcc_h74 = _source35.dtor_value;
            Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out56;
            _out56 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
            feedback = _out56;
            return feedback;
          }
        } else if (_source34.is_Forall) {
          AlcorProofKernel._IExpr _679___mcc_h76 = _source34.dtor_body;
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out57;
          _out57 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out57;
          return feedback;
        } else {
          BigInteger _680___mcc_h78 = _source34.dtor_value;
          Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out58;
          _out58 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
          feedback = _out58;
          return feedback;
        }
      } else if (_source33.is_Forall) {
        AlcorProofKernel._IExpr _681___mcc_h80 = _source33.dtor_body;
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out59;
        _out59 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out59;
        return feedback;
      } else {
        BigInteger _682___mcc_h82 = _source33.dtor_value;
        Wrappers._IResult<Dafny.ISequence<Dafny.Rune>> _out60;
        _out60 = (this).SetFailure(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Entry "), nameDefinition), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not a definition like x == y")));
        feedback = _out60;
        return feedback;
      }
      AlcorProofKernel._ISimplificationConfig _683_config;
      _683_config = AlcorProofKernel.SimplificationConfig.create(true, BigInteger.One);
      AlcorProofKernel._IExpr _684_newHypExpr;
      _684_newHypExpr = (_633_hypExpr).simplify(Dafny.Helpers.Id<Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr, Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>>>((_685_left, _686_right) => ((System.Func<AlcorProofKernel._IExpr, AlcorProofKernel._IExpr>)((_687_x) => {
        return ((object.Equals(_687_x, _685_left)) ? (_686_right) : (_687_x));
      })))(_637_left, _638_right), _683_config);
      AlcorTacticProofChecker._IEnv _688_newEnv;
      _688_newEnv = (_629_env).ReplaceTailAt(_631_iHyp, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, AlcorProofKernel._IExpr, AlcorTacticProofChecker._IEnv, BigInteger, Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>>>((_689_name, _690_newHypExpr, _691_env, _692_iHyp) => ((System.Func<AlcorTacticProofChecker._IEnv, AlcorTacticProofChecker._IEnv>)((_693_oldTail) => {
        return AlcorTacticProofChecker.Env.create_EnvCons(_689_name, _690_newHypExpr, (_693_oldTail).dtor_tail);
      })))(name, _684_newHypExpr, _629_env, _631_iHyp));
      (this).proofState = AlcorTacticProofChecker.ProofState.create_Sequents(AlcorTacticProofChecker.SequentList.create_SequentCons(AlcorTacticProofChecker.Sequent.create(_688_newEnv, _630_goal), (_627_sequents).dtor_tail));
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
      Microsoft.Dafny.IToken _694_token;
      _694_token = firstToken;
      System.Text.StringBuilder _695_sb;
      System.Text.StringBuilder _nw0 = new System.Text.StringBuilder();
      _695_sb = _nw0;
      while ((_694_token) != (object)((Microsoft.Dafny.IToken)null)) {
        System.String _696_newLeadingTrivia;
        _696_newLeadingTrivia = (reindent).GetNewLeadingTrivia(_694_token);
        System.String _697_newTrailingTrivia;
        _697_newTrailingTrivia = (reindent).GetNewTrailingTrivia(_694_token);
        (_695_sb).Append(_696_newLeadingTrivia);
        (_695_sb).Append(_694_token.val);
        (_695_sb).Append(_697_newTrailingTrivia);
        _694_token = _694_token.Next;
      }
      System.String _out61;
      _out61 = (_695_sb).ToString().ToString();
      s = _out61;
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



