// Dafny program the_program compiled into JavaScript
let _System = (function() {
  let $module = {};

  $module.nat = class nat {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  return $module;
})(); // end of module _System
let Std_Wrappers = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Wrappers._default";
    }
    _parentTraits() {
      return [];
    }
    static Need(condition, error) {
      if (condition) {
        return Std_Wrappers.OutcomeResult.create_Pass_k();
      } else {
        return Std_Wrappers.OutcomeResult.create_Fail_k(error);
      }
    };
  };

  $module.Option = class Option {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_None() {
      let $dt = new Option(0);
      return $dt;
    }
    static create_Some(value) {
      let $dt = new Option(1);
      $dt.value = value;
      return $dt;
    }
    get is_None() { return this.$tag === 0; }
    get is_Some() { return this.$tag === 1; }
    get dtor_value() { return this.value; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.Option.None";
      } else if (this.$tag === 1) {
        return "Wrappers.Option.Some" + "(" + _dafny.toString(this.value) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.value, other.value);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_Wrappers.Option.create_None();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Option.Default();
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_None;
    };
    PropagateFailure() {
      let _this = this;
      return Std_Wrappers.Option.create_None();
    };
    Extract() {
      let _this = this;
      return (_this).dtor_value;
    };
    GetOr(_$$_default) {
      let _this = this;
      let _source0 = _this;
      if (_source0.is_None) {
        return _$$_default;
      } else {
        let _0___mcc_h0 = (_source0).value;
        let _1_v = _0___mcc_h0;
        return _1_v;
      }
    };
    ToResult(error) {
      let _this = this;
      let _source1 = _this;
      if (_source1.is_None) {
        return Std_Wrappers.Result.create_Failure(error);
      } else {
        let _2___mcc_h0 = (_source1).value;
        let _3_v = _2___mcc_h0;
        return Std_Wrappers.Result.create_Success(_3_v);
      }
    };
    ToOutcome(error) {
      let _this = this;
      let _source2 = _this;
      if (_source2.is_None) {
        return Std_Wrappers.Outcome.create_Fail(error);
      } else {
        let _4___mcc_h0 = (_source2).value;
        let _5_v = _4___mcc_h0;
        return Std_Wrappers.Outcome.create_Pass();
      }
    };
    Map(rewrap) {
      let _this = this;
      return (rewrap)(_this);
    };
  }

  $module.Result = class Result {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Success(value) {
      let $dt = new Result(0);
      $dt.value = value;
      return $dt;
    }
    static create_Failure(error) {
      let $dt = new Result(1);
      $dt.error = error;
      return $dt;
    }
    get is_Success() { return this.$tag === 0; }
    get is_Failure() { return this.$tag === 1; }
    get dtor_value() { return this.value; }
    get dtor_error() { return this.error; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.Result.Success" + "(" + _dafny.toString(this.value) + ")";
      } else if (this.$tag === 1) {
        return "Wrappers.Result.Failure" + "(" + _dafny.toString(this.error) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.value, other.value);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.error, other.error);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_R) {
      return Std_Wrappers.Result.create_Success(_default_R);
    }
    static Rtd(rtd$_R) {
      return class {
        static get Default() {
          return Result.Default(rtd$_R.Default);
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_Failure;
    };
    PropagateFailure() {
      let _this = this;
      return Std_Wrappers.Result.create_Failure((_this).dtor_error);
    };
    Extract() {
      let _this = this;
      return (_this).dtor_value;
    };
    GetOr(_$$_default) {
      let _this = this;
      let _source3 = _this;
      if (_source3.is_Success) {
        let _6___mcc_h0 = (_source3).value;
        let _7_s = _6___mcc_h0;
        return _7_s;
      } else {
        let _8___mcc_h1 = (_source3).error;
        let _9_e = _8___mcc_h1;
        return _$$_default;
      }
    };
    ToOption() {
      let _this = this;
      let _source4 = _this;
      if (_source4.is_Success) {
        let _10___mcc_h0 = (_source4).value;
        let _11_s = _10___mcc_h0;
        return Std_Wrappers.Option.create_Some(_11_s);
      } else {
        let _12___mcc_h1 = (_source4).error;
        let _13_e = _12___mcc_h1;
        return Std_Wrappers.Option.create_None();
      }
    };
    ToOutcome() {
      let _this = this;
      let _source5 = _this;
      if (_source5.is_Success) {
        let _14___mcc_h0 = (_source5).value;
        let _15_s = _14___mcc_h0;
        return Std_Wrappers.Outcome.create_Pass();
      } else {
        let _16___mcc_h1 = (_source5).error;
        let _17_e = _16___mcc_h1;
        return Std_Wrappers.Outcome.create_Fail(_17_e);
      }
    };
    Map(rewrap) {
      let _this = this;
      return (rewrap)(_this);
    };
    MapFailure(reWrap) {
      let _this = this;
      let _source6 = _this;
      if (_source6.is_Success) {
        let _18___mcc_h0 = (_source6).value;
        let _19_s = _18___mcc_h0;
        return Std_Wrappers.Result.create_Success(_19_s);
      } else {
        let _20___mcc_h1 = (_source6).error;
        let _21_e = _20___mcc_h1;
        return Std_Wrappers.Result.create_Failure((reWrap)(_21_e));
      }
    };
  }

  $module.Outcome = class Outcome {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Pass() {
      let $dt = new Outcome(0);
      return $dt;
    }
    static create_Fail(error) {
      let $dt = new Outcome(1);
      $dt.error = error;
      return $dt;
    }
    get is_Pass() { return this.$tag === 0; }
    get is_Fail() { return this.$tag === 1; }
    get dtor_error() { return this.error; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.Outcome.Pass";
      } else if (this.$tag === 1) {
        return "Wrappers.Outcome.Fail" + "(" + _dafny.toString(this.error) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.error, other.error);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_Wrappers.Outcome.create_Pass();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Outcome.Default();
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_Fail;
    };
    PropagateFailure() {
      let _this = this;
      return _this;
    };
    ToOption(r) {
      let _this = this;
      let _source7 = _this;
      if (_source7.is_Pass) {
        return Std_Wrappers.Option.create_Some(r);
      } else {
        let _22___mcc_h0 = (_source7).error;
        let _23_e = _22___mcc_h0;
        return Std_Wrappers.Option.create_None();
      }
    };
    ToResult(r) {
      let _this = this;
      let _source8 = _this;
      if (_source8.is_Pass) {
        return Std_Wrappers.Result.create_Success(r);
      } else {
        let _24___mcc_h0 = (_source8).error;
        let _25_e = _24___mcc_h0;
        return Std_Wrappers.Result.create_Failure(_25_e);
      }
    };
    Map(rewrap) {
      let _this = this;
      return (rewrap)(_this);
    };
    MapFailure(rewrap, _$$_default) {
      let _this = this;
      let _source9 = _this;
      if (_source9.is_Pass) {
        return Std_Wrappers.Result.create_Success(_$$_default);
      } else {
        let _26___mcc_h0 = (_source9).error;
        let _27_e = _26___mcc_h0;
        return Std_Wrappers.Result.create_Failure((rewrap)(_27_e));
      }
    };
    static Need(condition, error) {
      if (condition) {
        return Std_Wrappers.Outcome.create_Pass();
      } else {
        return Std_Wrappers.Outcome.create_Fail(error);
      }
    };
  }

  $module.OutcomeResult = class OutcomeResult {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Pass_k() {
      let $dt = new OutcomeResult(0);
      return $dt;
    }
    static create_Fail_k(error) {
      let $dt = new OutcomeResult(1);
      $dt.error = error;
      return $dt;
    }
    get is_Pass_k() { return this.$tag === 0; }
    get is_Fail_k() { return this.$tag === 1; }
    get dtor_error() { return this.error; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.OutcomeResult.Pass'";
      } else if (this.$tag === 1) {
        return "Wrappers.OutcomeResult.Fail'" + "(" + _dafny.toString(this.error) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.error, other.error);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_Wrappers.OutcomeResult.create_Pass_k();
    }
    static Rtd() {
      return class {
        static get Default() {
          return OutcomeResult.Default();
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_Fail_k;
    };
    PropagateFailure() {
      let _this = this;
      return Std_Wrappers.Result.create_Failure((_this).dtor_error);
    };
  }
  return $module;
})(); // end of module Std_Wrappers
(function() {
  let $module = Std_Concurrent;


  $module.MutableMap = class MutableMap {
    constructor () {
      this._tname = "Std.InternalGenerateJavaScriptConcurrent.MutableMap";
      this.internal = _dafny.Map.Empty;
    }
    _parentTraits() {
      return [];
    }
    __ctor(inv) {
      let _this = this;
      (_this).internal = _dafny.Map.Empty.slice();
      return;
    }
    Keys() {
      let _this = this;
      let keys = _dafny.Set.Empty;
      keys = (_this.internal).Keys;
      return keys;
    }
    HasKey(k) {
      let _this = this;
      let used = false;
      used = ((_this.internal).Keys).contains(k);
      return used;
    }
    Values() {
      let _this = this;
      let values = _dafny.Set.Empty;
      values = (_this.internal).Values;
      return values;
    }
    Items() {
      let _this = this;
      let items = _dafny.Set.Empty;
      items = (_this.internal).Items;
      return items;
    }
    Get(k) {
      let _this = this;
      let r = Std_Wrappers.Option.Default();
      r = ((((_this.internal).Keys).contains(k)) ? (Std_Wrappers.Option.create_Some((_this.internal).get(k))) : (Std_Wrappers.Option.create_None()));
      return r;
    }
    Put(k, v) {
      let _this = this;
      (_this).internal = (_this.internal).update(k, v);
      return;
    }
    Remove(k) {
      let _this = this;
      (_this).internal = (_this.internal).Subtract(_dafny.Set.fromElements(k));
      return;
    }
    Size() {
      let _this = this;
      let c = _dafny.ZERO;
      c = new BigNumber((_this.internal).length);
      return c;
    }
  };

  $module.AtomicBox = class AtomicBox {
    constructor () {
      this._tname = "Std.InternalGenerateJavaScriptConcurrent.AtomicBox";
      this.boxed = undefined;
    }
    _parentTraits() {
      return [];
    }
    __ctor(inv, t) {
      let _this = this;
      (_this).boxed = t;
      return;
    }
    Get() {
      let _this = this;
      let t = undefined;
      t = _this.boxed;
      return t;
    }
    Put(t) {
      let _this = this;
      (_this).boxed = t;
      return;
    }
  };

  $module.Lock = class Lock {
    constructor () {
      this._tname = "Std.InternalGenerateJavaScriptConcurrent.Lock";
    }
    _parentTraits() {
      return [];
    }
    __ctor() {
      let _this = this;
      return;
    }
    __Lock() {
      let _this = this;
      return;
    }
    Unlock() {
      let _this = this;
      return;
    }
  };
  return $module;
})(); // end of module Std_Concurrent
(function() {
  let $module = Std_FileIOInternalExterns;

  return $module;
})(); // end of module Std_FileIOInternalExterns
let Std_BoundedInts = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.BoundedInts._default";
    }
    _parentTraits() {
      return [];
    }
    static get TWO__TO__THE__8() {
      return new BigNumber(256);
    };
    static get UINT8__MAX() {
      return 255;
    };
    static get TWO__TO__THE__16() {
      return new BigNumber(65536);
    };
    static get UINT16__MAX() {
      return 65535;
    };
    static get TWO__TO__THE__32() {
      return new BigNumber(4294967296);
    };
    static get UINT32__MAX() {
      return 4294967295;
    };
    static get TWO__TO__THE__64() {
      return new BigNumber("18446744073709551616");
    };
    static get UINT64__MAX() {
      return new BigNumber("18446744073709551615");
    };
    static get TWO__TO__THE__7() {
      return new BigNumber(128);
    };
    static get INT8__MIN() {
      return -128;
    };
    static get INT8__MAX() {
      return 127;
    };
    static get TWO__TO__THE__15() {
      return new BigNumber(32768);
    };
    static get INT16__MIN() {
      return -32768;
    };
    static get INT16__MAX() {
      return 32767;
    };
    static get TWO__TO__THE__31() {
      return new BigNumber(2147483648);
    };
    static get INT32__MIN() {
      return -2147483648;
    };
    static get INT32__MAX() {
      return 2147483647;
    };
    static get TWO__TO__THE__63() {
      return new BigNumber("9223372036854775808");
    };
    static get INT64__MIN() {
      return new BigNumber("-9223372036854775808");
    };
    static get INT64__MAX() {
      return new BigNumber("9223372036854775807");
    };
    static get NAT8__MAX() {
      return 127;
    };
    static get NAT16__MAX() {
      return 32767;
    };
    static get NAT32__MAX() {
      return 2147483647;
    };
    static get NAT64__MAX() {
      return new BigNumber("9223372036854775807");
    };
    static get TWO__TO__THE__128() {
      return new BigNumber("340282366920938463463374607431768211456");
    };
    static get TWO__TO__THE__127() {
      return new BigNumber("170141183460469231731687303715884105728");
    };
    static get TWO__TO__THE__0() {
      return _dafny.ONE;
    };
    static get TWO__TO__THE__1() {
      return new BigNumber(2);
    };
    static get TWO__TO__THE__2() {
      return new BigNumber(4);
    };
    static get TWO__TO__THE__4() {
      return new BigNumber(16);
    };
    static get TWO__TO__THE__5() {
      return new BigNumber(32);
    };
    static get TWO__TO__THE__24() {
      return new BigNumber(16777216);
    };
    static get TWO__TO__THE__40() {
      return new BigNumber(1099511627776);
    };
    static get TWO__TO__THE__48() {
      return new BigNumber(281474976710656);
    };
    static get TWO__TO__THE__56() {
      return new BigNumber("72057594037927936");
    };
    static get TWO__TO__THE__256() {
      return new BigNumber("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    };
    static get TWO__TO__THE__512() {
      return new BigNumber("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096");
    };
  };

  $module.uint8 = class uint8 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.uint16 = class uint16 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.uint32 = class uint32 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.uint64 = class uint64 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.uint128 = class uint128 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.int8 = class int8 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.int16 = class int16 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.int32 = class int32 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.int64 = class int64 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.int128 = class int128 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.nat8 = class nat8 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.nat16 = class nat16 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.nat32 = class nat32 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.nat64 = class nat64 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.nat128 = class nat128 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.opt__byte = class opt__byte {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };
  return $module;
})(); // end of module Std_BoundedInts
let Std_Base64 = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Base64._default";
    }
    _parentTraits() {
      return [];
    }
    static IsBase64Char(c) {
      return ((((_dafny.areEqual(c, new _dafny.CodePoint('+'.codePointAt(0)))) || (_dafny.areEqual(c, new _dafny.CodePoint('/'.codePointAt(0))))) || (((new _dafny.CodePoint('0'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('9'.codePointAt(0)))))) || (((new _dafny.CodePoint('A'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('Z'.codePointAt(0)))))) || (((new _dafny.CodePoint('a'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('z'.codePointAt(0)))));
    };
    static IsUnpaddedBase64String(s) {
      return (((new BigNumber((s).length)).mod(new BigNumber(4))).isEqualTo(_dafny.ZERO)) && (_dafny.Quantifier((s).UniqueElements, true, function (_forall_var_0) {
        let _28_k = _forall_var_0;
        return !(_dafny.Seq.contains(s, _28_k)) || (Std_Base64.__default.IsBase64Char(_28_k));
      }));
    };
    static IndexToChar(i) {
      if ((i).isEqualTo(new BigNumber(63))) {
        return new _dafny.CodePoint('/'.codePointAt(0));
      } else if ((i).isEqualTo(new BigNumber(62))) {
        return new _dafny.CodePoint('+'.codePointAt(0));
      } else if (((new BigNumber(52)).isLessThanOrEqualTo(i)) && ((i).isLessThanOrEqualTo(new BigNumber(61)))) {
        return new _dafny.CodePoint((((i).minus(new BigNumber(4))).mod(new BigNumber(2).exponentiatedBy(6))).toNumber());
      } else if (((new BigNumber(26)).isLessThanOrEqualTo(i)) && ((i).isLessThanOrEqualTo(new BigNumber(51)))) {
        return _dafny.UnicodePlusChar(new _dafny.CodePoint((i).toNumber()), new _dafny.CodePoint((new BigNumber(71)).toNumber()));
      } else {
        return _dafny.UnicodePlusChar(new _dafny.CodePoint((i).toNumber()), new _dafny.CodePoint((new BigNumber(65)).toNumber()));
      }
    };
    static CharToIndex(c) {
      if (_dafny.areEqual(c, new _dafny.CodePoint('/'.codePointAt(0)))) {
        return new BigNumber(63);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('+'.codePointAt(0)))) {
        return new BigNumber(62);
      } else if (((new _dafny.CodePoint('0'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('9'.codePointAt(0))))) {
        return new BigNumber((_dafny.UnicodePlusChar(c, new _dafny.CodePoint((new BigNumber(4)).toNumber()))).value);
      } else if (((new _dafny.CodePoint('a'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('z'.codePointAt(0))))) {
        return new BigNumber((_dafny.UnicodeMinusChar(c, new _dafny.CodePoint((new BigNumber(71)).toNumber()))).value);
      } else {
        return new BigNumber((_dafny.UnicodeMinusChar(c, new _dafny.CodePoint((new BigNumber(65)).toNumber()))).value);
      }
    };
    static BV24ToSeq(x) {
      let _29_b0 = _dafny.BitwiseAnd((_dafny.ShiftRight(x, (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), new BigNumber(255));
      let _30_b1 = _dafny.BitwiseAnd((_dafny.ShiftRight(x, (new BigNumber(8)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), new BigNumber(255));
      let _31_b2 = _dafny.BitwiseAnd(x, new BigNumber(255));
      return _dafny.Seq.of(_29_b0, _30_b1, _31_b2);
    };
    static SeqToBV24(x) {
      return _dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft((x)[_dafny.ZERO], (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft((x)[_dafny.ONE], (new BigNumber(8)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (x)[new BigNumber(2)]);
    };
    static BV24ToIndexSeq(x) {
      let _32_b0 = _dafny.BitwiseAnd((_dafny.ShiftRight(x, (new BigNumber(18)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), new BigNumber(63));
      let _33_b1 = _dafny.BitwiseAnd((_dafny.ShiftRight(x, (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), new BigNumber(63));
      let _34_b2 = _dafny.BitwiseAnd((_dafny.ShiftRight(x, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), new BigNumber(63));
      let _35_b3 = _dafny.BitwiseAnd(x, new BigNumber(63));
      return _dafny.Seq.of(_32_b0, _33_b1, _34_b2, _35_b3);
    };
    static IndexSeqToBV24(x) {
      return _dafny.BitwiseOr(_dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft((x)[_dafny.ZERO], (new BigNumber(18)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft((x)[_dafny.ONE], (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_dafny.ShiftLeft((x)[new BigNumber(2)], (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (x)[new BigNumber(3)]);
    };
    static DecodeBlock(s) {
      return Std_Base64.__default.BV24ToSeq(Std_Base64.__default.IndexSeqToBV24(s));
    };
    static EncodeBlock(s) {
      return Std_Base64.__default.BV24ToIndexSeq(Std_Base64.__default.SeqToBV24(s));
    };
    static DecodeRecursively(s) {
      let b = _dafny.Seq.of();
      let _36_resultLength;
      _36_resultLength = (_dafny.EuclideanDivision(new BigNumber((s).length), new BigNumber(4))).multipliedBy(new BigNumber(3));
      let _37_result;
      let _init0 = function (_38_i) {
        return _dafny.ZERO;
      };
      let _nw0 = Array((_36_resultLength).toNumber());
      for (let _i0_0 = 0; _i0_0 < new BigNumber(_nw0.length); _i0_0++) {
        _nw0[_i0_0] = _init0(new BigNumber(_i0_0));
      }
      _37_result = _nw0;
      let _39_i;
      _39_i = new BigNumber((s).length);
      let _40_j;
      _40_j = _36_resultLength;
      while ((_dafny.ZERO).isLessThan(_39_i)) {
        _39_i = (_39_i).minus(new BigNumber(4));
        _40_j = (_40_j).minus(new BigNumber(3));
        let _41_block;
        _41_block = Std_Base64.__default.DecodeBlock((s).slice(_39_i, (_39_i).plus(new BigNumber(4))));
        (_37_result)[(_40_j)] = (_41_block)[_dafny.ZERO];
        let _index0 = (_40_j).plus(_dafny.ONE);
        (_37_result)[_index0] = (_41_block)[_dafny.ONE];
        let _index1 = (_40_j).plus(new BigNumber(2));
        (_37_result)[_index1] = (_41_block)[new BigNumber(2)];
      }
      b = _dafny.Seq.of(...(_37_result).slice());
      return b;
    }
    static EncodeRecursively(b) {
      let s = _dafny.Seq.of();
      let _42_resultLength;
      _42_resultLength = (_dafny.EuclideanDivision(new BigNumber((b).length), new BigNumber(3))).multipliedBy(new BigNumber(4));
      let _43_result;
      let _init1 = function (_44_i) {
        return _dafny.ZERO;
      };
      let _nw1 = Array((_42_resultLength).toNumber());
      for (let _i0_1 = 0; _i0_1 < new BigNumber(_nw1.length); _i0_1++) {
        _nw1[_i0_1] = _init1(new BigNumber(_i0_1));
      }
      _43_result = _nw1;
      let _45_i;
      _45_i = new BigNumber((b).length);
      let _46_j;
      _46_j = _42_resultLength;
      while ((_dafny.ZERO).isLessThan(_45_i)) {
        _45_i = (_45_i).minus(new BigNumber(3));
        _46_j = (_46_j).minus(new BigNumber(4));
        let _47_block;
        _47_block = Std_Base64.__default.EncodeBlock((b).slice(_45_i, (_45_i).plus(new BigNumber(3))));
        (_43_result)[(_46_j)] = (_47_block)[_dafny.ZERO];
        let _index2 = (_46_j).plus(_dafny.ONE);
        (_43_result)[_index2] = (_47_block)[_dafny.ONE];
        let _index3 = (_46_j).plus(new BigNumber(2));
        (_43_result)[_index3] = (_47_block)[new BigNumber(2)];
        let _index4 = (_46_j).plus(new BigNumber(3));
        (_43_result)[_index4] = (_47_block)[new BigNumber(3)];
      }
      s = _dafny.Seq.of(...(_43_result).slice());
      return s;
    }
    static FromCharsToIndices(s) {
      return _dafny.Seq.Create(new BigNumber((s).length), ((_48_s) => function (_49_i) {
        return Std_Base64.__default.CharToIndex((_48_s)[_49_i]);
      })(s));
    };
    static FromIndicesToChars(b) {
      return _dafny.Seq.Create(new BigNumber((b).length), ((_50_b) => function (_51_i) {
        return Std_Base64.__default.IndexToChar((_50_b)[_51_i]);
      })(b));
    };
    static DecodeUnpadded(s) {
      return Std_Base64.__default.DecodeRecursively(Std_Base64.__default.FromCharsToIndices(s));
    };
    static EncodeUnpadded(b) {
      return Std_Base64.__default.FromIndicesToChars(Std_Base64.__default.EncodeRecursively(b));
    };
    static Is1Padding(s) {
      return ((((((new BigNumber((s).length)).isEqualTo(new BigNumber(4))) && (Std_Base64.__default.IsBase64Char((s)[_dafny.ZERO]))) && (Std_Base64.__default.IsBase64Char((s)[_dafny.ONE]))) && (Std_Base64.__default.IsBase64Char((s)[new BigNumber(2)]))) && ((_dafny.BitwiseAnd(Std_Base64.__default.CharToIndex((s)[new BigNumber(2)]), new BigNumber(3))).isEqualTo(_dafny.ZERO))) && (_dafny.areEqual((s)[new BigNumber(3)], new _dafny.CodePoint('='.codePointAt(0))));
    };
    static Decode1Padding(s) {
      let _52_d = Std_Base64.__default.DecodeBlock(_dafny.Seq.of(Std_Base64.__default.CharToIndex((s)[_dafny.ZERO]), Std_Base64.__default.CharToIndex((s)[_dafny.ONE]), Std_Base64.__default.CharToIndex((s)[new BigNumber(2)]), _dafny.ZERO));
      return _dafny.Seq.of((_52_d)[_dafny.ZERO], (_52_d)[_dafny.ONE]);
    };
    static Encode1Padding(b) {
      let _53_e = Std_Base64.__default.EncodeBlock(_dafny.Seq.of((b)[_dafny.ZERO], (b)[_dafny.ONE], _dafny.ZERO));
      return _dafny.Seq.of(Std_Base64.__default.IndexToChar((_53_e)[_dafny.ZERO]), Std_Base64.__default.IndexToChar((_53_e)[_dafny.ONE]), Std_Base64.__default.IndexToChar((_53_e)[new BigNumber(2)]), new _dafny.CodePoint('='.codePointAt(0)));
    };
    static Is2Padding(s) {
      return ((((((new BigNumber((s).length)).isEqualTo(new BigNumber(4))) && (Std_Base64.__default.IsBase64Char((s)[_dafny.ZERO]))) && (Std_Base64.__default.IsBase64Char((s)[_dafny.ONE]))) && (((Std_Base64.__default.CharToIndex((s)[_dafny.ONE])).mod(new BigNumber(16))).isEqualTo(_dafny.ZERO))) && (_dafny.areEqual((s)[new BigNumber(2)], new _dafny.CodePoint('='.codePointAt(0))))) && (_dafny.areEqual((s)[new BigNumber(3)], new _dafny.CodePoint('='.codePointAt(0))));
    };
    static Decode2Padding(s) {
      let _54_d = Std_Base64.__default.DecodeBlock(_dafny.Seq.of(Std_Base64.__default.CharToIndex((s)[_dafny.ZERO]), Std_Base64.__default.CharToIndex((s)[_dafny.ONE]), _dafny.ZERO, _dafny.ZERO));
      return _dafny.Seq.of((_54_d)[_dafny.ZERO]);
    };
    static Encode2Padding(b) {
      let _55_e = Std_Base64.__default.EncodeBlock(_dafny.Seq.of((b)[_dafny.ZERO], _dafny.ZERO, _dafny.ZERO));
      return _dafny.Seq.of(Std_Base64.__default.IndexToChar((_55_e)[_dafny.ZERO]), Std_Base64.__default.IndexToChar((_55_e)[_dafny.ONE]), new _dafny.CodePoint('='.codePointAt(0)), new _dafny.CodePoint('='.codePointAt(0)));
    };
    static IsBase64String(s) {
      let _56_finalBlockStart = (new BigNumber((s).length)).minus(new BigNumber(4));
      return (((new BigNumber((s).length)).mod(new BigNumber(4))).isEqualTo(_dafny.ZERO)) && ((Std_Base64.__default.IsUnpaddedBase64String(s)) || ((Std_Base64.__default.IsUnpaddedBase64String((s).slice(0, _56_finalBlockStart))) && ((Std_Base64.__default.Is1Padding((s).slice(_56_finalBlockStart))) || (Std_Base64.__default.Is2Padding((s).slice(_56_finalBlockStart))))));
    };
    static DecodeValid(s) {
      if (_dafny.areEqual(s, _dafny.Seq.of())) {
        return _dafny.Seq.of();
      } else {
        let _57_finalBlockStart = (new BigNumber((s).length)).minus(new BigNumber(4));
        let _58_prefix = (s).slice(0, _57_finalBlockStart);
        let _59_suffix = (s).slice(_57_finalBlockStart);
        if (Std_Base64.__default.Is1Padding(_59_suffix)) {
          return _dafny.Seq.Concat(Std_Base64.__default.DecodeUnpadded(_58_prefix), Std_Base64.__default.Decode1Padding(_59_suffix));
        } else if (Std_Base64.__default.Is2Padding(_59_suffix)) {
          return _dafny.Seq.Concat(Std_Base64.__default.DecodeUnpadded(_58_prefix), Std_Base64.__default.Decode2Padding(_59_suffix));
        } else {
          return Std_Base64.__default.DecodeUnpadded(s);
        }
      }
    };
    static DecodeBV(s) {
      if (Std_Base64.__default.IsBase64String(s)) {
        return Std_Wrappers.Result.create_Success(Std_Base64.__default.DecodeValid(s));
      } else {
        return Std_Wrappers.Result.create_Failure(_dafny.Seq.UnicodeFromString("The encoding is malformed"));
      }
    };
    static EncodeBV(b) {
      if (((new BigNumber((b).length)).mod(new BigNumber(3))).isEqualTo(_dafny.ZERO)) {
        return Std_Base64.__default.EncodeUnpadded(b);
      } else if (((new BigNumber((b).length)).mod(new BigNumber(3))).isEqualTo(_dafny.ONE)) {
        let _60_s1 = Std_Base64.__default.EncodeUnpadded((b).slice(0, (new BigNumber((b).length)).minus(_dafny.ONE)));
        let _61_s2 = Std_Base64.__default.Encode2Padding((b).slice((new BigNumber((b).length)).minus(_dafny.ONE)));
        return _dafny.Seq.Concat(_60_s1, _61_s2);
      } else {
        let _62_s1 = Std_Base64.__default.EncodeUnpadded((b).slice(0, (new BigNumber((b).length)).minus(new BigNumber(2))));
        let _63_s2 = Std_Base64.__default.Encode1Padding((b).slice((new BigNumber((b).length)).minus(new BigNumber(2))));
        return _dafny.Seq.Concat(_62_s1, _63_s2);
      }
    };
    static UInt8sToBVs(u) {
      return _dafny.Seq.Create(new BigNumber((u).length), ((_64_u) => function (_65_i) {
        return new BigNumber((_64_u)[_65_i]);
      })(u));
    };
    static BVsToUInt8s(b) {
      return _dafny.Seq.Create(new BigNumber((b).length), ((_66_b) => function (_67_i) {
        return ((_66_b)[_67_i]).toNumber();
      })(b));
    };
    static Encode(u) {
      return Std_Base64.__default.EncodeBV(Std_Base64.__default.UInt8sToBVs(u));
    };
    static Decode(s) {
      if (Std_Base64.__default.IsBase64String(s)) {
        let _68_b = Std_Base64.__default.DecodeValid(s);
        return Std_Wrappers.Result.create_Success(Std_Base64.__default.BVsToUInt8s(_68_b));
      } else {
        return Std_Wrappers.Result.create_Failure(_dafny.Seq.UnicodeFromString("The encoding is malformed"));
      }
    };
  };
  return $module;
})(); // end of module Std_Base64
let Std_Relations = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Relations
let Std_Math = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Math._default";
    }
    _parentTraits() {
      return [];
    }
    static Min(a, b) {
      if ((a).isLessThan(b)) {
        return a;
      } else {
        return b;
      }
    };
    static Min3(a, b, c) {
      return Std_Math.__default.Min(a, Std_Math.__default.Min(b, c));
    };
    static Max(a, b) {
      if ((a).isLessThan(b)) {
        return b;
      } else {
        return a;
      }
    };
    static Max3(a, b, c) {
      return Std_Math.__default.Max(a, Std_Math.__default.Max(b, c));
    };
    static Abs(a) {
      if ((a).isLessThan(_dafny.ZERO)) {
        return (_dafny.ZERO).minus(a);
      } else {
        return a;
      }
    };
  };
  return $module;
})(); // end of module Std_Math
let Std_Collections_Seq = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Collections.Seq._default";
    }
    _parentTraits() {
      return [];
    }
    static First(xs) {
      return (xs)[_dafny.ZERO];
    };
    static DropFirst(xs) {
      return (xs).slice(_dafny.ONE);
    };
    static Last(xs) {
      return (xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)];
    };
    static DropLast(xs) {
      return (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
    };
    static ToArray(xs) {
      let a = [];
      let _init2 = ((_69_xs) => function (_70_i) {
        return (_69_xs)[_70_i];
      })(xs);
      let _nw2 = Array((new BigNumber((xs).length)).toNumber());
      for (let _i0_2 = 0; _i0_2 < new BigNumber(_nw2.length); _i0_2++) {
        _nw2[_i0_2] = _init2(new BigNumber(_i0_2));
      }
      a = _nw2;
      return a;
    }
    static ToSet(xs) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of (xs).Elements) {
          let _71_x = _compr_0;
          if (_dafny.Seq.contains(xs, _71_x)) {
            _coll0.add(_71_x);
          }
        }
        return _coll0;
      }();
    };
    static IndexOf(xs, v) {
      let _72___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual((xs)[_dafny.ZERO], v)) {
          return (_dafny.ZERO).plus(_72___accumulator);
        } else {
          _72___accumulator = (_72___accumulator).plus(_dafny.ONE);
          let _in0 = (xs).slice(_dafny.ONE);
          let _in1 = v;
          xs = _in0;
          v = _in1;
          continue TAIL_CALL_START;
        }
      }
    };
    static IndexOfOption(xs, v) {
      return Std_Collections_Seq.__default.IndexByOption(xs, ((_73_v) => function (_74_x) {
        return _dafny.areEqual(_74_x, _73_v);
      })(v));
    };
    static IndexByOption(xs, p) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return Std_Wrappers.Option.create_None();
      } else if ((p)((xs)[_dafny.ZERO])) {
        return Std_Wrappers.Option.create_Some(_dafny.ZERO);
      } else {
        let _75_o_k = Std_Collections_Seq.__default.IndexByOption((xs).slice(_dafny.ONE), p);
        if ((_75_o_k).is_Some) {
          return Std_Wrappers.Option.create_Some(((_75_o_k).dtor_value).plus(_dafny.ONE));
        } else {
          return Std_Wrappers.Option.create_None();
        }
      }
    };
    static LastIndexOf(xs, v) {
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)], v)) {
          return (new BigNumber((xs).length)).minus(_dafny.ONE);
        } else {
          let _in2 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in3 = v;
          xs = _in2;
          v = _in3;
          continue TAIL_CALL_START;
        }
      }
    };
    static LastIndexOfOption(xs, v) {
      return Std_Collections_Seq.__default.LastIndexByOption(xs, ((_76_v) => function (_77_x) {
        return _dafny.areEqual(_77_x, _76_v);
      })(v));
    };
    static LastIndexByOption(xs, p) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return Std_Wrappers.Option.create_None();
        } else if ((p)((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)])) {
          return Std_Wrappers.Option.create_Some((new BigNumber((xs).length)).minus(_dafny.ONE));
        } else {
          let _in4 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in5 = p;
          xs = _in4;
          p = _in5;
          continue TAIL_CALL_START;
        }
      }
    };
    static Remove(xs, pos) {
      return _dafny.Seq.Concat((xs).slice(0, pos), (xs).slice((pos).plus(_dafny.ONE)));
    };
    static RemoveValue(xs, v) {
      if (!_dafny.Seq.contains(xs, v)) {
        return xs;
      } else {
        let _78_i = Std_Collections_Seq.__default.IndexOf(xs, v);
        return _dafny.Seq.Concat((xs).slice(0, _78_i), (xs).slice((_78_i).plus(_dafny.ONE)));
      }
    };
    static Insert(xs, a, pos) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat((xs).slice(0, pos), _dafny.Seq.of(a)), (xs).slice(pos));
    };
    static Reverse(xs) {
      let _79___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(xs, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_79___accumulator, _dafny.Seq.of());
        } else {
          _79___accumulator = _dafny.Seq.Concat(_79___accumulator, _dafny.Seq.of((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)]));
          let _in6 = (xs).slice(_dafny.ZERO, (new BigNumber((xs).length)).minus(_dafny.ONE));
          xs = _in6;
          continue TAIL_CALL_START;
        }
      }
    };
    static Repeat(v, length) {
      let _80___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((length).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_80___accumulator, _dafny.Seq.of());
        } else {
          _80___accumulator = _dafny.Seq.Concat(_80___accumulator, _dafny.Seq.of(v));
          let _in7 = v;
          let _in8 = (length).minus(_dafny.ONE);
          v = _in7;
          length = _in8;
          continue TAIL_CALL_START;
        }
      }
    };
    static Unzip(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.Seq.of());
      } else {
        let _let_tmp_rhs0 = Std_Collections_Seq.__default.Unzip(Std_Collections_Seq.__default.DropLast(xs));
        let _81_a = (_let_tmp_rhs0)[0];
        let _82_b = (_let_tmp_rhs0)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_81_a, _dafny.Seq.of((Std_Collections_Seq.__default.Last(xs))[0])), _dafny.Seq.Concat(_82_b, _dafny.Seq.of((Std_Collections_Seq.__default.Last(xs))[1])));
      }
    };
    static Zip(xs, ys) {
      let _83___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _83___accumulator);
        } else {
          _83___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(_dafny.Tuple.of(Std_Collections_Seq.__default.Last(xs), Std_Collections_Seq.__default.Last(ys))), _83___accumulator);
          let _in9 = Std_Collections_Seq.__default.DropLast(xs);
          let _in10 = Std_Collections_Seq.__default.DropLast(ys);
          xs = _in9;
          ys = _in10;
          continue TAIL_CALL_START;
        }
      }
    };
    static Max(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ONE)) {
        return (xs)[_dafny.ZERO];
      } else {
        return Std_Math.__default.Max((xs)[_dafny.ZERO], Std_Collections_Seq.__default.Max((xs).slice(_dafny.ONE)));
      }
    };
    static Min(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ONE)) {
        return (xs)[_dafny.ZERO];
      } else {
        return Std_Math.__default.Min((xs)[_dafny.ZERO], Std_Collections_Seq.__default.Min((xs).slice(_dafny.ONE)));
      }
    };
    static Flatten(xs) {
      let _84___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_84___accumulator, _dafny.Seq.of());
        } else {
          _84___accumulator = _dafny.Seq.Concat(_84___accumulator, (xs)[_dafny.ZERO]);
          let _in11 = (xs).slice(_dafny.ONE);
          xs = _in11;
          continue TAIL_CALL_START;
        }
      }
    };
    static FlattenReverse(xs) {
      let _85___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _85___accumulator);
        } else {
          _85___accumulator = _dafny.Seq.Concat(Std_Collections_Seq.__default.Last(xs), _85___accumulator);
          let _in12 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in12;
          continue TAIL_CALL_START;
        }
      }
    };
    static Join(seqs, separator) {
      let _86___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((seqs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_86___accumulator, _dafny.Seq.of());
        } else if ((new BigNumber((seqs).length)).isEqualTo(_dafny.ONE)) {
          return _dafny.Seq.Concat(_86___accumulator, (seqs)[_dafny.ZERO]);
        } else {
          _86___accumulator = _dafny.Seq.Concat(_86___accumulator, _dafny.Seq.Concat((seqs)[_dafny.ZERO], separator));
          let _in13 = (seqs).slice(_dafny.ONE);
          let _in14 = separator;
          seqs = _in13;
          separator = _in14;
          continue TAIL_CALL_START;
        }
      }
    };
    static Split(s, delim) {
      let _87___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _88_i = Std_Collections_Seq.__default.IndexOfOption(s, delim);
        if ((_88_i).is_Some) {
          _87___accumulator = _dafny.Seq.Concat(_87___accumulator, _dafny.Seq.of((s).slice(0, (_88_i).dtor_value)));
          let _in15 = (s).slice(((_88_i).dtor_value).plus(_dafny.ONE));
          let _in16 = delim;
          s = _in15;
          delim = _in16;
          continue TAIL_CALL_START;
        } else {
          return _dafny.Seq.Concat(_87___accumulator, _dafny.Seq.of(s));
        }
      }
    };
    static SplitOnce(s, delim) {
      let _89_i = Std_Collections_Seq.__default.IndexOfOption(s, delim);
      return _dafny.Tuple.of((s).slice(0, (_89_i).dtor_value), (s).slice(((_89_i).dtor_value).plus(_dafny.ONE)));
    };
    static SplitOnceOption(s, delim) {
      let _90_valueOrError0 = Std_Collections_Seq.__default.IndexOfOption(s, delim);
      if ((_90_valueOrError0).IsFailure()) {
        return (_90_valueOrError0).PropagateFailure();
      } else {
        let _91_i = (_90_valueOrError0).Extract();
        return Std_Wrappers.Option.create_Some(_dafny.Tuple.of((s).slice(0, _91_i), (s).slice((_91_i).plus(_dafny.ONE))));
      }
    };
    static Map(f, xs) {
      let _92___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_92___accumulator, _dafny.Seq.of());
        } else {
          _92___accumulator = _dafny.Seq.Concat(_92___accumulator, _dafny.Seq.of((f)((xs)[_dafny.ZERO])));
          let _in17 = f;
          let _in18 = (xs).slice(_dafny.ONE);
          f = _in17;
          xs = _in18;
          continue TAIL_CALL_START;
        }
      }
    };
    static MapWithResult(f, xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return Std_Wrappers.Result.create_Success(_dafny.Seq.of());
      } else {
        let _93_valueOrError0 = (f)((xs)[_dafny.ZERO]);
        if ((_93_valueOrError0).IsFailure()) {
          return (_93_valueOrError0).PropagateFailure();
        } else {
          let _94_head = (_93_valueOrError0).Extract();
          let _95_valueOrError1 = Std_Collections_Seq.__default.MapWithResult(f, (xs).slice(_dafny.ONE));
          if ((_95_valueOrError1).IsFailure()) {
            return (_95_valueOrError1).PropagateFailure();
          } else {
            let _96_tail = (_95_valueOrError1).Extract();
            return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.of(_94_head), _96_tail));
          }
        }
      }
    };
    static Filter(f, xs) {
      let _97___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_97___accumulator, _dafny.Seq.of());
        } else {
          _97___accumulator = _dafny.Seq.Concat(_97___accumulator, (((f)((xs)[_dafny.ZERO])) ? (_dafny.Seq.of((xs)[_dafny.ZERO])) : (_dafny.Seq.of())));
          let _in19 = f;
          let _in20 = (xs).slice(_dafny.ONE);
          f = _in19;
          xs = _in20;
          continue TAIL_CALL_START;
        }
      }
    };
    static FoldLeft(f, init, xs) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return init;
        } else {
          let _in21 = f;
          let _in22 = (f)(init, (xs)[_dafny.ZERO]);
          let _in23 = (xs).slice(_dafny.ONE);
          f = _in21;
          init = _in22;
          xs = _in23;
          continue TAIL_CALL_START;
        }
      }
    };
    static FoldRight(f, xs, init) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return init;
      } else {
        return (f)((xs)[_dafny.ZERO], Std_Collections_Seq.__default.FoldRight(f, (xs).slice(_dafny.ONE), init));
      }
    };
    static SetToSeq(s) {
      let xs = _dafny.Seq.of();
      xs = _dafny.Seq.of();
      let _98_left;
      _98_left = s;
      while (!(_98_left).equals(_dafny.Set.fromElements())) {
        let _99_x;
        L_ASSIGN_SUCH_THAT_0: {
          for (const _assign_such_that_0 of (_98_left).Elements) {
            _99_x = _assign_such_that_0;
            if ((_98_left).contains(_99_x)) {
              break L_ASSIGN_SUCH_THAT_0;
            }
          }
          throw new Error("assign-such-that search produced no value (line 7231)");
        }
        _98_left = (_98_left).Difference(_dafny.Set.fromElements(_99_x));
        xs = _dafny.Seq.Concat(xs, _dafny.Seq.of(_99_x));
      }
      return xs;
    }
    static SetToSortedSeq(s, R) {
      let xs = _dafny.Seq.of();
      let _out0;
      _out0 = Std_Collections_Seq.__default.SetToSeq(s);
      xs = _out0;
      xs = Std_Collections_Seq.__default.MergeSortBy(R, xs);
      return xs;
    }
    static MergeSortBy(lessThanOrEq, a) {
      if ((new BigNumber((a).length)).isLessThanOrEqualTo(_dafny.ONE)) {
        return a;
      } else {
        let _100_splitIndex = _dafny.EuclideanDivision(new BigNumber((a).length), new BigNumber(2));
        let _101_left = (a).slice(0, _100_splitIndex);
        let _102_right = (a).slice(_100_splitIndex);
        let _103_leftSorted = Std_Collections_Seq.__default.MergeSortBy(lessThanOrEq, _101_left);
        let _104_rightSorted = Std_Collections_Seq.__default.MergeSortBy(lessThanOrEq, _102_right);
        return Std_Collections_Seq.__default.MergeSortedWith(_103_leftSorted, _104_rightSorted, lessThanOrEq);
      }
    };
    static MergeSortedWith(left, right, lessThanOrEq) {
      let _105___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((left).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_105___accumulator, right);
        } else if ((new BigNumber((right).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_105___accumulator, left);
        } else if ((lessThanOrEq)((left)[_dafny.ZERO], (right)[_dafny.ZERO])) {
          _105___accumulator = _dafny.Seq.Concat(_105___accumulator, _dafny.Seq.of((left)[_dafny.ZERO]));
          let _in24 = (left).slice(_dafny.ONE);
          let _in25 = right;
          let _in26 = lessThanOrEq;
          left = _in24;
          right = _in25;
          lessThanOrEq = _in26;
          continue TAIL_CALL_START;
        } else {
          _105___accumulator = _dafny.Seq.Concat(_105___accumulator, _dafny.Seq.of((right)[_dafny.ZERO]));
          let _in27 = left;
          let _in28 = (right).slice(_dafny.ONE);
          let _in29 = lessThanOrEq;
          left = _in27;
          right = _in28;
          lessThanOrEq = _in29;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module Std_Collections_Seq
let Std_Collections_Array = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Collections.Array._default";
    }
    _parentTraits() {
      return [];
    }
    static BinarySearch(a, key, less) {
      let r = Std_Wrappers.Option.Default();
      let _106_lo;
      let _107_hi;
      let _rhs0 = _dafny.ZERO;
      let _rhs1 = new BigNumber((a).length);
      _106_lo = _rhs0;
      _107_hi = _rhs1;
      while ((_106_lo).isLessThan(_107_hi)) {
        let _108_mid;
        _108_mid = _dafny.EuclideanDivision((_106_lo).plus(_107_hi), new BigNumber(2));
        if ((less)(key, (a)[_108_mid])) {
          _107_hi = _108_mid;
        } else if ((less)((a)[_108_mid], key)) {
          _106_lo = (_108_mid).plus(_dafny.ONE);
        } else {
          r = Std_Wrappers.Option.create_Some(_108_mid);
          return r;
        }
      }
      r = Std_Wrappers.Option.create_None();
      return r;
      return r;
    }
  };
  return $module;
})(); // end of module Std_Collections_Array
let Std_Collections_Imap = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Collections.Imap._default";
    }
    _parentTraits() {
      return [];
    }
    static Get(m, x) {
      if ((m).contains(x)) {
        return Std_Wrappers.Option.create_Some((m).get(x));
      } else {
        return Std_Wrappers.Option.create_None();
      }
    };
  };
  return $module;
})(); // end of module Std_Collections_Imap
let Std_Functions = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Functions
let Std_Collections_Iset = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Collections_Iset
let Std_Collections_Map = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Collections.Map._default";
    }
    _parentTraits() {
      return [];
    }
    static Get(m, x) {
      if ((m).contains(x)) {
        return Std_Wrappers.Option.create_Some((m).get(x));
      } else {
        return Std_Wrappers.Option.create_None();
      }
    };
    static ToImap(m) {
      return function () {
        let _coll1 = new _dafny.Map();
        for (const _compr_1 of (m).Keys.Elements) {
          let _109_x = _compr_1;
          if ((m).contains(_109_x)) {
            _coll1.push([_109_x,(m).get(_109_x)]);
          }
        }
        return _coll1;
      }();
    };
    static RemoveKeys(m, xs) {
      return (m).Subtract(xs);
    };
    static Remove(m, x) {
      let _110_m_k = function () {
        let _coll2 = new _dafny.Map();
        for (const _compr_2 of (m).Keys.Elements) {
          let _111_x_k = _compr_2;
          if (((m).contains(_111_x_k)) && (!_dafny.areEqual(_111_x_k, x))) {
            _coll2.push([_111_x_k,(m).get(_111_x_k)]);
          }
        }
        return _coll2;
      }();
      return _110_m_k;
    };
    static Restrict(m, xs) {
      return function () {
        let _coll3 = new _dafny.Map();
        for (const _compr_3 of (xs).Elements) {
          let _112_x = _compr_3;
          if (((xs).contains(_112_x)) && ((m).contains(_112_x))) {
            _coll3.push([_112_x,(m).get(_112_x)]);
          }
        }
        return _coll3;
      }();
    };
    static Union(m, m_k) {
      return (m).Merge(m_k);
    };
  };
  return $module;
})(); // end of module Std_Collections_Map
let Std_Collections_Set = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Collections.Set._default";
    }
    _parentTraits() {
      return [];
    }
    static ExtractFromSingleton(s) {
      return function (_let_dummy_0) {
        let _113_x = undefined;
        L_ASSIGN_SUCH_THAT_1: {
          for (const _assign_such_that_1 of (s).Elements) {
            _113_x = _assign_such_that_1;
            if ((s).contains(_113_x)) {
              break L_ASSIGN_SUCH_THAT_1;
            }
          }
          throw new Error("assign-such-that search produced no value (line 7408)");
        }
        return _113_x;
      }(0);
    };
    static Map(f, xs) {
      let _114_ys = function () {
        let _coll4 = new _dafny.Set();
        for (const _compr_4 of (xs).Elements) {
          let _115_x = _compr_4;
          if ((xs).contains(_115_x)) {
            _coll4.add((f)(_115_x));
          }
        }
        return _coll4;
      }();
      return _114_ys;
    };
    static Filter(f, xs) {
      let _116_ys = function () {
        let _coll5 = new _dafny.Set();
        for (const _compr_5 of (xs).Elements) {
          let _117_x = _compr_5;
          if (((xs).contains(_117_x)) && ((f)(_117_x))) {
            _coll5.add(_117_x);
          }
        }
        return _coll5;
      }();
      return _116_ys;
    };
    static SetRange(a, b) {
      let _118___accumulator = _dafny.Set.fromElements();
      TAIL_CALL_START: while (true) {
        if ((a).isEqualTo(b)) {
          return (_dafny.Set.fromElements()).Union(_118___accumulator);
        } else {
          _118___accumulator = (_118___accumulator).Union(_dafny.Set.fromElements(a));
          let _in30 = (a).plus(_dafny.ONE);
          let _in31 = b;
          a = _in30;
          b = _in31;
          continue TAIL_CALL_START;
        }
      }
    };
    static SetRangeZeroBound(n) {
      return Std_Collections_Set.__default.SetRange(_dafny.ZERO, n);
    };
  };
  return $module;
})(); // end of module Std_Collections_Set
let Std_Collections = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Collections
let Std_DynamicArray = (function() {
  let $module = {};


  $module.DynamicArray = class DynamicArray {
    constructor () {
      this._tname = "Std.DynamicArray.DynamicArray";
      this.size = _dafny.ZERO;
      this.capacity = _dafny.ZERO;
      this.data = [];
    }
    _parentTraits() {
      return [];
    }
    __ctor() {
      let _this = this;
      (_this).size = _dafny.ZERO;
      (_this).capacity = _dafny.ZERO;
      let _nw3 = Array((_dafny.ZERO).toNumber());
      (_this).data = _nw3;
      return;
    }
    At(index) {
      let _this = this;
      return (_this.data)[index];
    };
    Put(index, element) {
      let _this = this;
      let _arr0 = _this.data;
      _arr0[(index)] = element;
      return;
    }
    Ensure(reserved, defaultValue) {
      let _this = this;
      let _119_newCapacity;
      _119_newCapacity = _this.capacity;
      while (((_119_newCapacity).minus(_this.size)).isLessThan(reserved)) {
        _119_newCapacity = (_this).DefaultNewCapacity(_119_newCapacity);
      }
      if ((_this.capacity).isLessThan(_119_newCapacity)) {
        (_this).Realloc(defaultValue, _119_newCapacity);
      }
      return;
    }
    PopFast() {
      let _this = this;
      (_this).size = (_this.size).minus(_dafny.ONE);
      return;
    }
    PushFast(element) {
      let _this = this;
      let _arr1 = _this.data;
      let _index5 = _this.size;
      _arr1[_index5] = element;
      (_this).size = (_this.size).plus(_dafny.ONE);
      return;
    }
    Push(element) {
      let _this = this;
      if ((_this.size).isEqualTo(_this.capacity)) {
        (_this).ReallocDefault(element);
      }
      (_this).PushFast(element);
      return;
    }
    Realloc(defaultValue, newCapacity) {
      let _this = this;
      let _120_oldData;
      let _121_oldCapacity;
      let _rhs2 = _this.data;
      let _rhs3 = _this.capacity;
      _120_oldData = _rhs2;
      _121_oldCapacity = _rhs3;
      let _init3 = ((_122_defaultValue) => function (_123___v0) {
        return _122_defaultValue;
      })(defaultValue);
      let _nw4 = Array((newCapacity).toNumber());
      for (let _i0_3 = 0; _i0_3 < new BigNumber(_nw4.length); _i0_3++) {
        _nw4[_i0_3] = _init3(new BigNumber(_i0_3));
      }
      let _rhs4 = _nw4;
      let _rhs5 = newCapacity;
      let _lhs0 = _this;
      let _lhs1 = _this;
      _lhs0.data = _rhs4;
      _lhs1.capacity = _rhs5;
      (_this).CopyFrom(_120_oldData, _121_oldCapacity);
      return;
    }
    DefaultNewCapacity(capacity) {
      let _this = this;
      if ((capacity).isEqualTo(_dafny.ZERO)) {
        return new BigNumber(8);
      } else {
        return (new BigNumber(2)).multipliedBy(capacity);
      }
    };
    ReallocDefault(defaultValue) {
      let _this = this;
      (_this).Realloc(defaultValue, (_this).DefaultNewCapacity(_this.capacity));
      return;
    }
    CopyFrom(newData, count) {
      let _this = this;
      for (const _guard_loop_0 of _dafny.IntegerRange(_dafny.ZERO, count)) {
        let _124_index = _guard_loop_0;
        if ((true) && (((_dafny.ZERO).isLessThanOrEqualTo(_124_index)) && ((_124_index).isLessThan(count)))) {
          let _arr2 = _this.data;
          _arr2[(_124_index)] = (newData)[_124_index];
        }
      }
      return;
    }
  };
  return $module;
})(); // end of module Std_DynamicArray
let Std_FileIO = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.FileIO._default";
    }
    _parentTraits() {
      return [];
    }
    static ReadBytesFromFile(path) {
      let res = Std_Wrappers.Result.Default(_dafny.Seq.of());
      let _125_isError;
      let _126_bytesRead;
      let _127_errorMsg;
      let _out1;
      let _out2;
      let _out3;
      let _outcollector0 = Std_FileIOInternalExterns.__default.INTERNAL__ReadBytesFromFile(path);
      _out1 = _outcollector0[0];
      _out2 = _outcollector0[1];
      _out3 = _outcollector0[2];
      _125_isError = _out1;
      _126_bytesRead = _out2;
      _127_errorMsg = _out3;
      res = ((_125_isError) ? (Std_Wrappers.Result.create_Failure(_127_errorMsg)) : (Std_Wrappers.Result.create_Success(_126_bytesRead)));
      return res;
      return res;
    }
    static WriteBytesToFile(path, bytes) {
      let res = Std_Wrappers.Result.Default(_dafny.Tuple.Default());
      let _128_isError;
      let _129_errorMsg;
      let _out4;
      let _out5;
      let _outcollector1 = Std_FileIOInternalExterns.__default.INTERNAL__WriteBytesToFile(path, bytes);
      _out4 = _outcollector1[0];
      _out5 = _outcollector1[1];
      _128_isError = _out4;
      _129_errorMsg = _out5;
      res = ((_128_isError) ? (Std_Wrappers.Result.create_Failure(_129_errorMsg)) : (Std_Wrappers.Result.create_Success(_dafny.Tuple.of())));
      return res;
      return res;
    }
  };
  return $module;
})(); // end of module Std_FileIO
let Std_Arithmetic_GeneralInternals = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Arithmetic_GeneralInternals
let Std_Arithmetic_MulInternalsNonlinear = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Arithmetic_MulInternalsNonlinear
let Std_Arithmetic_MulInternals = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Arithmetic.MulInternals._default";
    }
    _parentTraits() {
      return [];
    }
    static MulPos(x, y) {
      let _130___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((x).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_130___accumulator);
        } else {
          _130___accumulator = (_130___accumulator).plus(y);
          let _in32 = (x).minus(_dafny.ONE);
          let _in33 = y;
          x = _in32;
          y = _in33;
          continue TAIL_CALL_START;
        }
      }
    };
    static MulRecursive(x, y) {
      if ((_dafny.ZERO).isLessThanOrEqualTo(x)) {
        return Std_Arithmetic_MulInternals.__default.MulPos(x, y);
      } else {
        return (new BigNumber(-1)).multipliedBy(Std_Arithmetic_MulInternals.__default.MulPos((new BigNumber(-1)).multipliedBy(x), y));
      }
    };
  };
  return $module;
})(); // end of module Std_Arithmetic_MulInternals
let Std_Arithmetic_Mul = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Arithmetic_Mul
let Std_Arithmetic_ModInternalsNonlinear = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Arithmetic_ModInternalsNonlinear
let Std_Arithmetic_DivInternalsNonlinear = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Arithmetic_DivInternalsNonlinear
let Std_Arithmetic_ModInternals = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Arithmetic.ModInternals._default";
    }
    _parentTraits() {
      return [];
    }
    static ModRecursive(x, d) {
      TAIL_CALL_START: while (true) {
        if ((x).isLessThan(_dafny.ZERO)) {
          let _in34 = (d).plus(x);
          let _in35 = d;
          x = _in34;
          d = _in35;
          continue TAIL_CALL_START;
        } else if ((x).isLessThan(d)) {
          return x;
        } else {
          let _in36 = (x).minus(d);
          let _in37 = d;
          x = _in36;
          d = _in37;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module Std_Arithmetic_ModInternals
let Std_Arithmetic_DivInternals = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Arithmetic.DivInternals._default";
    }
    _parentTraits() {
      return [];
    }
    static DivPos(x, d) {
      let _131___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((x).isLessThan(_dafny.ZERO)) {
          _131___accumulator = (_131___accumulator).plus(new BigNumber(-1));
          let _in38 = (x).plus(d);
          let _in39 = d;
          x = _in38;
          d = _in39;
          continue TAIL_CALL_START;
        } else if ((x).isLessThan(d)) {
          return (_dafny.ZERO).plus(_131___accumulator);
        } else {
          _131___accumulator = (_131___accumulator).plus(_dafny.ONE);
          let _in40 = (x).minus(d);
          let _in41 = d;
          x = _in40;
          d = _in41;
          continue TAIL_CALL_START;
        }
      }
    };
    static DivRecursive(x, d) {
      if ((_dafny.ZERO).isLessThan(d)) {
        return Std_Arithmetic_DivInternals.__default.DivPos(x, d);
      } else {
        return (new BigNumber(-1)).multipliedBy(Std_Arithmetic_DivInternals.__default.DivPos(x, (new BigNumber(-1)).multipliedBy(d)));
      }
    };
  };
  return $module;
})(); // end of module Std_Arithmetic_DivInternals
let Std_Arithmetic_DivMod = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Arithmetic.DivMod._default";
    }
    _parentTraits() {
      return [];
    }
    static MultiplesVanish(a, b, m) {
      return ((((m).multipliedBy(a)).plus(b)).mod(m)).isEqualTo((b).mod(m));
    };
  };
  return $module;
})(); // end of module Std_Arithmetic_DivMod
let Std_Arithmetic_Power = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Arithmetic.Power._default";
    }
    _parentTraits() {
      return [];
    }
    static Pow(b, e) {
      let _132___accumulator = _dafny.ONE;
      TAIL_CALL_START: while (true) {
        if ((e).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ONE).multipliedBy(_132___accumulator);
        } else {
          _132___accumulator = (_132___accumulator).multipliedBy(b);
          let _in42 = b;
          let _in43 = (e).minus(_dafny.ONE);
          b = _in42;
          e = _in43;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module Std_Arithmetic_Power
let Std_Arithmetic_Logarithm = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Arithmetic.Logarithm._default";
    }
    _parentTraits() {
      return [];
    }
    static Log(base, pow) {
      let _133___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((pow).isLessThan(base)) {
          return (_dafny.ZERO).plus(_133___accumulator);
        } else {
          _133___accumulator = (_133___accumulator).plus(_dafny.ONE);
          let _in44 = base;
          let _in45 = _dafny.EuclideanDivision(pow, base);
          base = _in44;
          pow = _in45;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module Std_Arithmetic_Logarithm
let Std_Arithmetic_Power2 = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Arithmetic.Power2._default";
    }
    _parentTraits() {
      return [];
    }
    static Pow2(e) {
      return Std_Arithmetic_Power.__default.Pow(new BigNumber(2), e);
    };
  };
  return $module;
})(); // end of module Std_Arithmetic_Power2
let Std_Arithmetic = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Arithmetic
let Std_Strings_HexConversion = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Strings.HexConversion._default";
    }
    _parentTraits() {
      return [];
    }
    static BASE() {
      return Std_Strings_HexConversion.__default.base;
    };
    static IsDigitChar(c) {
      return (Std_Strings_HexConversion.__default.charToDigit).contains(c);
    };
    static OfDigits(digits) {
      let _134___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _134___accumulator);
        } else {
          _134___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_Strings_HexConversion.__default.chars)[(digits)[_dafny.ZERO]]), _134___accumulator);
          let _in46 = (digits).slice(_dafny.ONE);
          digits = _in46;
          continue TAIL_CALL_START;
        }
      }
    };
    static OfNat(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of((Std_Strings_HexConversion.__default.chars)[_dafny.ZERO]);
      } else {
        return Std_Strings_HexConversion.__default.OfDigits(Std_Strings_HexConversion.__default.FromNat(n));
      }
    };
    static IsNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((_dafny.areEqual((str)[_dafny.ZERO], minus)) || ((Std_Strings_HexConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_1) {
        let _135_c = _forall_var_1;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _135_c)) || (Std_Strings_HexConversion.__default.IsDigitChar(_135_c));
      })));
    };
    static OfInt(n, minus) {
      if ((_dafny.ZERO).isLessThanOrEqualTo(n)) {
        return Std_Strings_HexConversion.__default.OfNat(n);
      } else {
        return _dafny.Seq.Concat(_dafny.Seq.of(minus), Std_Strings_HexConversion.__default.OfNat((_dafny.ZERO).minus(n)));
      }
    };
    static ToNat(str) {
      if (_dafny.areEqual(str, _dafny.Seq.of())) {
        return _dafny.ZERO;
      } else {
        let _136_c = (str)[(new BigNumber((str).length)).minus(_dafny.ONE)];
        return ((Std_Strings_HexConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_Strings_HexConversion.__default.base)).plus((Std_Strings_HexConversion.__default.charToDigit).get(_136_c));
      }
    };
    static ToInt(str, minus) {
      if (_dafny.Seq.IsPrefixOf(_dafny.Seq.of(minus), str)) {
        return (_dafny.ZERO).minus((Std_Strings_HexConversion.__default.ToNat((str).slice(_dafny.ONE))));
      } else {
        return Std_Strings_HexConversion.__default.ToNat(str);
      }
    };
    static ToNatRight(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.ZERO;
      } else {
        return ((Std_Strings_HexConversion.__default.ToNatRight(Std_Collections_Seq.__default.DropFirst(xs))).multipliedBy(Std_Strings_HexConversion.__default.BASE())).plus(Std_Collections_Seq.__default.First(xs));
      }
    };
    static ToNatLeft(xs) {
      let _137___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_137___accumulator);
        } else {
          _137___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_Strings_HexConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_137___accumulator);
          let _in47 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in47;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _138___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_138___accumulator, _dafny.Seq.of());
        } else {
          _138___accumulator = _dafny.Seq.Concat(_138___accumulator, _dafny.Seq.of((n).mod(Std_Strings_HexConversion.__default.BASE())));
          let _in48 = _dafny.EuclideanDivision(n, Std_Strings_HexConversion.__default.BASE());
          n = _in48;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in49 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in50 = n;
          xs = _in49;
          n = _in50;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _139_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_Strings_HexConversion.__default.SeqExtend(xs, _139_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_Strings_HexConversion.__default.SeqExtend(Std_Strings_HexConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _140_xs = Std_Strings_HexConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _140_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs1 = Std_Strings_HexConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _141_zs_k = (_let_tmp_rhs1)[0];
        let _142_cin = (_let_tmp_rhs1)[1];
        let _143_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_142_cin);
        let _let_tmp_rhs2 = (((_143_sum).isLessThan(Std_Strings_HexConversion.__default.BASE())) ? (_dafny.Tuple.of(_143_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_143_sum).minus(Std_Strings_HexConversion.__default.BASE()), _dafny.ONE)));
        let _144_sum__out = (_let_tmp_rhs2)[0];
        let _145_cout = (_let_tmp_rhs2)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_141_zs_k, _dafny.Seq.of(_144_sum__out)), _145_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs3 = Std_Strings_HexConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _146_zs = (_let_tmp_rhs3)[0];
        let _147_cin = (_let_tmp_rhs3)[1];
        let _let_tmp_rhs4 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_147_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_147_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_Strings_HexConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_147_cin), _dafny.ONE)));
        let _148_diff__out = (_let_tmp_rhs4)[0];
        let _149_cout = (_let_tmp_rhs4)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_146_zs, _dafny.Seq.of(_148_diff__out)), _149_cout);
      }
    };
    static get HEX__DIGITS() {
      return _dafny.Seq.UnicodeFromString("0123456789ABCDEF");
    };
    static get chars() {
      return Std_Strings_HexConversion.__default.HEX__DIGITS;
    };
    static get base() {
      return new BigNumber((Std_Strings_HexConversion.__default.chars).length);
    };
    static get charToDigit() {
      return _dafny.Map.Empty.slice().updateUnsafe(new _dafny.CodePoint('0'.codePointAt(0)),_dafny.ZERO).updateUnsafe(new _dafny.CodePoint('1'.codePointAt(0)),_dafny.ONE).updateUnsafe(new _dafny.CodePoint('2'.codePointAt(0)),new BigNumber(2)).updateUnsafe(new _dafny.CodePoint('3'.codePointAt(0)),new BigNumber(3)).updateUnsafe(new _dafny.CodePoint('4'.codePointAt(0)),new BigNumber(4)).updateUnsafe(new _dafny.CodePoint('5'.codePointAt(0)),new BigNumber(5)).updateUnsafe(new _dafny.CodePoint('6'.codePointAt(0)),new BigNumber(6)).updateUnsafe(new _dafny.CodePoint('7'.codePointAt(0)),new BigNumber(7)).updateUnsafe(new _dafny.CodePoint('8'.codePointAt(0)),new BigNumber(8)).updateUnsafe(new _dafny.CodePoint('9'.codePointAt(0)),new BigNumber(9)).updateUnsafe(new _dafny.CodePoint('a'.codePointAt(0)),new BigNumber(10)).updateUnsafe(new _dafny.CodePoint('b'.codePointAt(0)),new BigNumber(11)).updateUnsafe(new _dafny.CodePoint('c'.codePointAt(0)),new BigNumber(12)).updateUnsafe(new _dafny.CodePoint('d'.codePointAt(0)),new BigNumber(13)).updateUnsafe(new _dafny.CodePoint('e'.codePointAt(0)),new BigNumber(14)).updateUnsafe(new _dafny.CodePoint('f'.codePointAt(0)),new BigNumber(15)).updateUnsafe(new _dafny.CodePoint('A'.codePointAt(0)),new BigNumber(10)).updateUnsafe(new _dafny.CodePoint('B'.codePointAt(0)),new BigNumber(11)).updateUnsafe(new _dafny.CodePoint('C'.codePointAt(0)),new BigNumber(12)).updateUnsafe(new _dafny.CodePoint('D'.codePointAt(0)),new BigNumber(13)).updateUnsafe(new _dafny.CodePoint('E'.codePointAt(0)),new BigNumber(14)).updateUnsafe(new _dafny.CodePoint('F'.codePointAt(0)),new BigNumber(15));
    };
  };

  $module.CharSeq = class CharSeq {
    constructor () {
    }
    static get Default() {
      return '';
    }
  };

  $module.digit = class digit {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module Std_Strings_HexConversion
let Std_Strings_DecimalConversion = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Strings.DecimalConversion._default";
    }
    _parentTraits() {
      return [];
    }
    static BASE() {
      return Std_Strings_DecimalConversion.__default.base;
    };
    static IsDigitChar(c) {
      return (Std_Strings_DecimalConversion.__default.charToDigit).contains(c);
    };
    static OfDigits(digits) {
      let _150___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _150___accumulator);
        } else {
          _150___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_Strings_DecimalConversion.__default.chars)[(digits)[_dafny.ZERO]]), _150___accumulator);
          let _in51 = (digits).slice(_dafny.ONE);
          digits = _in51;
          continue TAIL_CALL_START;
        }
      }
    };
    static OfNat(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of((Std_Strings_DecimalConversion.__default.chars)[_dafny.ZERO]);
      } else {
        return Std_Strings_DecimalConversion.__default.OfDigits(Std_Strings_DecimalConversion.__default.FromNat(n));
      }
    };
    static IsNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((_dafny.areEqual((str)[_dafny.ZERO], minus)) || ((Std_Strings_DecimalConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_2) {
        let _151_c = _forall_var_2;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _151_c)) || (Std_Strings_DecimalConversion.__default.IsDigitChar(_151_c));
      })));
    };
    static OfInt(n, minus) {
      if ((_dafny.ZERO).isLessThanOrEqualTo(n)) {
        return Std_Strings_DecimalConversion.__default.OfNat(n);
      } else {
        return _dafny.Seq.Concat(_dafny.Seq.of(minus), Std_Strings_DecimalConversion.__default.OfNat((_dafny.ZERO).minus(n)));
      }
    };
    static ToNat(str) {
      if (_dafny.areEqual(str, _dafny.Seq.of())) {
        return _dafny.ZERO;
      } else {
        let _152_c = (str)[(new BigNumber((str).length)).minus(_dafny.ONE)];
        return ((Std_Strings_DecimalConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_Strings_DecimalConversion.__default.base)).plus((Std_Strings_DecimalConversion.__default.charToDigit).get(_152_c));
      }
    };
    static ToInt(str, minus) {
      if (_dafny.Seq.IsPrefixOf(_dafny.Seq.of(minus), str)) {
        return (_dafny.ZERO).minus((Std_Strings_DecimalConversion.__default.ToNat((str).slice(_dafny.ONE))));
      } else {
        return Std_Strings_DecimalConversion.__default.ToNat(str);
      }
    };
    static ToNatRight(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.ZERO;
      } else {
        return ((Std_Strings_DecimalConversion.__default.ToNatRight(Std_Collections_Seq.__default.DropFirst(xs))).multipliedBy(Std_Strings_DecimalConversion.__default.BASE())).plus(Std_Collections_Seq.__default.First(xs));
      }
    };
    static ToNatLeft(xs) {
      let _153___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_153___accumulator);
        } else {
          _153___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_Strings_DecimalConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_153___accumulator);
          let _in52 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in52;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _154___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_154___accumulator, _dafny.Seq.of());
        } else {
          _154___accumulator = _dafny.Seq.Concat(_154___accumulator, _dafny.Seq.of((n).mod(Std_Strings_DecimalConversion.__default.BASE())));
          let _in53 = _dafny.EuclideanDivision(n, Std_Strings_DecimalConversion.__default.BASE());
          n = _in53;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in54 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in55 = n;
          xs = _in54;
          n = _in55;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _155_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_Strings_DecimalConversion.__default.SeqExtend(xs, _155_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_Strings_DecimalConversion.__default.SeqExtend(Std_Strings_DecimalConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _156_xs = Std_Strings_DecimalConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _156_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs5 = Std_Strings_DecimalConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _157_zs_k = (_let_tmp_rhs5)[0];
        let _158_cin = (_let_tmp_rhs5)[1];
        let _159_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_158_cin);
        let _let_tmp_rhs6 = (((_159_sum).isLessThan(Std_Strings_DecimalConversion.__default.BASE())) ? (_dafny.Tuple.of(_159_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_159_sum).minus(Std_Strings_DecimalConversion.__default.BASE()), _dafny.ONE)));
        let _160_sum__out = (_let_tmp_rhs6)[0];
        let _161_cout = (_let_tmp_rhs6)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_157_zs_k, _dafny.Seq.of(_160_sum__out)), _161_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs7 = Std_Strings_DecimalConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _162_zs = (_let_tmp_rhs7)[0];
        let _163_cin = (_let_tmp_rhs7)[1];
        let _let_tmp_rhs8 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_163_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_163_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_Strings_DecimalConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_163_cin), _dafny.ONE)));
        let _164_diff__out = (_let_tmp_rhs8)[0];
        let _165_cout = (_let_tmp_rhs8)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_162_zs, _dafny.Seq.of(_164_diff__out)), _165_cout);
      }
    };
    static get DIGITS() {
      return _dafny.Seq.UnicodeFromString("0123456789");
    };
    static get chars() {
      return Std_Strings_DecimalConversion.__default.DIGITS;
    };
    static get base() {
      return new BigNumber((Std_Strings_DecimalConversion.__default.chars).length);
    };
    static get charToDigit() {
      return _dafny.Map.Empty.slice().updateUnsafe(new _dafny.CodePoint('0'.codePointAt(0)),_dafny.ZERO).updateUnsafe(new _dafny.CodePoint('1'.codePointAt(0)),_dafny.ONE).updateUnsafe(new _dafny.CodePoint('2'.codePointAt(0)),new BigNumber(2)).updateUnsafe(new _dafny.CodePoint('3'.codePointAt(0)),new BigNumber(3)).updateUnsafe(new _dafny.CodePoint('4'.codePointAt(0)),new BigNumber(4)).updateUnsafe(new _dafny.CodePoint('5'.codePointAt(0)),new BigNumber(5)).updateUnsafe(new _dafny.CodePoint('6'.codePointAt(0)),new BigNumber(6)).updateUnsafe(new _dafny.CodePoint('7'.codePointAt(0)),new BigNumber(7)).updateUnsafe(new _dafny.CodePoint('8'.codePointAt(0)),new BigNumber(8)).updateUnsafe(new _dafny.CodePoint('9'.codePointAt(0)),new BigNumber(9));
    };
  };

  $module.CharSeq = class CharSeq {
    constructor () {
    }
    static get Default() {
      return '';
    }
  };

  $module.digit = class digit {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module Std_Strings_DecimalConversion
let Std_Strings_CharStrEscaping = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Strings.CharStrEscaping._default";
    }
    _parentTraits() {
      return [];
    }
    static Escape(str, mustEscape, escape) {
      let _166___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(str, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_166___accumulator, str);
        } else if ((mustEscape).contains((str)[_dafny.ZERO])) {
          _166___accumulator = _dafny.Seq.Concat(_166___accumulator, _dafny.Seq.of(escape, (str)[_dafny.ZERO]));
          let _in56 = (str).slice(_dafny.ONE);
          let _in57 = mustEscape;
          let _in58 = escape;
          str = _in56;
          mustEscape = _in57;
          escape = _in58;
          continue TAIL_CALL_START;
        } else {
          _166___accumulator = _dafny.Seq.Concat(_166___accumulator, _dafny.Seq.of((str)[_dafny.ZERO]));
          let _in59 = (str).slice(_dafny.ONE);
          let _in60 = mustEscape;
          let _in61 = escape;
          str = _in59;
          mustEscape = _in60;
          escape = _in61;
          continue TAIL_CALL_START;
        }
      }
    };
    static Unescape(str, escape) {
      if (_dafny.areEqual(str, _dafny.Seq.of())) {
        return Std_Wrappers.Option.create_Some(str);
      } else if (_dafny.areEqual((str)[_dafny.ZERO], escape)) {
        if ((_dafny.ONE).isLessThan(new BigNumber((str).length))) {
          let _167_valueOrError0 = Std_Strings_CharStrEscaping.__default.Unescape((str).slice(new BigNumber(2)), escape);
          if ((_167_valueOrError0).IsFailure()) {
            return (_167_valueOrError0).PropagateFailure();
          } else {
            let _168_tl = (_167_valueOrError0).Extract();
            return Std_Wrappers.Option.create_Some(_dafny.Seq.Concat(_dafny.Seq.of((str)[_dafny.ONE]), _168_tl));
          }
        } else {
          return Std_Wrappers.Option.create_None();
        }
      } else {
        let _169_valueOrError1 = Std_Strings_CharStrEscaping.__default.Unescape((str).slice(_dafny.ONE), escape);
        if ((_169_valueOrError1).IsFailure()) {
          return (_169_valueOrError1).PropagateFailure();
        } else {
          let _170_tl = (_169_valueOrError1).Extract();
          return Std_Wrappers.Option.create_Some(_dafny.Seq.Concat(_dafny.Seq.of((str)[_dafny.ZERO]), _170_tl));
        }
      }
    };
  };
  return $module;
})(); // end of module Std_Strings_CharStrEscaping
let Std_Strings = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Strings._default";
    }
    _parentTraits() {
      return [];
    }
    static OfNat(n) {
      return Std_Strings_DecimalConversion.__default.OfNat(n);
    };
    static OfInt(n) {
      return Std_Strings_DecimalConversion.__default.OfInt(n, new _dafny.CodePoint('-'.codePointAt(0)));
    };
    static ToNat(str) {
      return Std_Strings_DecimalConversion.__default.ToNat(str);
    };
    static ToInt(str) {
      return Std_Strings_DecimalConversion.__default.ToInt(str, new _dafny.CodePoint('-'.codePointAt(0)));
    };
    static EscapeQuotes(str) {
      return Std_Strings_CharStrEscaping.__default.Escape(str, _dafny.Set.fromElements(new _dafny.CodePoint('\"'.codePointAt(0)), new _dafny.CodePoint('\''.codePointAt(0))), new _dafny.CodePoint('\\'.codePointAt(0)));
    };
    static UnescapeQuotes(str) {
      return Std_Strings_CharStrEscaping.__default.Unescape(str, new _dafny.CodePoint('\\'.codePointAt(0)));
    };
    static OfBool(b) {
      if (b) {
        return _dafny.Seq.UnicodeFromString("true");
      } else {
        return _dafny.Seq.UnicodeFromString("false");
      }
    };
    static OfChar(c) {
      return _dafny.Seq.of(c);
    };
  };
  return $module;
})(); // end of module Std_Strings
let Std_Unicode_Base = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Unicode.Base._default";
    }
    _parentTraits() {
      return [];
    }
    static IsInAssignedPlane(i) {
      let _171_plane = (_dafny.ShiftRight(i, (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      return (Std_Unicode_Base.__default.ASSIGNED__PLANES).contains(_171_plane);
    };
    static get HIGH__SURROGATE__MIN() {
      return new BigNumber(55296);
    };
    static get HIGH__SURROGATE__MAX() {
      return new BigNumber(56319);
    };
    static get LOW__SURROGATE__MIN() {
      return new BigNumber(56320);
    };
    static get LOW__SURROGATE__MAX() {
      return new BigNumber(57343);
    };
    static get ASSIGNED__PLANES() {
      return _dafny.Set.fromElements(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(14), new BigNumber(15), new BigNumber(16));
    };
  };

  $module.CodePoint = class CodePoint {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.HighSurrogateCodePoint = class HighSurrogateCodePoint {
    constructor () {
    }
    static get Witness() {
      return Std_Unicode_Base.__default.HIGH__SURROGATE__MIN;
    }
    static get Default() {
      return Std_Unicode_Base.HighSurrogateCodePoint.Witness;
    }
  };

  $module.LowSurrogateCodePoint = class LowSurrogateCodePoint {
    constructor () {
    }
    static get Witness() {
      return Std_Unicode_Base.__default.LOW__SURROGATE__MIN;
    }
    static get Default() {
      return Std_Unicode_Base.LowSurrogateCodePoint.Witness;
    }
  };

  $module.ScalarValue = class ScalarValue {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.AssignedCodePoint = class AssignedCodePoint {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module Std_Unicode_Base
let Std_Unicode_Utf8EncodingForm = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Unicode.Utf8EncodingForm._default";
    }
    _parentTraits() {
      return [];
    }
    static IsMinimalWellFormedCodeUnitSubsequence(s) {
      if ((new BigNumber((s).length)).isEqualTo(_dafny.ONE)) {
        let _172_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedSingleCodeUnitSequence(s);
        return _172_b;
      } else if ((new BigNumber((s).length)).isEqualTo(new BigNumber(2))) {
        let _173_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _173_b;
      } else if ((new BigNumber((s).length)).isEqualTo(new BigNumber(3))) {
        let _174_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedTripleCodeUnitSequence(s);
        return _174_b;
      } else if ((new BigNumber((s).length)).isEqualTo(new BigNumber(4))) {
        let _175_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedQuadrupleCodeUnitSequence(s);
        return _175_b;
      } else {
        return false;
      }
    };
    static IsWellFormedSingleCodeUnitSequence(s) {
      let _176_firstByte = (s)[_dafny.ZERO];
      return (true) && (((_dafny.ZERO).isLessThanOrEqualTo(_176_firstByte)) && ((_176_firstByte).isLessThanOrEqualTo(new BigNumber(127))));
    };
    static IsWellFormedDoubleCodeUnitSequence(s) {
      let _177_firstByte = (s)[_dafny.ZERO];
      let _178_secondByte = (s)[_dafny.ONE];
      return (((new BigNumber(194)).isLessThanOrEqualTo(_177_firstByte)) && ((_177_firstByte).isLessThanOrEqualTo(new BigNumber(223)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_178_secondByte)) && ((_178_secondByte).isLessThanOrEqualTo(new BigNumber(191))));
    };
    static IsWellFormedTripleCodeUnitSequence(s) {
      let _179_firstByte = (s)[_dafny.ZERO];
      let _180_secondByte = (s)[_dafny.ONE];
      let _181_thirdByte = (s)[new BigNumber(2)];
      return ((((((_179_firstByte).isEqualTo(new BigNumber(224))) && (((new BigNumber(160)).isLessThanOrEqualTo(_180_secondByte)) && ((_180_secondByte).isLessThanOrEqualTo(new BigNumber(191))))) || ((((new BigNumber(225)).isLessThanOrEqualTo(_179_firstByte)) && ((_179_firstByte).isLessThanOrEqualTo(new BigNumber(236)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_180_secondByte)) && ((_180_secondByte).isLessThanOrEqualTo(new BigNumber(191)))))) || (((_179_firstByte).isEqualTo(new BigNumber(237))) && (((new BigNumber(128)).isLessThanOrEqualTo(_180_secondByte)) && ((_180_secondByte).isLessThanOrEqualTo(new BigNumber(159)))))) || ((((new BigNumber(238)).isLessThanOrEqualTo(_179_firstByte)) && ((_179_firstByte).isLessThanOrEqualTo(new BigNumber(239)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_180_secondByte)) && ((_180_secondByte).isLessThanOrEqualTo(new BigNumber(191)))))) && (((new BigNumber(128)).isLessThanOrEqualTo(_181_thirdByte)) && ((_181_thirdByte).isLessThanOrEqualTo(new BigNumber(191))));
    };
    static IsWellFormedQuadrupleCodeUnitSequence(s) {
      let _182_firstByte = (s)[_dafny.ZERO];
      let _183_secondByte = (s)[_dafny.ONE];
      let _184_thirdByte = (s)[new BigNumber(2)];
      let _185_fourthByte = (s)[new BigNumber(3)];
      return ((((((_182_firstByte).isEqualTo(new BigNumber(240))) && (((new BigNumber(144)).isLessThanOrEqualTo(_183_secondByte)) && ((_183_secondByte).isLessThanOrEqualTo(new BigNumber(191))))) || ((((new BigNumber(241)).isLessThanOrEqualTo(_182_firstByte)) && ((_182_firstByte).isLessThanOrEqualTo(new BigNumber(243)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_183_secondByte)) && ((_183_secondByte).isLessThanOrEqualTo(new BigNumber(191)))))) || (((_182_firstByte).isEqualTo(new BigNumber(244))) && (((new BigNumber(128)).isLessThanOrEqualTo(_183_secondByte)) && ((_183_secondByte).isLessThanOrEqualTo(new BigNumber(143)))))) && (((new BigNumber(128)).isLessThanOrEqualTo(_184_thirdByte)) && ((_184_thirdByte).isLessThanOrEqualTo(new BigNumber(191))))) && (((new BigNumber(128)).isLessThanOrEqualTo(_185_fourthByte)) && ((_185_fourthByte).isLessThanOrEqualTo(new BigNumber(191))));
    };
    static SplitPrefixMinimalWellFormedCodeUnitSubsequence(s) {
      if (((_dafny.ONE).isLessThanOrEqualTo(new BigNumber((s).length))) && (Std_Unicode_Utf8EncodingForm.__default.IsWellFormedSingleCodeUnitSequence((s).slice(0, _dafny.ONE)))) {
        return Std_Wrappers.Option.create_Some((s).slice(0, _dafny.ONE));
      } else if (((new BigNumber(2)).isLessThanOrEqualTo(new BigNumber((s).length))) && (Std_Unicode_Utf8EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence((s).slice(0, new BigNumber(2))))) {
        return Std_Wrappers.Option.create_Some((s).slice(0, new BigNumber(2)));
      } else if (((new BigNumber(3)).isLessThanOrEqualTo(new BigNumber((s).length))) && (Std_Unicode_Utf8EncodingForm.__default.IsWellFormedTripleCodeUnitSequence((s).slice(0, new BigNumber(3))))) {
        return Std_Wrappers.Option.create_Some((s).slice(0, new BigNumber(3)));
      } else if (((new BigNumber(4)).isLessThanOrEqualTo(new BigNumber((s).length))) && (Std_Unicode_Utf8EncodingForm.__default.IsWellFormedQuadrupleCodeUnitSequence((s).slice(0, new BigNumber(4))))) {
        return Std_Wrappers.Option.create_Some((s).slice(0, new BigNumber(4)));
      } else {
        return Std_Wrappers.Option.create_None();
      }
    };
    static EncodeScalarValue(v) {
      if ((v).isLessThanOrEqualTo(new BigNumber(127))) {
        return Std_Unicode_Utf8EncodingForm.__default.EncodeScalarValueSingleByte(v);
      } else if ((v).isLessThanOrEqualTo(new BigNumber(2047))) {
        return Std_Unicode_Utf8EncodingForm.__default.EncodeScalarValueDoubleByte(v);
      } else if ((v).isLessThanOrEqualTo(new BigNumber(65535))) {
        return Std_Unicode_Utf8EncodingForm.__default.EncodeScalarValueTripleByte(v);
      } else {
        return Std_Unicode_Utf8EncodingForm.__default.EncodeScalarValueQuadrupleByte(v);
      }
    };
    static EncodeScalarValueSingleByte(v) {
      let _186_x = _dafny.BitwiseAnd(v, new BigNumber(127));
      let _187_firstByte = _186_x;
      return _dafny.Seq.of(_187_firstByte);
    };
    static EncodeScalarValueDoubleByte(v) {
      let _188_x = _dafny.BitwiseAnd(v, new BigNumber(63));
      let _189_y = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(1984)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _190_firstByte = _dafny.BitwiseOr(new BigNumber(192), _189_y);
      let _191_secondByte = _dafny.BitwiseOr(new BigNumber(128), _188_x);
      return _dafny.Seq.of(_190_firstByte, _191_secondByte);
    };
    static EncodeScalarValueTripleByte(v) {
      let _192_x = _dafny.BitwiseAnd(v, new BigNumber(63));
      let _193_y = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(4032)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _194_z = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(61440)), (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _195_firstByte = _dafny.BitwiseOr(new BigNumber(224), _194_z);
      let _196_secondByte = _dafny.BitwiseOr(new BigNumber(128), _193_y);
      let _197_thirdByte = _dafny.BitwiseOr(new BigNumber(128), _192_x);
      return _dafny.Seq.of(_195_firstByte, _196_secondByte, _197_thirdByte);
    };
    static EncodeScalarValueQuadrupleByte(v) {
      let _198_x = _dafny.BitwiseAnd(v, new BigNumber(63));
      let _199_y = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(4032)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _200_z = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(61440)), (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _201_u2 = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(196608)), (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _202_u1 = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(1835008)), (new BigNumber(18)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _203_firstByte = _dafny.BitwiseOr(new BigNumber(240), _202_u1);
      let _204_secondByte = _dafny.BitwiseOr(_dafny.BitwiseOr(new BigNumber(128), (_dafny.ShiftLeft(_201_u2, (new BigNumber(4)).toNumber())).mod(new BigNumber(2).exponentiatedBy(8))), _200_z);
      let _205_thirdByte = _dafny.BitwiseOr(new BigNumber(128), _199_y);
      let _206_fourthByte = _dafny.BitwiseOr(new BigNumber(128), _198_x);
      return _dafny.Seq.of(_203_firstByte, _204_secondByte, _205_thirdByte, _206_fourthByte);
    };
    static DecodeMinimalWellFormedCodeUnitSubsequence(m) {
      if ((new BigNumber((m).length)).isEqualTo(_dafny.ONE)) {
        return Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m);
      } else if ((new BigNumber((m).length)).isEqualTo(new BigNumber(2))) {
        return Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m);
      } else if ((new BigNumber((m).length)).isEqualTo(new BigNumber(3))) {
        return Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m);
      } else {
        return Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m);
      }
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m) {
      let _207_firstByte = (m)[_dafny.ZERO];
      let _208_x = _207_firstByte;
      return _208_x;
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m) {
      let _209_firstByte = (m)[_dafny.ZERO];
      let _210_secondByte = (m)[_dafny.ONE];
      let _211_y = _dafny.BitwiseAnd(_209_firstByte, new BigNumber(31));
      let _212_x = _dafny.BitwiseAnd(_210_secondByte, new BigNumber(63));
      return _dafny.BitwiseOr((_dafny.ShiftLeft(_211_y, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_212_x));
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m) {
      let _213_firstByte = (m)[_dafny.ZERO];
      let _214_secondByte = (m)[_dafny.ONE];
      let _215_thirdByte = (m)[new BigNumber(2)];
      let _216_z = _dafny.BitwiseAnd(_213_firstByte, new BigNumber(15));
      let _217_y = _dafny.BitwiseAnd(_214_secondByte, new BigNumber(63));
      let _218_x = _dafny.BitwiseAnd(_215_thirdByte, new BigNumber(63));
      return _dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft(_216_z, (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft(_217_y, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_218_x));
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m) {
      let _219_firstByte = (m)[_dafny.ZERO];
      let _220_secondByte = (m)[_dafny.ONE];
      let _221_thirdByte = (m)[new BigNumber(2)];
      let _222_fourthByte = (m)[new BigNumber(3)];
      let _223_u1 = _dafny.BitwiseAnd(_219_firstByte, new BigNumber(7));
      let _224_u2 = (_dafny.ShiftRight(_dafny.BitwiseAnd(_220_secondByte, new BigNumber(48)), (new BigNumber(4)).toNumber())).mod(new BigNumber(2).exponentiatedBy(8));
      let _225_z = _dafny.BitwiseAnd(_220_secondByte, new BigNumber(15));
      let _226_y = _dafny.BitwiseAnd(_221_thirdByte, new BigNumber(63));
      let _227_x = _dafny.BitwiseAnd(_222_fourthByte, new BigNumber(63));
      return _dafny.BitwiseOr(_dafny.BitwiseOr(_dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft(_223_u1, (new BigNumber(18)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft(_224_u2, (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_dafny.ShiftLeft(_225_z, (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_dafny.ShiftLeft(_226_y, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_227_x));
    };
    static PartitionCodeUnitSequenceChecked(s) {
      let maybeParts = Std_Wrappers.Option.Default();
      if (_dafny.areEqual(s, _dafny.Seq.of())) {
        maybeParts = Std_Wrappers.Option.create_Some(_dafny.Seq.of());
        return maybeParts;
      }
      let _228_result;
      _228_result = _dafny.Seq.of();
      let _229_rest;
      _229_rest = s;
      while ((_dafny.ZERO).isLessThan(new BigNumber((_229_rest).length))) {
        let _230_prefix;
        let _231_valueOrError0 = Std_Wrappers.Option.Default();
        _231_valueOrError0 = Std_Unicode_Utf8EncodingForm.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_229_rest);
        if ((_231_valueOrError0).IsFailure()) {
          maybeParts = (_231_valueOrError0).PropagateFailure();
          return maybeParts;
        }
        _230_prefix = (_231_valueOrError0).Extract();
        _228_result = _dafny.Seq.Concat(_228_result, _dafny.Seq.of(_230_prefix));
        _229_rest = (_229_rest).slice(new BigNumber((_230_prefix).length));
      }
      maybeParts = Std_Wrappers.Option.create_Some(_228_result);
      return maybeParts;
      return maybeParts;
    }
    static PartitionCodeUnitSequence(s) {
      return (Std_Unicode_Utf8EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).Extract();
    };
    static IsWellFormedCodeUnitSequence(s) {
      return (Std_Unicode_Utf8EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).is_Some;
    };
    static EncodeScalarSequence(vs) {
      let s = Std_Unicode_Utf8EncodingForm.WellFormedCodeUnitSeq.Default;
      s = _dafny.Seq.of();
      let _lo0 = _dafny.ZERO;
      for (let _232_i = new BigNumber((vs).length); _lo0.isLessThan(_232_i); ) {
        _232_i = _232_i.minus(_dafny.ONE);
        let _233_next;
        _233_next = Std_Unicode_Utf8EncodingForm.__default.EncodeScalarValue((vs)[_232_i]);
        s = _dafny.Seq.Concat(_233_next, s);
      }
      return s;
    }
    static DecodeCodeUnitSequence(s) {
      let _234_parts = Std_Unicode_Utf8EncodingForm.__default.PartitionCodeUnitSequence(s);
      let _235_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _234_parts);
      return _235_vs;
    };
    static DecodeCodeUnitSequenceChecked(s) {
      let maybeVs = Std_Wrappers.Option.Default();
      let _236_maybeParts;
      _236_maybeParts = Std_Unicode_Utf8EncodingForm.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_236_maybeParts).is_None) {
        maybeVs = Std_Wrappers.Option.create_None();
        return maybeVs;
      }
      let _237_parts;
      _237_parts = (_236_maybeParts).dtor_value;
      let _238_vs;
      _238_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _237_parts);
      maybeVs = Std_Wrappers.Option.create_Some(_238_vs);
      return maybeVs;
      return maybeVs;
    }
  };

  $module.WellFormedCodeUnitSeq = class WellFormedCodeUnitSeq {
    constructor () {
    }
    static get Witness() {
      return _dafny.Seq.of();
    }
    static get Default() {
      return Std_Unicode_Utf8EncodingForm.WellFormedCodeUnitSeq.Witness;
    }
  };

  $module.MinimalWellFormedCodeUnitSeq = class MinimalWellFormedCodeUnitSeq {
    constructor () {
    }
    static get Default() {
      return _dafny.Seq.of();
    }
  };
  return $module;
})(); // end of module Std_Unicode_Utf8EncodingForm
let Std_Unicode_Utf16EncodingForm = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Unicode.Utf16EncodingForm._default";
    }
    _parentTraits() {
      return [];
    }
    static IsMinimalWellFormedCodeUnitSubsequence(s) {
      if ((new BigNumber((s).length)).isEqualTo(_dafny.ONE)) {
        return Std_Unicode_Utf16EncodingForm.__default.IsWellFormedSingleCodeUnitSequence(s);
      } else if ((new BigNumber((s).length)).isEqualTo(new BigNumber(2))) {
        let _239_b = Std_Unicode_Utf16EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _239_b;
      } else {
        return false;
      }
    };
    static IsWellFormedSingleCodeUnitSequence(s) {
      let _240_firstWord = (s)[_dafny.ZERO];
      return (((_dafny.ZERO).isLessThanOrEqualTo(_240_firstWord)) && ((_240_firstWord).isLessThanOrEqualTo(new BigNumber(55295)))) || (((new BigNumber(57344)).isLessThanOrEqualTo(_240_firstWord)) && ((_240_firstWord).isLessThanOrEqualTo(new BigNumber(65535))));
    };
    static IsWellFormedDoubleCodeUnitSequence(s) {
      let _241_firstWord = (s)[_dafny.ZERO];
      let _242_secondWord = (s)[_dafny.ONE];
      return (((new BigNumber(55296)).isLessThanOrEqualTo(_241_firstWord)) && ((_241_firstWord).isLessThanOrEqualTo(new BigNumber(56319)))) && (((new BigNumber(56320)).isLessThanOrEqualTo(_242_secondWord)) && ((_242_secondWord).isLessThanOrEqualTo(new BigNumber(57343))));
    };
    static SplitPrefixMinimalWellFormedCodeUnitSubsequence(s) {
      if (((_dafny.ONE).isLessThanOrEqualTo(new BigNumber((s).length))) && (Std_Unicode_Utf16EncodingForm.__default.IsWellFormedSingleCodeUnitSequence((s).slice(0, _dafny.ONE)))) {
        return Std_Wrappers.Option.create_Some((s).slice(0, _dafny.ONE));
      } else if (((new BigNumber(2)).isLessThanOrEqualTo(new BigNumber((s).length))) && (Std_Unicode_Utf16EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence((s).slice(0, new BigNumber(2))))) {
        return Std_Wrappers.Option.create_Some((s).slice(0, new BigNumber(2)));
      } else {
        return Std_Wrappers.Option.create_None();
      }
    };
    static EncodeScalarValue(v) {
      if ((((_dafny.ZERO).isLessThanOrEqualTo(v)) && ((v).isLessThanOrEqualTo(new BigNumber(55295)))) || (((new BigNumber(57344)).isLessThanOrEqualTo(v)) && ((v).isLessThanOrEqualTo(new BigNumber(65535))))) {
        return Std_Unicode_Utf16EncodingForm.__default.EncodeScalarValueSingleWord(v);
      } else {
        return Std_Unicode_Utf16EncodingForm.__default.EncodeScalarValueDoubleWord(v);
      }
    };
    static EncodeScalarValueSingleWord(v) {
      let _243_firstWord = v;
      return _dafny.Seq.of(_243_firstWord);
    };
    static EncodeScalarValueDoubleWord(v) {
      let _244_x2 = _dafny.BitwiseAnd(v, new BigNumber(1023));
      let _245_x1 = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(64512)), (new BigNumber(10)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _246_u = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(2031616)), (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _247_w = ((_246_u).minus(_dafny.ONE)).mod(new BigNumber(2).exponentiatedBy(5));
      let _248_firstWord = _dafny.BitwiseOr(_dafny.BitwiseOr(new BigNumber(55296), (_dafny.ShiftLeft(_247_w, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(16))), _245_x1);
      let _249_secondWord = _dafny.BitwiseOr(new BigNumber(56320), _244_x2);
      return _dafny.Seq.of(_248_firstWord, _249_secondWord);
    };
    static DecodeMinimalWellFormedCodeUnitSubsequence(m) {
      if ((new BigNumber((m).length)).isEqualTo(_dafny.ONE)) {
        return Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m);
      } else {
        return Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m);
      }
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m) {
      let _250_firstWord = (m)[_dafny.ZERO];
      let _251_x = (_250_firstWord);
      return _251_x;
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m) {
      let _252_firstWord = (m)[_dafny.ZERO];
      let _253_secondWord = (m)[_dafny.ONE];
      let _254_x2 = _dafny.BitwiseAnd(_253_secondWord, new BigNumber(1023));
      let _255_x1 = _dafny.BitwiseAnd(_252_firstWord, new BigNumber(63));
      let _256_w = (_dafny.ShiftRight(_dafny.BitwiseAnd(_252_firstWord, new BigNumber(960)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(16));
      let _257_u = (((_256_w).plus(_dafny.ONE)).mod(new BigNumber(2).exponentiatedBy(24)));
      let _258_v = _dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft(_257_u, (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft(_255_x1, (new BigNumber(10)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_254_x2));
      return _258_v;
    };
    static PartitionCodeUnitSequenceChecked(s) {
      let maybeParts = Std_Wrappers.Option.Default();
      if (_dafny.areEqual(s, _dafny.Seq.of())) {
        maybeParts = Std_Wrappers.Option.create_Some(_dafny.Seq.of());
        return maybeParts;
      }
      let _259_result;
      _259_result = _dafny.Seq.of();
      let _260_rest;
      _260_rest = s;
      while ((_dafny.ZERO).isLessThan(new BigNumber((_260_rest).length))) {
        let _261_prefix;
        let _262_valueOrError0 = Std_Wrappers.Option.Default();
        _262_valueOrError0 = Std_Unicode_Utf16EncodingForm.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_260_rest);
        if ((_262_valueOrError0).IsFailure()) {
          maybeParts = (_262_valueOrError0).PropagateFailure();
          return maybeParts;
        }
        _261_prefix = (_262_valueOrError0).Extract();
        _259_result = _dafny.Seq.Concat(_259_result, _dafny.Seq.of(_261_prefix));
        _260_rest = (_260_rest).slice(new BigNumber((_261_prefix).length));
      }
      maybeParts = Std_Wrappers.Option.create_Some(_259_result);
      return maybeParts;
      return maybeParts;
    }
    static PartitionCodeUnitSequence(s) {
      return (Std_Unicode_Utf16EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).Extract();
    };
    static IsWellFormedCodeUnitSequence(s) {
      return (Std_Unicode_Utf16EncodingForm.__default.PartitionCodeUnitSequenceChecked(s)).is_Some;
    };
    static EncodeScalarSequence(vs) {
      let s = Std_Unicode_Utf16EncodingForm.WellFormedCodeUnitSeq.Default;
      s = _dafny.Seq.of();
      let _lo1 = _dafny.ZERO;
      for (let _263_i = new BigNumber((vs).length); _lo1.isLessThan(_263_i); ) {
        _263_i = _263_i.minus(_dafny.ONE);
        let _264_next;
        _264_next = Std_Unicode_Utf16EncodingForm.__default.EncodeScalarValue((vs)[_263_i]);
        s = _dafny.Seq.Concat(_264_next, s);
      }
      return s;
    }
    static DecodeCodeUnitSequence(s) {
      let _265_parts = Std_Unicode_Utf16EncodingForm.__default.PartitionCodeUnitSequence(s);
      let _266_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _265_parts);
      return _266_vs;
    };
    static DecodeCodeUnitSequenceChecked(s) {
      let maybeVs = Std_Wrappers.Option.Default();
      let _267_maybeParts;
      _267_maybeParts = Std_Unicode_Utf16EncodingForm.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_267_maybeParts).is_None) {
        maybeVs = Std_Wrappers.Option.create_None();
        return maybeVs;
      }
      let _268_parts;
      _268_parts = (_267_maybeParts).dtor_value;
      let _269_vs;
      _269_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _268_parts);
      maybeVs = Std_Wrappers.Option.create_Some(_269_vs);
      return maybeVs;
      return maybeVs;
    }
  };

  $module.WellFormedCodeUnitSeq = class WellFormedCodeUnitSeq {
    constructor () {
    }
    static get Witness() {
      return _dafny.Seq.of();
    }
    static get Default() {
      return Std_Unicode_Utf16EncodingForm.WellFormedCodeUnitSeq.Witness;
    }
  };

  $module.MinimalWellFormedCodeUnitSeq = class MinimalWellFormedCodeUnitSeq {
    constructor () {
    }
    static get Default() {
      return _dafny.Seq.of();
    }
  };
  return $module;
})(); // end of module Std_Unicode_Utf16EncodingForm
let Std_Unicode_UnicodeStringsWithUnicodeChar = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Unicode.UnicodeStringsWithUnicodeChar._default";
    }
    _parentTraits() {
      return [];
    }
    static CharAsUnicodeScalarValue(c) {
      return new BigNumber((c).value);
    };
    static CharFromUnicodeScalarValue(sv) {
      return new _dafny.CodePoint((sv).toNumber());
    };
    static ToUTF8Checked(s) {
      let _270_asCodeUnits = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharAsUnicodeScalarValue, s);
      let _271_asUtf8CodeUnits = Std_Unicode_Utf8EncodingForm.__default.EncodeScalarSequence(_270_asCodeUnits);
      let _272_asBytes = Std_Collections_Seq.__default.Map(function (_273_cu) {
        return (_273_cu).toNumber();
      }, _271_asUtf8CodeUnits);
      return Std_Wrappers.Option.create_Some(_272_asBytes);
    };
    static FromUTF8Checked(bs) {
      let _274_asCodeUnits = Std_Collections_Seq.__default.Map(function (_275_c) {
        return new BigNumber(_275_c);
      }, bs);
      let _276_valueOrError0 = Std_Unicode_Utf8EncodingForm.__default.DecodeCodeUnitSequenceChecked(_274_asCodeUnits);
      if ((_276_valueOrError0).IsFailure()) {
        return (_276_valueOrError0).PropagateFailure();
      } else {
        let _277_utf32 = (_276_valueOrError0).Extract();
        let _278_asChars = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharFromUnicodeScalarValue, _277_utf32);
        return Std_Wrappers.Option.create_Some(_278_asChars);
      }
    };
    static ToUTF16Checked(s) {
      let _279_asCodeUnits = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharAsUnicodeScalarValue, s);
      let _280_asUtf16CodeUnits = Std_Unicode_Utf16EncodingForm.__default.EncodeScalarSequence(_279_asCodeUnits);
      let _281_asBytes = Std_Collections_Seq.__default.Map(function (_282_cu) {
        return (_282_cu).toNumber();
      }, _280_asUtf16CodeUnits);
      return Std_Wrappers.Option.create_Some(_281_asBytes);
    };
    static FromUTF16Checked(bs) {
      let _283_asCodeUnits = Std_Collections_Seq.__default.Map(function (_284_c) {
        return new BigNumber(_284_c);
      }, bs);
      let _285_valueOrError0 = Std_Unicode_Utf16EncodingForm.__default.DecodeCodeUnitSequenceChecked(_283_asCodeUnits);
      if ((_285_valueOrError0).IsFailure()) {
        return (_285_valueOrError0).PropagateFailure();
      } else {
        let _286_utf32 = (_285_valueOrError0).Extract();
        let _287_asChars = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharFromUnicodeScalarValue, _286_utf32);
        return Std_Wrappers.Option.create_Some(_287_asChars);
      }
    };
    static ASCIIToUTF8(s) {
      return Std_Collections_Seq.__default.Map(function (_288_c) {
        return (_288_c).value;
      }, s);
    };
    static ASCIIToUTF16(s) {
      return Std_Collections_Seq.__default.Map(function (_289_c) {
        return (_289_c).value;
      }, s);
    };
  };
  return $module;
})(); // end of module Std_Unicode_UnicodeStringsWithUnicodeChar
let Std_Unicode_Utf8EncodingScheme = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.Unicode.Utf8EncodingScheme._default";
    }
    _parentTraits() {
      return [];
    }
    static Serialize(s) {
      return Std_Collections_Seq.__default.Map(function (_290_c) {
        return (_290_c).toNumber();
      }, s);
    };
    static Deserialize(b) {
      return Std_Collections_Seq.__default.Map(function (_291_b) {
        return new BigNumber(_291_b);
      }, b);
    };
  };
  return $module;
})(); // end of module Std_Unicode_Utf8EncodingScheme
let Std_Unicode = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Unicode
let Std_JSON_Values = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Values._default";
    }
    _parentTraits() {
      return [];
    }
    static Int(n) {
      return Std_JSON_Values.Decimal.create_Decimal(n, _dafny.ZERO);
    };
  };

  $module.Decimal = class Decimal {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Decimal(n, e10) {
      let $dt = new Decimal(0);
      $dt.n = n;
      $dt.e10 = e10;
      return $dt;
    }
    get is_Decimal() { return this.$tag === 0; }
    get dtor_n() { return this.n; }
    get dtor_e10() { return this.e10; }
    toString() {
      if (this.$tag === 0) {
        return "Values.Decimal.Decimal" + "(" + _dafny.toString(this.n) + ", " + _dafny.toString(this.e10) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.n, other.n) && _dafny.areEqual(this.e10, other.e10);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Values.Decimal.create_Decimal(_dafny.ZERO, _dafny.ZERO);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Decimal.Default();
        }
      };
    }
  }

  $module.JSON = class JSON {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Null() {
      let $dt = new JSON(0);
      return $dt;
    }
    static create_Bool(b) {
      let $dt = new JSON(1);
      $dt.b = b;
      return $dt;
    }
    static create_String(str) {
      let $dt = new JSON(2);
      $dt.str = str;
      return $dt;
    }
    static create_Number(num) {
      let $dt = new JSON(3);
      $dt.num = num;
      return $dt;
    }
    static create_Object(obj) {
      let $dt = new JSON(4);
      $dt.obj = obj;
      return $dt;
    }
    static create_Array(arr) {
      let $dt = new JSON(5);
      $dt.arr = arr;
      return $dt;
    }
    get is_Null() { return this.$tag === 0; }
    get is_Bool() { return this.$tag === 1; }
    get is_String() { return this.$tag === 2; }
    get is_Number() { return this.$tag === 3; }
    get is_Object() { return this.$tag === 4; }
    get is_Array() { return this.$tag === 5; }
    get dtor_b() { return this.b; }
    get dtor_str() { return this.str; }
    get dtor_num() { return this.num; }
    get dtor_obj() { return this.obj; }
    get dtor_arr() { return this.arr; }
    toString() {
      if (this.$tag === 0) {
        return "Values.JSON.Null";
      } else if (this.$tag === 1) {
        return "Values.JSON.Bool" + "(" + _dafny.toString(this.b) + ")";
      } else if (this.$tag === 2) {
        return "Values.JSON.String" + "(" + this.str.toVerbatimString(true) + ")";
      } else if (this.$tag === 3) {
        return "Values.JSON.Number" + "(" + _dafny.toString(this.num) + ")";
      } else if (this.$tag === 4) {
        return "Values.JSON.Object" + "(" + _dafny.toString(this.obj) + ")";
      } else if (this.$tag === 5) {
        return "Values.JSON.Array" + "(" + _dafny.toString(this.arr) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && this.b === other.b;
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.str, other.str);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.num, other.num);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.obj, other.obj);
      } else if (this.$tag === 5) {
        return other.$tag === 5 && _dafny.areEqual(this.arr, other.arr);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Values.JSON.create_Null();
    }
    static Rtd() {
      return class {
        static get Default() {
          return JSON.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module Std_JSON_Values
let Std_JSON_Errors = (function() {
  let $module = {};


  $module.DeserializationError = class DeserializationError {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_UnterminatedSequence() {
      let $dt = new DeserializationError(0);
      return $dt;
    }
    static create_UnsupportedEscape(str) {
      let $dt = new DeserializationError(1);
      $dt.str = str;
      return $dt;
    }
    static create_EscapeAtEOS() {
      let $dt = new DeserializationError(2);
      return $dt;
    }
    static create_EmptyNumber() {
      let $dt = new DeserializationError(3);
      return $dt;
    }
    static create_ExpectingEOF() {
      let $dt = new DeserializationError(4);
      return $dt;
    }
    static create_IntOverflow() {
      let $dt = new DeserializationError(5);
      return $dt;
    }
    static create_ReachedEOF() {
      let $dt = new DeserializationError(6);
      return $dt;
    }
    static create_ExpectingByte(expected, b) {
      let $dt = new DeserializationError(7);
      $dt.expected = expected;
      $dt.b = b;
      return $dt;
    }
    static create_ExpectingAnyByte(expected__sq, b) {
      let $dt = new DeserializationError(8);
      $dt.expected__sq = expected__sq;
      $dt.b = b;
      return $dt;
    }
    static create_InvalidUnicode() {
      let $dt = new DeserializationError(9);
      return $dt;
    }
    get is_UnterminatedSequence() { return this.$tag === 0; }
    get is_UnsupportedEscape() { return this.$tag === 1; }
    get is_EscapeAtEOS() { return this.$tag === 2; }
    get is_EmptyNumber() { return this.$tag === 3; }
    get is_ExpectingEOF() { return this.$tag === 4; }
    get is_IntOverflow() { return this.$tag === 5; }
    get is_ReachedEOF() { return this.$tag === 6; }
    get is_ExpectingByte() { return this.$tag === 7; }
    get is_ExpectingAnyByte() { return this.$tag === 8; }
    get is_InvalidUnicode() { return this.$tag === 9; }
    get dtor_str() { return this.str; }
    get dtor_expected() { return this.expected; }
    get dtor_b() { return this.b; }
    get dtor_expected__sq() { return this.expected__sq; }
    toString() {
      if (this.$tag === 0) {
        return "Errors.DeserializationError.UnterminatedSequence";
      } else if (this.$tag === 1) {
        return "Errors.DeserializationError.UnsupportedEscape" + "(" + this.str.toVerbatimString(true) + ")";
      } else if (this.$tag === 2) {
        return "Errors.DeserializationError.EscapeAtEOS";
      } else if (this.$tag === 3) {
        return "Errors.DeserializationError.EmptyNumber";
      } else if (this.$tag === 4) {
        return "Errors.DeserializationError.ExpectingEOF";
      } else if (this.$tag === 5) {
        return "Errors.DeserializationError.IntOverflow";
      } else if (this.$tag === 6) {
        return "Errors.DeserializationError.ReachedEOF";
      } else if (this.$tag === 7) {
        return "Errors.DeserializationError.ExpectingByte" + "(" + _dafny.toString(this.expected) + ", " + _dafny.toString(this.b) + ")";
      } else if (this.$tag === 8) {
        return "Errors.DeserializationError.ExpectingAnyByte" + "(" + _dafny.toString(this.expected__sq) + ", " + _dafny.toString(this.b) + ")";
      } else if (this.$tag === 9) {
        return "Errors.DeserializationError.InvalidUnicode";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.str, other.str);
      } else if (this.$tag === 2) {
        return other.$tag === 2;
      } else if (this.$tag === 3) {
        return other.$tag === 3;
      } else if (this.$tag === 4) {
        return other.$tag === 4;
      } else if (this.$tag === 5) {
        return other.$tag === 5;
      } else if (this.$tag === 6) {
        return other.$tag === 6;
      } else if (this.$tag === 7) {
        return other.$tag === 7 && this.expected === other.expected && this.b === other.b;
      } else if (this.$tag === 8) {
        return other.$tag === 8 && _dafny.areEqual(this.expected__sq, other.expected__sq) && this.b === other.b;
      } else if (this.$tag === 9) {
        return other.$tag === 9;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Errors.DeserializationError.create_UnterminatedSequence();
    }
    static Rtd() {
      return class {
        static get Default() {
          return DeserializationError.Default();
        }
      };
    }
    ToString() {
      let _this = this;
      let _source10 = _this;
      if (_source10.is_UnterminatedSequence) {
        return _dafny.Seq.UnicodeFromString("Unterminated sequence");
      } else if (_source10.is_UnsupportedEscape) {
        let _292___mcc_h0 = (_source10).str;
        let _293_str = _292___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Unsupported escape sequence: "), _293_str);
      } else if (_source10.is_EscapeAtEOS) {
        return _dafny.Seq.UnicodeFromString("Escape character at end of string");
      } else if (_source10.is_EmptyNumber) {
        return _dafny.Seq.UnicodeFromString("Number must contain at least one digit");
      } else if (_source10.is_ExpectingEOF) {
        return _dafny.Seq.UnicodeFromString("Expecting EOF");
      } else if (_source10.is_IntOverflow) {
        return _dafny.Seq.UnicodeFromString("Input length does not fit in a 32-bit counter");
      } else if (_source10.is_ReachedEOF) {
        return _dafny.Seq.UnicodeFromString("Reached EOF");
      } else if (_source10.is_ExpectingByte) {
        let _294___mcc_h1 = (_source10).expected;
        let _295___mcc_h2 = (_source10).b;
        let _296_b = _295___mcc_h2;
        let _297_b0 = _294___mcc_h1;
        let _298_c = (((_296_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_296_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting '"), _dafny.Seq.of(new _dafny.CodePoint((_297_b0)))), _dafny.Seq.UnicodeFromString("', read ")), _298_c);
      } else if (_source10.is_ExpectingAnyByte) {
        let _299___mcc_h3 = (_source10).expected__sq;
        let _300___mcc_h4 = (_source10).b;
        let _301_b = _300___mcc_h4;
        let _302_bs0 = _299___mcc_h3;
        let _303_c = (((_301_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_301_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        let _304_c0s = _dafny.Seq.Create(new BigNumber((_302_bs0).length), ((_305_bs0) => function (_306_idx) {
          return new _dafny.CodePoint(((_305_bs0)[_306_idx]));
        })(_302_bs0));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting one of '"), _304_c0s), _dafny.Seq.UnicodeFromString("', read ")), _303_c);
      } else {
        return _dafny.Seq.UnicodeFromString("Invalid Unicode sequence");
      }
    };
  }

  $module.SerializationError = class SerializationError {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_OutOfMemory() {
      let $dt = new SerializationError(0);
      return $dt;
    }
    static create_IntTooLarge(i) {
      let $dt = new SerializationError(1);
      $dt.i = i;
      return $dt;
    }
    static create_StringTooLong(s) {
      let $dt = new SerializationError(2);
      $dt.s = s;
      return $dt;
    }
    static create_InvalidUnicode() {
      let $dt = new SerializationError(3);
      return $dt;
    }
    get is_OutOfMemory() { return this.$tag === 0; }
    get is_IntTooLarge() { return this.$tag === 1; }
    get is_StringTooLong() { return this.$tag === 2; }
    get is_InvalidUnicode() { return this.$tag === 3; }
    get dtor_i() { return this.i; }
    get dtor_s() { return this.s; }
    toString() {
      if (this.$tag === 0) {
        return "Errors.SerializationError.OutOfMemory";
      } else if (this.$tag === 1) {
        return "Errors.SerializationError.IntTooLarge" + "(" + _dafny.toString(this.i) + ")";
      } else if (this.$tag === 2) {
        return "Errors.SerializationError.StringTooLong" + "(" + this.s.toVerbatimString(true) + ")";
      } else if (this.$tag === 3) {
        return "Errors.SerializationError.InvalidUnicode";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.i, other.i);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.s, other.s);
      } else if (this.$tag === 3) {
        return other.$tag === 3;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Errors.SerializationError.create_OutOfMemory();
    }
    static Rtd() {
      return class {
        static get Default() {
          return SerializationError.Default();
        }
      };
    }
    ToString() {
      let _this = this;
      let _source11 = _this;
      if (_source11.is_OutOfMemory) {
        return _dafny.Seq.UnicodeFromString("Out of memory");
      } else if (_source11.is_IntTooLarge) {
        let _307___mcc_h0 = (_source11).i;
        let _308_i = _307___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Integer too large: "), Std_Strings.__default.OfInt(_308_i));
      } else if (_source11.is_StringTooLong) {
        let _309___mcc_h1 = (_source11).s;
        let _310_s = _309___mcc_h1;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("String too long: "), _310_s);
      } else {
        return _dafny.Seq.UnicodeFromString("Invalid Unicode sequence");
      }
    };
  }
  return $module;
})(); // end of module Std_JSON_Errors
let Std_JSON_Spec = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Spec._default";
    }
    _parentTraits() {
      return [];
    }
    static EscapeUnicode(c) {
      let _311_sStr = Std_Strings_HexConversion.__default.OfNat(new BigNumber(c));
      let _312_s = Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_311_sStr);
      return _dafny.Seq.Concat(_312_s, _dafny.Seq.Create((new BigNumber(4)).minus(new BigNumber((_312_s).length)), function (_313___v8) {
        return (new _dafny.CodePoint(' '.codePointAt(0))).value;
      }));
    };
    static Escape(str, start) {
      let _314___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _pat_let_tv0 = str;
        let _pat_let_tv1 = start;
        if ((new BigNumber((str).length)).isLessThanOrEqualTo(start)) {
          return _dafny.Seq.Concat(_314___accumulator, _dafny.Seq.of());
        } else {
          _314___accumulator = _dafny.Seq.Concat(_314___accumulator, ((((str)[start]) === (34)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\\""))) : (((((str)[start]) === (92)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\\\"))) : (((((str)[start]) === (8)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\b"))) : (((((str)[start]) === (12)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\f"))) : (((((str)[start]) === (10)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\n"))) : (((((str)[start]) === (13)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\r"))) : (((((str)[start]) === (9)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\t"))) : (function (_pat_let1_0) {
            return function (_315_c) {
              return (((_315_c) < (31)) ? (_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\u")), Std_JSON_Spec.__default.EscapeUnicode(_315_c))) : (_dafny.Seq.of((_pat_let_tv0)[_pat_let_tv1])));
            }(_pat_let1_0);
          }((str)[start]))))))))))))))));
          let _in62 = str;
          let _in63 = (start).plus(_dafny.ONE);
          str = _in62;
          start = _in63;
          continue TAIL_CALL_START;
        }
      }
    };
    static EscapeToUTF8(str, start) {
      let _316_valueOrError0 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(str)).ToResult(Std_JSON_Errors.SerializationError.create_InvalidUnicode());
      if ((_316_valueOrError0).IsFailure()) {
        return (_316_valueOrError0).PropagateFailure();
      } else {
        let _317_utf16 = (_316_valueOrError0).Extract();
        let _318_escaped = Std_JSON_Spec.__default.Escape(_317_utf16, _dafny.ZERO);
        let _319_valueOrError1 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_318_escaped)).ToResult(Std_JSON_Errors.SerializationError.create_InvalidUnicode());
        if ((_319_valueOrError1).IsFailure()) {
          return (_319_valueOrError1).PropagateFailure();
        } else {
          let _320_utf32 = (_319_valueOrError1).Extract();
          return (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ToUTF8Checked(_320_utf32)).ToResult(Std_JSON_Errors.SerializationError.create_InvalidUnicode());
        }
      }
    };
    static String(str) {
      let _321_valueOrError0 = Std_JSON_Spec.__default.EscapeToUTF8(str, _dafny.ZERO);
      if ((_321_valueOrError0).IsFailure()) {
        return (_321_valueOrError0).PropagateFailure();
      } else {
        let _322_inBytes = (_321_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("\"")), _322_inBytes), Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("\""))));
      }
    };
    static IntToBytes(n) {
      let _323_s = Std_Strings.__default.OfInt(n);
      return Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_323_s);
    };
    static Number(dec) {
      return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(Std_JSON_Spec.__default.IntToBytes((dec).dtor_n), ((((dec).dtor_e10).isEqualTo(_dafny.ZERO)) ? (_dafny.Seq.of()) : (_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("e")), Std_JSON_Spec.__default.IntToBytes((dec).dtor_e10))))));
    };
    static KeyValue(kv) {
      let _324_valueOrError0 = Std_JSON_Spec.__default.String((kv)[0]);
      if ((_324_valueOrError0).IsFailure()) {
        return (_324_valueOrError0).PropagateFailure();
      } else {
        let _325_key = (_324_valueOrError0).Extract();
        let _326_valueOrError1 = Std_JSON_Spec.__default.JSON((kv)[1]);
        if ((_326_valueOrError1).IsFailure()) {
          return (_326_valueOrError1).PropagateFailure();
        } else {
          let _327_value = (_326_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(_325_key, Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString(":"))), _327_value));
        }
      }
    };
    static Join(sep, items) {
      if ((new BigNumber((items).length)).isEqualTo(_dafny.ZERO)) {
        return Std_Wrappers.Result.create_Success(_dafny.Seq.of());
      } else {
        let _328_valueOrError0 = (items)[_dafny.ZERO];
        if ((_328_valueOrError0).IsFailure()) {
          return (_328_valueOrError0).PropagateFailure();
        } else {
          let _329_first = (_328_valueOrError0).Extract();
          if ((new BigNumber((items).length)).isEqualTo(_dafny.ONE)) {
            return Std_Wrappers.Result.create_Success(_329_first);
          } else {
            let _330_valueOrError1 = Std_JSON_Spec.__default.Join(sep, (items).slice(_dafny.ONE));
            if ((_330_valueOrError1).IsFailure()) {
              return (_330_valueOrError1).PropagateFailure();
            } else {
              let _331_rest = (_330_valueOrError1).Extract();
              return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(_329_first, sep), _331_rest));
            }
          }
        }
      }
    };
    static Object(obj) {
      let _332_valueOrError0 = Std_JSON_Spec.__default.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString(",")), _dafny.Seq.Create(new BigNumber((obj).length), ((_333_obj) => function (_334_i) {
        return Std_JSON_Spec.__default.KeyValue((_333_obj)[_334_i]);
      })(obj)));
      if ((_332_valueOrError0).IsFailure()) {
        return (_332_valueOrError0).PropagateFailure();
      } else {
        let _335_middle = (_332_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("{")), _335_middle), Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("}"))));
      }
    };
    static Array(arr) {
      let _336_valueOrError0 = Std_JSON_Spec.__default.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString(",")), _dafny.Seq.Create(new BigNumber((arr).length), ((_337_arr) => function (_338_i) {
        return Std_JSON_Spec.__default.JSON((_337_arr)[_338_i]);
      })(arr)));
      if ((_336_valueOrError0).IsFailure()) {
        return (_336_valueOrError0).PropagateFailure();
      } else {
        let _339_middle = (_336_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("[")), _339_middle), Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("]"))));
      }
    };
    static JSON(js) {
      let _source12 = js;
      if (_source12.is_Null) {
        return Std_Wrappers.Result.create_Success(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("null")));
      } else if (_source12.is_Bool) {
        let _340___mcc_h0 = (_source12).b;
        let _341_b = _340___mcc_h0;
        return Std_Wrappers.Result.create_Success(((_341_b) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("true"))) : (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("false")))));
      } else if (_source12.is_String) {
        let _342___mcc_h1 = (_source12).str;
        let _343_str = _342___mcc_h1;
        return Std_JSON_Spec.__default.String(_343_str);
      } else if (_source12.is_Number) {
        let _344___mcc_h2 = (_source12).num;
        let _345_dec = _344___mcc_h2;
        return Std_JSON_Spec.__default.Number(_345_dec);
      } else if (_source12.is_Object) {
        let _346___mcc_h3 = (_source12).obj;
        let _347_obj = _346___mcc_h3;
        return Std_JSON_Spec.__default.Object(_347_obj);
      } else {
        let _348___mcc_h4 = (_source12).arr;
        let _349_arr = _348___mcc_h4;
        return Std_JSON_Spec.__default.Array(_349_arr);
      }
    };
  };
  return $module;
})(); // end of module Std_JSON_Spec
let Std_JSON_Utils_Views_Core = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Utils.Views.Core._default";
    }
    _parentTraits() {
      return [];
    }
    static Adjacent(lv, rv) {
      return (((lv).dtor_end) === ((rv).dtor_beg)) && (_dafny.areEqual((lv).dtor_s, (rv).dtor_s));
    };
    static Merge(lv, rv) {
      let _350_dt__update__tmp_h0 = lv;
      let _351_dt__update_hend_h0 = (rv).dtor_end;
      return Std_JSON_Utils_Views_Core.View__.create_View((_350_dt__update__tmp_h0).dtor_s, (_350_dt__update__tmp_h0).dtor_beg, _351_dt__update_hend_h0);
    };
  };

  $module.View = class View {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.create_View(_dafny.Seq.of(), 0, 0);
    }
    static get Default() {
      return Std_JSON_Utils_Views_Core.View.Witness;
    }
  };

  $module.View__ = class View__ {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_View(s, beg, end) {
      let $dt = new View__(0);
      $dt.s = s;
      $dt.beg = beg;
      $dt.end = end;
      return $dt;
    }
    get is_View() { return this.$tag === 0; }
    get dtor_s() { return this.s; }
    get dtor_beg() { return this.beg; }
    get dtor_end() { return this.end; }
    toString() {
      if (this.$tag === 0) {
        return "Core.View_.View" + "(" + _dafny.toString(this.s) + ", " + _dafny.toString(this.beg) + ", " + _dafny.toString(this.end) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.s, other.s) && this.beg === other.beg && this.end === other.end;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Utils_Views_Core.View__.create_View(_dafny.Seq.of(), 0, 0);
    }
    static Rtd() {
      return class {
        static get Default() {
          return View__.Default();
        }
      };
    }
    Length() {
      let _this = this;
      return ((_this).dtor_end) - ((_this).dtor_beg);
    };
    Bytes() {
      let _this = this;
      return ((_this).dtor_s).slice((_this).dtor_beg, (_this).dtor_end);
    };
    static OfBytes(bs) {
      return Std_JSON_Utils_Views_Core.View__.create_View(bs, (0), (bs).length);
    };
    static OfString(s) {
      return _dafny.Seq.Create(new BigNumber((s).length), ((_352_s) => function (_353_i) {
        return ((_352_s)[_353_i]).value;
      })(s));
    };
    Byte_q(c) {
      let _this = this;
      let _hresult = false;
      _hresult = (((_this).Length()) === (1)) && (((_this).At(0)) === (c));
      return _hresult;
      return _hresult;
    }
    Char_q(c) {
      let _this = this;
      return (_this).Byte_q((c).value);
    };
    At(idx) {
      let _this = this;
      return ((_this).dtor_s)[((_this).dtor_beg) + (idx)];
    };
    Peek() {
      let _this = this;
      if ((_this).Empty_q) {
        return -1;
      } else {
        return (_this).At(0);
      }
    };
    CopyTo(dest, start) {
      let _this = this;
      let _hi0 = (_this).Length();
      for (let _354_idx = 0; _354_idx < _hi0; _354_idx++) {
        let _index6 = (start) + (_354_idx);
        (dest)[_index6] = ((_this).dtor_s)[((_this).dtor_beg) + (_354_idx)];
      }
      return;
    }
    static get Empty() {
      return Std_JSON_Utils_Views_Core.View__.create_View(_dafny.Seq.of(), 0, 0);
    };
    get Empty_q() {
      let _this = this;
      return ((_this).dtor_beg) === ((_this).dtor_end);
    };
  }
  return $module;
})(); // end of module Std_JSON_Utils_Views_Core
let Std_JSON_Utils_Views_Writers = (function() {
  let $module = {};


  $module.Chain = class Chain {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Empty() {
      let $dt = new Chain(0);
      return $dt;
    }
    static create_Chain(previous, v) {
      let $dt = new Chain(1);
      $dt.previous = previous;
      $dt.v = v;
      return $dt;
    }
    get is_Empty() { return this.$tag === 0; }
    get is_Chain() { return this.$tag === 1; }
    get dtor_previous() { return this.previous; }
    get dtor_v() { return this.v; }
    toString() {
      if (this.$tag === 0) {
        return "Writers.Chain.Empty";
      } else if (this.$tag === 1) {
        return "Writers.Chain.Chain" + "(" + _dafny.toString(this.previous) + ", " + _dafny.toString(this.v) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.previous, other.previous) && _dafny.areEqual(this.v, other.v);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Utils_Views_Writers.Chain.create_Empty();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Chain.Default();
        }
      };
    }
    Length() {
      let _this = this;
      let _355___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((_this).is_Empty) {
          return (_dafny.ZERO).plus(_355___accumulator);
        } else {
          _355___accumulator = (new BigNumber(((_this).dtor_v).Length())).plus(_355___accumulator);
          let _in64 = (_this).dtor_previous;
          _this = _in64;
          ;
          continue TAIL_CALL_START;
        }
      }
    };
    Count() {
      let _this = this;
      let _356___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((_this).is_Empty) {
          return (_dafny.ZERO).plus(_356___accumulator);
        } else {
          _356___accumulator = (_dafny.ONE).plus(_356___accumulator);
          let _in65 = (_this).dtor_previous;
          _this = _in65;
          ;
          continue TAIL_CALL_START;
        }
      }
    };
    Bytes() {
      let _this = this;
      let _357___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((_this).is_Empty) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _357___accumulator);
        } else {
          _357___accumulator = _dafny.Seq.Concat(((_this).dtor_v).Bytes(), _357___accumulator);
          let _in66 = (_this).dtor_previous;
          _this = _in66;
          ;
          continue TAIL_CALL_START;
        }
      }
    };
    Append(v_k) {
      let _this = this;
      if (((_this).is_Chain) && (Std_JSON_Utils_Views_Core.__default.Adjacent((_this).dtor_v, v_k))) {
        return Std_JSON_Utils_Views_Writers.Chain.create_Chain((_this).dtor_previous, Std_JSON_Utils_Views_Core.__default.Merge((_this).dtor_v, v_k));
      } else {
        return Std_JSON_Utils_Views_Writers.Chain.create_Chain(_this, v_k);
      }
    };
    CopyTo(dest, end) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((_this).is_Chain) {
          let _358_end;
          _358_end = (end) - (((_this).dtor_v).Length());
          ((_this).dtor_v).CopyTo(dest, _358_end);
          let _in67 = (_this).dtor_previous;
          let _in68 = dest;
          let _in69 = _358_end;
          _this = _in67;
          ;
          dest = _in68;
          end = _in69;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
  }

  $module.Writer = class Writer {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Writers.Writer__.create_Writer(0, Std_JSON_Utils_Views_Writers.Chain.create_Empty());
    }
    static get Default() {
      return Std_JSON_Utils_Views_Writers.Writer.Witness;
    }
  };

  $module.Writer__ = class Writer__ {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Writer(length, chain) {
      let $dt = new Writer__(0);
      $dt.length = length;
      $dt.chain = chain;
      return $dt;
    }
    get is_Writer() { return this.$tag === 0; }
    get dtor_length() { return this.length; }
    get dtor_chain() { return this.chain; }
    toString() {
      if (this.$tag === 0) {
        return "Writers.Writer_.Writer" + "(" + _dafny.toString(this.length) + ", " + _dafny.toString(this.chain) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && this.length === other.length && _dafny.areEqual(this.chain, other.chain);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Utils_Views_Writers.Writer__.create_Writer(0, Std_JSON_Utils_Views_Writers.Chain.Default());
    }
    static Rtd() {
      return class {
        static get Default() {
          return Writer__.Default();
        }
      };
    }
    Bytes() {
      let _this = this;
      return ((_this).dtor_chain).Bytes();
    };
    static SaturatedAddU32(a, b) {
      if ((a) <= ((Std_BoundedInts.__default.UINT32__MAX) - (b))) {
        return (a) + (b);
      } else {
        return Std_BoundedInts.__default.UINT32__MAX;
      }
    };
    Append(v_k) {
      let _this = this;
      return Std_JSON_Utils_Views_Writers.Writer__.create_Writer(Std_JSON_Utils_Views_Writers.Writer__.SaturatedAddU32((_this).dtor_length, (v_k).Length()), ((_this).dtor_chain).Append(v_k));
    };
    Then(fn) {
      let _this = this;
      return (fn)(_this);
    };
    CopyTo(dest) {
      let _this = this;
      ((_this).dtor_chain).CopyTo(dest, (_this).dtor_length);
      return;
    }
    ToArray() {
      let _this = this;
      let bs = [];
      let _init4 = function (_359_i) {
        return 0;
      };
      let _nw5 = Array((BigNumber((_this).dtor_length)).toNumber());
      for (let _i0_4 = 0; _i0_4 < new BigNumber(_nw5.length); _i0_4++) {
        _nw5[_i0_4] = _init4(new BigNumber(_i0_4));
      }
      bs = _nw5;
      (_this).CopyTo(bs);
      return bs;
    }
    static get Empty() {
      return Std_JSON_Utils_Views_Writers.Writer__.create_Writer(0, Std_JSON_Utils_Views_Writers.Chain.create_Empty());
    };
    get Unsaturated_q() {
      let _this = this;
      return ((_this).dtor_length) !== (Std_BoundedInts.__default.UINT32__MAX);
    };
    get Empty_q() {
      let _this = this;
      return ((_this).dtor_chain).is_Empty;
    };
  }
  return $module;
})(); // end of module Std_JSON_Utils_Views_Writers
let Std_JSON_Utils_Views = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON_Utils_Views
let Std_JSON_Utils_Lexers_Core = (function() {
  let $module = {};


  $module.LexerResult = class LexerResult {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Accept() {
      let $dt = new LexerResult(0);
      return $dt;
    }
    static create_Reject(err) {
      let $dt = new LexerResult(1);
      $dt.err = err;
      return $dt;
    }
    static create_Partial(st) {
      let $dt = new LexerResult(2);
      $dt.st = st;
      return $dt;
    }
    get is_Accept() { return this.$tag === 0; }
    get is_Reject() { return this.$tag === 1; }
    get is_Partial() { return this.$tag === 2; }
    get dtor_err() { return this.err; }
    get dtor_st() { return this.st; }
    toString() {
      if (this.$tag === 0) {
        return "Core.LexerResult.Accept";
      } else if (this.$tag === 1) {
        return "Core.LexerResult.Reject" + "(" + _dafny.toString(this.err) + ")";
      } else if (this.$tag === 2) {
        return "Core.LexerResult.Partial" + "(" + _dafny.toString(this.st) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.err, other.err);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.st, other.st);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Utils_Lexers_Core.LexerResult.create_Accept();
    }
    static Rtd() {
      return class {
        static get Default() {
          return LexerResult.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module Std_JSON_Utils_Lexers_Core
let Std_JSON_Utils_Lexers_Strings = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Utils.Lexers.Strings._default";
    }
    _parentTraits() {
      return [];
    }
    static StringBody(escaped, _$$_byte) {
      if ((_$$_byte) === ((new _dafny.CodePoint('\\'.codePointAt(0))).value)) {
        return Std_JSON_Utils_Lexers_Core.LexerResult.create_Partial(!(escaped));
      } else if (((_$$_byte) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) && (!(escaped))) {
        return Std_JSON_Utils_Lexers_Core.LexerResult.create_Accept();
      } else {
        return Std_JSON_Utils_Lexers_Core.LexerResult.create_Partial(false);
      }
    };
    static String(st, _$$_byte) {
      let _source13 = st;
      if (_source13.is_Start) {
        if ((_$$_byte) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) {
          return Std_JSON_Utils_Lexers_Core.LexerResult.create_Partial(Std_JSON_Utils_Lexers_Strings.StringLexerState.create_Body(false));
        } else {
          return Std_JSON_Utils_Lexers_Core.LexerResult.create_Reject(_dafny.Seq.UnicodeFromString("String must start with double quote"));
        }
      } else if (_source13.is_Body) {
        let _360___mcc_h0 = (_source13).escaped;
        let _361_escaped = _360___mcc_h0;
        if ((_$$_byte) === ((new _dafny.CodePoint('\\'.codePointAt(0))).value)) {
          return Std_JSON_Utils_Lexers_Core.LexerResult.create_Partial(Std_JSON_Utils_Lexers_Strings.StringLexerState.create_Body(!(_361_escaped)));
        } else if (((_$$_byte) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) && (!(_361_escaped))) {
          return Std_JSON_Utils_Lexers_Core.LexerResult.create_Partial(Std_JSON_Utils_Lexers_Strings.StringLexerState.create_End());
        } else {
          return Std_JSON_Utils_Lexers_Core.LexerResult.create_Partial(Std_JSON_Utils_Lexers_Strings.StringLexerState.create_Body(false));
        }
      } else {
        return Std_JSON_Utils_Lexers_Core.LexerResult.create_Accept();
      }
    };
    static get StringBodyLexerStart() {
      return false;
    };
    static get StringLexerStart() {
      return Std_JSON_Utils_Lexers_Strings.StringLexerState.create_Start();
    };
  };

  $module.StringLexerState = class StringLexerState {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Start() {
      let $dt = new StringLexerState(0);
      return $dt;
    }
    static create_Body(escaped) {
      let $dt = new StringLexerState(1);
      $dt.escaped = escaped;
      return $dt;
    }
    static create_End() {
      let $dt = new StringLexerState(2);
      return $dt;
    }
    get is_Start() { return this.$tag === 0; }
    get is_Body() { return this.$tag === 1; }
    get is_End() { return this.$tag === 2; }
    get dtor_escaped() { return this.escaped; }
    toString() {
      if (this.$tag === 0) {
        return "Strings.StringLexerState.Start";
      } else if (this.$tag === 1) {
        return "Strings.StringLexerState.Body" + "(" + _dafny.toString(this.escaped) + ")";
      } else if (this.$tag === 2) {
        return "Strings.StringLexerState.End";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && this.escaped === other.escaped;
      } else if (this.$tag === 2) {
        return other.$tag === 2;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Utils_Lexers_Strings.StringLexerState.create_Start();
    }
    static Rtd() {
      return class {
        static get Default() {
          return StringLexerState.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module Std_JSON_Utils_Lexers_Strings
let Std_JSON_Utils_Lexers = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON_Utils_Lexers
let Std_JSON_Utils_Cursors = (function() {
  let $module = {};


  $module.Split = class Split {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_SP(t, cs) {
      let $dt = new Split(0);
      $dt.t = t;
      $dt.cs = cs;
      return $dt;
    }
    get is_SP() { return this.$tag === 0; }
    get dtor_t() { return this.t; }
    get dtor_cs() { return this.cs; }
    toString() {
      if (this.$tag === 0) {
        return "Cursors.Split.SP" + "(" + _dafny.toString(this.t) + ", " + _dafny.toString(this.cs) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.t, other.t) && _dafny.areEqual(this.cs, other.cs);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_T) {
      return Std_JSON_Utils_Cursors.Split.create_SP(_default_T, Std_JSON_Utils_Cursors.FreshCursor.Default);
    }
    static Rtd(rtd$_T) {
      return class {
        static get Default() {
          return Split.Default(rtd$_T.Default);
        }
      };
    }
  }

  $module.Cursor = class Cursor {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor(_dafny.Seq.of(), 0, 0, 0);
    }
    static get Default() {
      return Std_JSON_Utils_Cursors.Cursor.Witness;
    }
  };

  $module.FreshCursor = class FreshCursor {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor(_dafny.Seq.of(), 0, 0, 0);
    }
    static get Default() {
      return Std_JSON_Utils_Cursors.FreshCursor.Witness;
    }
  };

  $module.CursorError = class CursorError {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_EOF() {
      let $dt = new CursorError(0);
      return $dt;
    }
    static create_ExpectingByte(expected, b) {
      let $dt = new CursorError(1);
      $dt.expected = expected;
      $dt.b = b;
      return $dt;
    }
    static create_ExpectingAnyByte(expected__sq, b) {
      let $dt = new CursorError(2);
      $dt.expected__sq = expected__sq;
      $dt.b = b;
      return $dt;
    }
    static create_OtherError(err) {
      let $dt = new CursorError(3);
      $dt.err = err;
      return $dt;
    }
    get is_EOF() { return this.$tag === 0; }
    get is_ExpectingByte() { return this.$tag === 1; }
    get is_ExpectingAnyByte() { return this.$tag === 2; }
    get is_OtherError() { return this.$tag === 3; }
    get dtor_expected() { return this.expected; }
    get dtor_b() { return this.b; }
    get dtor_expected__sq() { return this.expected__sq; }
    get dtor_err() { return this.err; }
    toString() {
      if (this.$tag === 0) {
        return "Cursors.CursorError.EOF";
      } else if (this.$tag === 1) {
        return "Cursors.CursorError.ExpectingByte" + "(" + _dafny.toString(this.expected) + ", " + _dafny.toString(this.b) + ")";
      } else if (this.$tag === 2) {
        return "Cursors.CursorError.ExpectingAnyByte" + "(" + _dafny.toString(this.expected__sq) + ", " + _dafny.toString(this.b) + ")";
      } else if (this.$tag === 3) {
        return "Cursors.CursorError.OtherError" + "(" + _dafny.toString(this.err) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && this.expected === other.expected && this.b === other.b;
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.expected__sq, other.expected__sq) && this.b === other.b;
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.err, other.err);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Utils_Cursors.CursorError.create_EOF();
    }
    static Rtd() {
      return class {
        static get Default() {
          return CursorError.Default();
        }
      };
    }
    ToString(pr) {
      let _this = this;
      let _source14 = _this;
      if (_source14.is_EOF) {
        return _dafny.Seq.UnicodeFromString("Reached EOF");
      } else if (_source14.is_ExpectingByte) {
        let _362___mcc_h0 = (_source14).expected;
        let _363___mcc_h1 = (_source14).b;
        let _364_b = _363___mcc_h1;
        let _365_b0 = _362___mcc_h0;
        let _366_c = (((_364_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_364_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting '"), _dafny.Seq.of(new _dafny.CodePoint((_365_b0)))), _dafny.Seq.UnicodeFromString("', read ")), _366_c);
      } else if (_source14.is_ExpectingAnyByte) {
        let _367___mcc_h2 = (_source14).expected__sq;
        let _368___mcc_h3 = (_source14).b;
        let _369_b = _368___mcc_h3;
        let _370_bs0 = _367___mcc_h2;
        let _371_c = (((_369_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_369_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        let _372_c0s = _dafny.Seq.Create(new BigNumber((_370_bs0).length), ((_373_bs0) => function (_374_idx) {
          return new _dafny.CodePoint(((_373_bs0)[_374_idx]));
        })(_370_bs0));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting one of '"), _372_c0s), _dafny.Seq.UnicodeFromString("', read ")), _371_c);
      } else {
        let _375___mcc_h4 = (_source14).err;
        let _376_err = _375___mcc_h4;
        return (pr)(_376_err);
      }
    };
  }

  $module.Cursor__ = class Cursor__ {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Cursor(s, beg, point, end) {
      let $dt = new Cursor__(0);
      $dt.s = s;
      $dt.beg = beg;
      $dt.point = point;
      $dt.end = end;
      return $dt;
    }
    get is_Cursor() { return this.$tag === 0; }
    get dtor_s() { return this.s; }
    get dtor_beg() { return this.beg; }
    get dtor_point() { return this.point; }
    get dtor_end() { return this.end; }
    toString() {
      if (this.$tag === 0) {
        return "Cursors.Cursor_.Cursor" + "(" + _dafny.toString(this.s) + ", " + _dafny.toString(this.beg) + ", " + _dafny.toString(this.point) + ", " + _dafny.toString(this.end) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.s, other.s) && this.beg === other.beg && this.point === other.point && this.end === other.end;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor(_dafny.Seq.of(), 0, 0, 0);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Cursor__.Default();
        }
      };
    }
    static OfView(v) {
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor((v).dtor_s, (v).dtor_beg, (v).dtor_beg, (v).dtor_end);
    };
    static OfBytes(bs) {
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor(bs, 0, 0, (bs).length);
    };
    Bytes() {
      let _this = this;
      return ((_this).dtor_s).slice((_this).dtor_beg, (_this).dtor_end);
    };
    Prefix() {
      let _this = this;
      return Std_JSON_Utils_Views_Core.View__.create_View((_this).dtor_s, (_this).dtor_beg, (_this).dtor_point);
    };
    Suffix() {
      let _this = this;
      let _377_dt__update__tmp_h0 = _this;
      let _378_dt__update_hbeg_h0 = (_this).dtor_point;
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_377_dt__update__tmp_h0).dtor_s, _378_dt__update_hbeg_h0, (_377_dt__update__tmp_h0).dtor_point, (_377_dt__update__tmp_h0).dtor_end);
    };
    Split() {
      let _this = this;
      return Std_JSON_Utils_Cursors.Split.create_SP((_this).Prefix(), (_this).Suffix());
    };
    PrefixLength() {
      let _this = this;
      return ((_this).dtor_point) - ((_this).dtor_beg);
    };
    SuffixLength() {
      let _this = this;
      return ((_this).dtor_end) - ((_this).dtor_point);
    };
    Length() {
      let _this = this;
      return ((_this).dtor_end) - ((_this).dtor_beg);
    };
    At(idx) {
      let _this = this;
      return ((_this).dtor_s)[((_this).dtor_beg) + (idx)];
    };
    SuffixAt(idx) {
      let _this = this;
      return ((_this).dtor_s)[((_this).dtor_point) + (idx)];
    };
    Peek() {
      let _this = this;
      if ((_this).EOF_q) {
        return -1;
      } else {
        return (_this).SuffixAt(0);
      }
    };
    LookingAt(c) {
      let _this = this;
      return ((_this).Peek()) === ((c).value);
    };
    Skip(n) {
      let _this = this;
      let _379_dt__update__tmp_h0 = _this;
      let _380_dt__update_hpoint_h0 = ((_this).dtor_point) + (n);
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_379_dt__update__tmp_h0).dtor_s, (_379_dt__update__tmp_h0).dtor_beg, _380_dt__update_hpoint_h0, (_379_dt__update__tmp_h0).dtor_end);
    };
    Unskip(n) {
      let _this = this;
      let _381_dt__update__tmp_h0 = _this;
      let _382_dt__update_hpoint_h0 = ((_this).dtor_point) - (n);
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_381_dt__update__tmp_h0).dtor_s, (_381_dt__update__tmp_h0).dtor_beg, _382_dt__update_hpoint_h0, (_381_dt__update__tmp_h0).dtor_end);
    };
    Get(err) {
      let _this = this;
      if ((_this).EOF_q) {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_OtherError(err));
      } else {
        return Std_Wrappers.Result.create_Success((_this).Skip(1));
      }
    };
    AssertByte(b) {
      let _this = this;
      let _383_nxt = (_this).Peek();
      if ((_383_nxt) === (b)) {
        return Std_Wrappers.Result.create_Success((_this).Skip(1));
      } else {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_ExpectingByte(b, _383_nxt));
      }
    };
    AssertBytes(bs, offset) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((offset) === ((bs).length)) {
          return Std_Wrappers.Result.create_Success(_this);
        } else {
          let _384_valueOrError0 = (_this).AssertByte(((bs)[offset]));
          if ((_384_valueOrError0).IsFailure()) {
            return (_384_valueOrError0).PropagateFailure();
          } else {
            let _385_ps = (_384_valueOrError0).Extract();
            let _in70 = _385_ps;
            let _in71 = bs;
            let _in72 = (offset) + (1);
            _this = _in70;
            ;
            bs = _in71;
            offset = _in72;
            continue TAIL_CALL_START;
          }
        }
      }
    };
    AssertChar(c0) {
      let _this = this;
      return (_this).AssertByte((c0).value);
    };
    SkipByte() {
      let _this = this;
      if ((_this).EOF_q) {
        return _this;
      } else {
        return (_this).Skip(1);
      }
    };
    SkipIf(p) {
      let _this = this;
      if (((_this).EOF_q) || (!((p)((_this).SuffixAt(0))))) {
        return _this;
      } else {
        return (_this).Skip(1);
      }
    };
    SkipWhile(p) {
      let _this = this;
      let ps = Std_JSON_Utils_Cursors.Cursor.Default;
      let _386_point_k;
      _386_point_k = (_this).dtor_point;
      let _387_end;
      _387_end = (_this).dtor_end;
      while (((_386_point_k) < (_387_end)) && ((p)(((_this).dtor_s)[_386_point_k]))) {
        _386_point_k = (_386_point_k) + (1);
      }
      ps = Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_this).dtor_s, (_this).dtor_beg, _386_point_k, (_this).dtor_end);
      return ps;
      return ps;
    }
    SkipWhileLexer(step, st) {
      let _this = this;
      let pr = Std_Wrappers.Result.Default(Std_JSON_Utils_Cursors.Cursor.Default);
      let _388_point_k;
      _388_point_k = (_this).dtor_point;
      let _389_end;
      _389_end = (_this).dtor_end;
      let _390_st_k;
      _390_st_k = st;
      while (true) {
        let _391_eof;
        _391_eof = (_388_point_k) === (_389_end);
        let _392_minusone;
        _392_minusone = -1;
        let _393_c;
        _393_c = ((_391_eof) ? (_392_minusone) : (((_this).dtor_s)[_388_point_k]));
        let _source15 = (step)(_390_st_k, _393_c);
        if (_source15.is_Accept) {
          pr = Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_this).dtor_s, (_this).dtor_beg, _388_point_k, (_this).dtor_end));
          return pr;
        } else if (_source15.is_Reject) {
          let _394___mcc_h0 = (_source15).err;
          let _395_err = _394___mcc_h0;
          pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_OtherError(_395_err));
          return pr;
        } else {
          let _396___mcc_h1 = (_source15).st;
          let _397_st_k_k = _396___mcc_h1;
          if (_391_eof) {
            pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
            return pr;
          } else {
            _390_st_k = _397_st_k_k;
            _388_point_k = (_388_point_k) + (1);
          }
        }
      }
      return pr;
    }
    get BOF_q() {
      let _this = this;
      return ((_this).dtor_point) === ((_this).dtor_beg);
    };
    get EOF_q() {
      let _this = this;
      return ((_this).dtor_point) === ((_this).dtor_end);
    };
  }
  return $module;
})(); // end of module Std_JSON_Utils_Cursors
let Std_JSON_Utils_Parsers = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Utils.Parsers._default";
    }
    _parentTraits() {
      return [];
    }
    static ParserWitness() {
      return function (_398___v9) {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
      };
    };
    static SubParserWitness() {
      return function (_399_cs) {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
      };
    };
  };

  $module.Parser = class Parser {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Parsers.__default.ParserWitness();
    }
    static get Default() {
      return Std_JSON_Utils_Parsers.Parser.Witness;
    }
  };

  $module.Parser__ = class Parser__ {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Parser(fn) {
      let $dt = new Parser__(0);
      $dt.fn = fn;
      return $dt;
    }
    get is_Parser() { return this.$tag === 0; }
    get dtor_fn() { return this.fn; }
    toString() {
      if (this.$tag === 0) {
        return "Parsers.Parser_.Parser" + "(" + _dafny.toString(this.fn) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.fn, other.fn);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_T) {
      return function () { return Std_Wrappers.Result.Default(Std_JSON_Utils_Cursors.Split.Default(_default_T)); };
    }
    static Rtd(rtd$_T) {
      return class {
        static get Default() {
          return Parser__.Default(rtd$_T.Default);
        }
      };
    }
  }

  $module.SubParser__ = class SubParser__ {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_SubParser(fn) {
      let $dt = new SubParser__(0);
      $dt.fn = fn;
      return $dt;
    }
    get is_SubParser() { return this.$tag === 0; }
    get dtor_fn() { return this.fn; }
    toString() {
      if (this.$tag === 0) {
        return "Parsers.SubParser_.SubParser" + "(" + _dafny.toString(this.fn) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.fn, other.fn);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return null;
    }
    static Rtd() {
      return class {
        static get Default() {
          return SubParser__.Default();
        }
      };
    }
  }

  $module.SubParser = class SubParser {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Parsers.__default.SubParserWitness();
    }
    static get Default() {
      return Std_JSON_Utils_Parsers.SubParser.Witness;
    }
  };
  return $module;
})(); // end of module Std_JSON_Utils_Parsers
let Std_JSON_Utils = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON_Utils
let Std_JSON_Grammar = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Grammar._default";
    }
    _parentTraits() {
      return [];
    }
    static Blank_q(b) {
      return ((((b) === (32)) || ((b) === (9))) || ((b) === (10))) || ((b) === (13));
    };
    static Digit_q(b) {
      return (((new _dafny.CodePoint('0'.codePointAt(0))).value) <= (b)) && ((b) <= ((new _dafny.CodePoint('9'.codePointAt(0))).value));
    };
    static get NULL() {
      return _dafny.Seq.of((new _dafny.CodePoint('n'.codePointAt(0))).value, (new _dafny.CodePoint('u'.codePointAt(0))).value, (new _dafny.CodePoint('l'.codePointAt(0))).value, (new _dafny.CodePoint('l'.codePointAt(0))).value);
    };
    static get TRUE() {
      return _dafny.Seq.of((new _dafny.CodePoint('t'.codePointAt(0))).value, (new _dafny.CodePoint('r'.codePointAt(0))).value, (new _dafny.CodePoint('u'.codePointAt(0))).value, (new _dafny.CodePoint('e'.codePointAt(0))).value);
    };
    static get FALSE() {
      return _dafny.Seq.of((new _dafny.CodePoint('f'.codePointAt(0))).value, (new _dafny.CodePoint('a'.codePointAt(0))).value, (new _dafny.CodePoint('l'.codePointAt(0))).value, (new _dafny.CodePoint('s'.codePointAt(0))).value, (new _dafny.CodePoint('e'.codePointAt(0))).value);
    };
    static get DOUBLEQUOTE() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('\"'.codePointAt(0))).value));
    };
    static get PERIOD() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('.'.codePointAt(0))).value));
    };
    static get E() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('e'.codePointAt(0))).value));
    };
    static get COLON() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint(':'.codePointAt(0))).value));
    };
    static get COMMA() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint(','.codePointAt(0))).value));
    };
    static get LBRACE() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('{'.codePointAt(0))).value));
    };
    static get RBRACE() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('}'.codePointAt(0))).value));
    };
    static get LBRACKET() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('['.codePointAt(0))).value));
    };
    static get RBRACKET() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint(']'.codePointAt(0))).value));
    };
    static get MINUS() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('-'.codePointAt(0))).value));
    };
    static get EMPTY() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of());
    };
  };

  $module.jchar = class jchar {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('b'.codePointAt(0))).value));
    }
    static get Default() {
      return Std_JSON_Grammar.jchar.Witness;
    }
  };

  $module.jquote = class jquote {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.DOUBLEQUOTE;
    }
    static get Default() {
      return Std_JSON_Grammar.jquote.Witness;
    }
  };

  $module.jperiod = class jperiod {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.PERIOD;
    }
    static get Default() {
      return Std_JSON_Grammar.jperiod.Witness;
    }
  };

  $module.je = class je {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.E;
    }
    static get Default() {
      return Std_JSON_Grammar.je.Witness;
    }
  };

  $module.jcolon = class jcolon {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.COLON;
    }
    static get Default() {
      return Std_JSON_Grammar.jcolon.Witness;
    }
  };

  $module.jcomma = class jcomma {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.COMMA;
    }
    static get Default() {
      return Std_JSON_Grammar.jcomma.Witness;
    }
  };

  $module.jlbrace = class jlbrace {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.LBRACE;
    }
    static get Default() {
      return Std_JSON_Grammar.jlbrace.Witness;
    }
  };

  $module.jrbrace = class jrbrace {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.RBRACE;
    }
    static get Default() {
      return Std_JSON_Grammar.jrbrace.Witness;
    }
  };

  $module.jlbracket = class jlbracket {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.LBRACKET;
    }
    static get Default() {
      return Std_JSON_Grammar.jlbracket.Witness;
    }
  };

  $module.jrbracket = class jrbracket {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.RBRACKET;
    }
    static get Default() {
      return Std_JSON_Grammar.jrbracket.Witness;
    }
  };

  $module.jminus = class jminus {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.MINUS;
    }
    static get Default() {
      return Std_JSON_Grammar.jminus.Witness;
    }
  };

  $module.jsign = class jsign {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Grammar.__default.EMPTY;
    }
    static get Default() {
      return Std_JSON_Grammar.jsign.Witness;
    }
  };

  $module.jblanks = class jblanks {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of());
    }
    static get Default() {
      return Std_JSON_Grammar.jblanks.Witness;
    }
  };

  $module.Structural = class Structural {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Structural(before, t, after) {
      let $dt = new Structural(0);
      $dt.before = before;
      $dt.t = t;
      $dt.after = after;
      return $dt;
    }
    get is_Structural() { return this.$tag === 0; }
    get dtor_before() { return this.before; }
    get dtor_t() { return this.t; }
    get dtor_after() { return this.after; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.Structural.Structural" + "(" + _dafny.toString(this.before) + ", " + _dafny.toString(this.t) + ", " + _dafny.toString(this.after) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.before, other.before) && _dafny.areEqual(this.t, other.t) && _dafny.areEqual(this.after, other.after);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_T) {
      return Std_JSON_Grammar.Structural.create_Structural(Std_JSON_Grammar.jblanks.Default, _default_T, Std_JSON_Grammar.jblanks.Default);
    }
    static Rtd(rtd$_T) {
      return class {
        static get Default() {
          return Structural.Default(rtd$_T.Default);
        }
      };
    }
  }

  $module.Maybe = class Maybe {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Empty() {
      let $dt = new Maybe(0);
      return $dt;
    }
    static create_NonEmpty(t) {
      let $dt = new Maybe(1);
      $dt.t = t;
      return $dt;
    }
    get is_Empty() { return this.$tag === 0; }
    get is_NonEmpty() { return this.$tag === 1; }
    get dtor_t() { return this.t; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.Maybe.Empty";
      } else if (this.$tag === 1) {
        return "Grammar.Maybe.NonEmpty" + "(" + _dafny.toString(this.t) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.t, other.t);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Grammar.Maybe.create_Empty();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Maybe.Default();
        }
      };
    }
  }

  $module.Suffixed = class Suffixed {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Suffixed(t, suffix) {
      let $dt = new Suffixed(0);
      $dt.t = t;
      $dt.suffix = suffix;
      return $dt;
    }
    get is_Suffixed() { return this.$tag === 0; }
    get dtor_t() { return this.t; }
    get dtor_suffix() { return this.suffix; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.Suffixed.Suffixed" + "(" + _dafny.toString(this.t) + ", " + _dafny.toString(this.suffix) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.t, other.t) && _dafny.areEqual(this.suffix, other.suffix);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_T) {
      return Std_JSON_Grammar.Suffixed.create_Suffixed(_default_T, Std_JSON_Grammar.Maybe.Default());
    }
    static Rtd(rtd$_T) {
      return class {
        static get Default() {
          return Suffixed.Default(rtd$_T.Default);
        }
      };
    }
  }

  $module.SuffixedSequence = class SuffixedSequence {
    constructor () {
    }
    static get Default() {
      return _dafny.Seq.of();
    }
  };

  $module.Bracketed = class Bracketed {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Bracketed(l, data, r) {
      let $dt = new Bracketed(0);
      $dt.l = l;
      $dt.data = data;
      $dt.r = r;
      return $dt;
    }
    get is_Bracketed() { return this.$tag === 0; }
    get dtor_l() { return this.l; }
    get dtor_data() { return this.data; }
    get dtor_r() { return this.r; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.Bracketed.Bracketed" + "(" + _dafny.toString(this.l) + ", " + _dafny.toString(this.data) + ", " + _dafny.toString(this.r) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.l, other.l) && _dafny.areEqual(this.data, other.data) && _dafny.areEqual(this.r, other.r);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_L, _default_R) {
      return Std_JSON_Grammar.Bracketed.create_Bracketed(Std_JSON_Grammar.Structural.Default(_default_L), _dafny.Seq.of(), Std_JSON_Grammar.Structural.Default(_default_R));
    }
    static Rtd(rtd$_L, rtd$_R) {
      return class {
        static get Default() {
          return Bracketed.Default(rtd$_L.Default, rtd$_R.Default);
        }
      };
    }
  }

  $module.jnull = class jnull {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(Std_JSON_Grammar.__default.NULL);
    }
    static get Default() {
      return Std_JSON_Grammar.jnull.Witness;
    }
  };

  $module.jbool = class jbool {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(Std_JSON_Grammar.__default.TRUE);
    }
    static get Default() {
      return Std_JSON_Grammar.jbool.Witness;
    }
  };

  $module.jdigits = class jdigits {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of());
    }
    static get Default() {
      return Std_JSON_Grammar.jdigits.Witness;
    }
  };

  $module.jnum = class jnum {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('0'.codePointAt(0))).value));
    }
    static get Default() {
      return Std_JSON_Grammar.jnum.Witness;
    }
  };

  $module.jint = class jint {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('0'.codePointAt(0))).value));
    }
    static get Default() {
      return Std_JSON_Grammar.jint.Witness;
    }
  };

  $module.jstr = class jstr {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of());
    }
    static get Default() {
      return Std_JSON_Grammar.jstr.Witness;
    }
  };

  $module.jstring = class jstring {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_JString(lq, contents, rq) {
      let $dt = new jstring(0);
      $dt.lq = lq;
      $dt.contents = contents;
      $dt.rq = rq;
      return $dt;
    }
    get is_JString() { return this.$tag === 0; }
    get dtor_lq() { return this.lq; }
    get dtor_contents() { return this.contents; }
    get dtor_rq() { return this.rq; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.jstring.JString" + "(" + _dafny.toString(this.lq) + ", " + _dafny.toString(this.contents) + ", " + _dafny.toString(this.rq) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.lq, other.lq) && _dafny.areEqual(this.contents, other.contents) && _dafny.areEqual(this.rq, other.rq);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Grammar.jstring.create_JString(Std_JSON_Grammar.jquote.Default, Std_JSON_Grammar.jstr.Default, Std_JSON_Grammar.jquote.Default);
    }
    static Rtd() {
      return class {
        static get Default() {
          return jstring.Default();
        }
      };
    }
  }

  $module.jKeyValue = class jKeyValue {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_KeyValue(k, colon, v) {
      let $dt = new jKeyValue(0);
      $dt.k = k;
      $dt.colon = colon;
      $dt.v = v;
      return $dt;
    }
    get is_KeyValue() { return this.$tag === 0; }
    get dtor_k() { return this.k; }
    get dtor_colon() { return this.colon; }
    get dtor_v() { return this.v; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.jKeyValue.KeyValue" + "(" + _dafny.toString(this.k) + ", " + _dafny.toString(this.colon) + ", " + _dafny.toString(this.v) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.k, other.k) && _dafny.areEqual(this.colon, other.colon) && _dafny.areEqual(this.v, other.v);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Grammar.jKeyValue.create_KeyValue(Std_JSON_Grammar.jstring.Default(), Std_JSON_Grammar.Structural.Default(Std_JSON_Grammar.jcolon.Default), Std_JSON_Grammar.Value.Default());
    }
    static Rtd() {
      return class {
        static get Default() {
          return jKeyValue.Default();
        }
      };
    }
  }

  $module.jfrac = class jfrac {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_JFrac(period, num) {
      let $dt = new jfrac(0);
      $dt.period = period;
      $dt.num = num;
      return $dt;
    }
    get is_JFrac() { return this.$tag === 0; }
    get dtor_period() { return this.period; }
    get dtor_num() { return this.num; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.jfrac.JFrac" + "(" + _dafny.toString(this.period) + ", " + _dafny.toString(this.num) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.period, other.period) && _dafny.areEqual(this.num, other.num);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Grammar.jfrac.create_JFrac(Std_JSON_Grammar.jperiod.Default, Std_JSON_Grammar.jnum.Default);
    }
    static Rtd() {
      return class {
        static get Default() {
          return jfrac.Default();
        }
      };
    }
  }

  $module.jexp = class jexp {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_JExp(e, sign, num) {
      let $dt = new jexp(0);
      $dt.e = e;
      $dt.sign = sign;
      $dt.num = num;
      return $dt;
    }
    get is_JExp() { return this.$tag === 0; }
    get dtor_e() { return this.e; }
    get dtor_sign() { return this.sign; }
    get dtor_num() { return this.num; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.jexp.JExp" + "(" + _dafny.toString(this.e) + ", " + _dafny.toString(this.sign) + ", " + _dafny.toString(this.num) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.e, other.e) && _dafny.areEqual(this.sign, other.sign) && _dafny.areEqual(this.num, other.num);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Grammar.jexp.create_JExp(Std_JSON_Grammar.je.Default, Std_JSON_Grammar.jsign.Default, Std_JSON_Grammar.jnum.Default);
    }
    static Rtd() {
      return class {
        static get Default() {
          return jexp.Default();
        }
      };
    }
  }

  $module.jnumber = class jnumber {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_JNumber(minus, num, frac, exp) {
      let $dt = new jnumber(0);
      $dt.minus = minus;
      $dt.num = num;
      $dt.frac = frac;
      $dt.exp = exp;
      return $dt;
    }
    get is_JNumber() { return this.$tag === 0; }
    get dtor_minus() { return this.minus; }
    get dtor_num() { return this.num; }
    get dtor_frac() { return this.frac; }
    get dtor_exp() { return this.exp; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.jnumber.JNumber" + "(" + _dafny.toString(this.minus) + ", " + _dafny.toString(this.num) + ", " + _dafny.toString(this.frac) + ", " + _dafny.toString(this.exp) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.minus, other.minus) && _dafny.areEqual(this.num, other.num) && _dafny.areEqual(this.frac, other.frac) && _dafny.areEqual(this.exp, other.exp);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Grammar.jnumber.create_JNumber(Std_JSON_Grammar.jminus.Default, Std_JSON_Grammar.jnum.Default, Std_JSON_Grammar.Maybe.Default(), Std_JSON_Grammar.Maybe.Default());
    }
    static Rtd() {
      return class {
        static get Default() {
          return jnumber.Default();
        }
      };
    }
  }

  $module.Value = class Value {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Null(n) {
      let $dt = new Value(0);
      $dt.n = n;
      return $dt;
    }
    static create_Bool(b) {
      let $dt = new Value(1);
      $dt.b = b;
      return $dt;
    }
    static create_String(str) {
      let $dt = new Value(2);
      $dt.str = str;
      return $dt;
    }
    static create_Number(num) {
      let $dt = new Value(3);
      $dt.num = num;
      return $dt;
    }
    static create_Object(obj) {
      let $dt = new Value(4);
      $dt.obj = obj;
      return $dt;
    }
    static create_Array(arr) {
      let $dt = new Value(5);
      $dt.arr = arr;
      return $dt;
    }
    get is_Null() { return this.$tag === 0; }
    get is_Bool() { return this.$tag === 1; }
    get is_String() { return this.$tag === 2; }
    get is_Number() { return this.$tag === 3; }
    get is_Object() { return this.$tag === 4; }
    get is_Array() { return this.$tag === 5; }
    get dtor_n() { return this.n; }
    get dtor_b() { return this.b; }
    get dtor_str() { return this.str; }
    get dtor_num() { return this.num; }
    get dtor_obj() { return this.obj; }
    get dtor_arr() { return this.arr; }
    toString() {
      if (this.$tag === 0) {
        return "Grammar.Value.Null" + "(" + _dafny.toString(this.n) + ")";
      } else if (this.$tag === 1) {
        return "Grammar.Value.Bool" + "(" + _dafny.toString(this.b) + ")";
      } else if (this.$tag === 2) {
        return "Grammar.Value.String" + "(" + _dafny.toString(this.str) + ")";
      } else if (this.$tag === 3) {
        return "Grammar.Value.Number" + "(" + _dafny.toString(this.num) + ")";
      } else if (this.$tag === 4) {
        return "Grammar.Value.Object" + "(" + _dafny.toString(this.obj) + ")";
      } else if (this.$tag === 5) {
        return "Grammar.Value.Array" + "(" + _dafny.toString(this.arr) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.n, other.n);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.b, other.b);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.str, other.str);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.num, other.num);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.obj, other.obj);
      } else if (this.$tag === 5) {
        return other.$tag === 5 && _dafny.areEqual(this.arr, other.arr);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Std_JSON_Grammar.Value.create_Null(Std_JSON_Grammar.jnull.Default);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Value.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module Std_JSON_Grammar
let Std_JSON_ByteStrConversion = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ByteStrConversion._default";
    }
    _parentTraits() {
      return [];
    }
    static BASE() {
      return Std_JSON_ByteStrConversion.__default.base;
    };
    static IsDigitChar(c) {
      return (Std_JSON_ByteStrConversion.__default.charToDigit).contains(c);
    };
    static OfDigits(digits) {
      let _400___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _400___accumulator);
        } else {
          _400___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_JSON_ByteStrConversion.__default.chars)[(digits)[_dafny.ZERO]]), _400___accumulator);
          let _in73 = (digits).slice(_dafny.ONE);
          digits = _in73;
          continue TAIL_CALL_START;
        }
      }
    };
    static OfNat(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of((Std_JSON_ByteStrConversion.__default.chars)[_dafny.ZERO]);
      } else {
        return Std_JSON_ByteStrConversion.__default.OfDigits(Std_JSON_ByteStrConversion.__default.FromNat(n));
      }
    };
    static IsNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((((str)[_dafny.ZERO]) === (minus)) || ((Std_JSON_ByteStrConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_3) {
        let _401_c = _forall_var_3;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _401_c)) || (Std_JSON_ByteStrConversion.__default.IsDigitChar(_401_c));
      })));
    };
    static OfInt(n, minus) {
      if ((_dafny.ZERO).isLessThanOrEqualTo(n)) {
        return Std_JSON_ByteStrConversion.__default.OfNat(n);
      } else {
        return _dafny.Seq.Concat(_dafny.Seq.of(minus), Std_JSON_ByteStrConversion.__default.OfNat((_dafny.ZERO).minus(n)));
      }
    };
    static ToNat(str) {
      if (_dafny.areEqual(str, _dafny.Seq.of())) {
        return _dafny.ZERO;
      } else {
        let _402_c = (str)[(new BigNumber((str).length)).minus(_dafny.ONE)];
        return ((Std_JSON_ByteStrConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_JSON_ByteStrConversion.__default.base)).plus((Std_JSON_ByteStrConversion.__default.charToDigit).get(_402_c));
      }
    };
    static ToInt(str, minus) {
      if (_dafny.Seq.IsPrefixOf(_dafny.Seq.of(minus), str)) {
        return (_dafny.ZERO).minus((Std_JSON_ByteStrConversion.__default.ToNat((str).slice(_dafny.ONE))));
      } else {
        return Std_JSON_ByteStrConversion.__default.ToNat(str);
      }
    };
    static ToNatRight(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.ZERO;
      } else {
        return ((Std_JSON_ByteStrConversion.__default.ToNatRight(Std_Collections_Seq.__default.DropFirst(xs))).multipliedBy(Std_JSON_ByteStrConversion.__default.BASE())).plus(Std_Collections_Seq.__default.First(xs));
      }
    };
    static ToNatLeft(xs) {
      let _403___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_403___accumulator);
        } else {
          _403___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_JSON_ByteStrConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_403___accumulator);
          let _in74 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in74;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _404___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_404___accumulator, _dafny.Seq.of());
        } else {
          _404___accumulator = _dafny.Seq.Concat(_404___accumulator, _dafny.Seq.of((n).mod(Std_JSON_ByteStrConversion.__default.BASE())));
          let _in75 = _dafny.EuclideanDivision(n, Std_JSON_ByteStrConversion.__default.BASE());
          n = _in75;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in76 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in77 = n;
          xs = _in76;
          n = _in77;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _405_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_JSON_ByteStrConversion.__default.SeqExtend(xs, _405_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_JSON_ByteStrConversion.__default.SeqExtend(Std_JSON_ByteStrConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _406_xs = Std_JSON_ByteStrConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _406_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs9 = Std_JSON_ByteStrConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _407_zs_k = (_let_tmp_rhs9)[0];
        let _408_cin = (_let_tmp_rhs9)[1];
        let _409_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_408_cin);
        let _let_tmp_rhs10 = (((_409_sum).isLessThan(Std_JSON_ByteStrConversion.__default.BASE())) ? (_dafny.Tuple.of(_409_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_409_sum).minus(Std_JSON_ByteStrConversion.__default.BASE()), _dafny.ONE)));
        let _410_sum__out = (_let_tmp_rhs10)[0];
        let _411_cout = (_let_tmp_rhs10)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_407_zs_k, _dafny.Seq.of(_410_sum__out)), _411_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs11 = Std_JSON_ByteStrConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _412_zs = (_let_tmp_rhs11)[0];
        let _413_cin = (_let_tmp_rhs11)[1];
        let _let_tmp_rhs12 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_413_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_413_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_JSON_ByteStrConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_413_cin), _dafny.ONE)));
        let _414_diff__out = (_let_tmp_rhs12)[0];
        let _415_cout = (_let_tmp_rhs12)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_412_zs, _dafny.Seq.of(_414_diff__out)), _415_cout);
      }
    };
    static get chars() {
      return _dafny.Seq.of((new _dafny.CodePoint('0'.codePointAt(0))).value, (new _dafny.CodePoint('1'.codePointAt(0))).value, (new _dafny.CodePoint('2'.codePointAt(0))).value, (new _dafny.CodePoint('3'.codePointAt(0))).value, (new _dafny.CodePoint('4'.codePointAt(0))).value, (new _dafny.CodePoint('5'.codePointAt(0))).value, (new _dafny.CodePoint('6'.codePointAt(0))).value, (new _dafny.CodePoint('7'.codePointAt(0))).value, (new _dafny.CodePoint('8'.codePointAt(0))).value, (new _dafny.CodePoint('9'.codePointAt(0))).value);
    };
    static get base() {
      return new BigNumber((Std_JSON_ByteStrConversion.__default.chars).length);
    };
    static get charToDigit() {
      return _dafny.Map.Empty.slice().updateUnsafe((new _dafny.CodePoint('0'.codePointAt(0))).value,_dafny.ZERO).updateUnsafe((new _dafny.CodePoint('1'.codePointAt(0))).value,_dafny.ONE).updateUnsafe((new _dafny.CodePoint('2'.codePointAt(0))).value,new BigNumber(2)).updateUnsafe((new _dafny.CodePoint('3'.codePointAt(0))).value,new BigNumber(3)).updateUnsafe((new _dafny.CodePoint('4'.codePointAt(0))).value,new BigNumber(4)).updateUnsafe((new _dafny.CodePoint('5'.codePointAt(0))).value,new BigNumber(5)).updateUnsafe((new _dafny.CodePoint('6'.codePointAt(0))).value,new BigNumber(6)).updateUnsafe((new _dafny.CodePoint('7'.codePointAt(0))).value,new BigNumber(7)).updateUnsafe((new _dafny.CodePoint('8'.codePointAt(0))).value,new BigNumber(8)).updateUnsafe((new _dafny.CodePoint('9'.codePointAt(0))).value,new BigNumber(9));
    };
  };

  $module.CharSeq = class CharSeq {
    constructor () {
    }
    static get Default() {
      return _dafny.Seq.of();
    }
  };

  $module.digit = class digit {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module Std_JSON_ByteStrConversion
let Std_JSON_Serializer = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Serializer._default";
    }
    _parentTraits() {
      return [];
    }
    static Bool(b) {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(((b) ? (Std_JSON_Grammar.__default.TRUE) : (Std_JSON_Grammar.__default.FALSE)));
    };
    static CheckLength(s, err) {
      return Std_Wrappers.Outcome.Need((new BigNumber((s).length)).isLessThan(Std_BoundedInts.__default.TWO__TO__THE__32), err);
    };
    static String(str) {
      let _416_valueOrError0 = Std_JSON_Spec.__default.EscapeToUTF8(str, _dafny.ZERO);
      if ((_416_valueOrError0).IsFailure()) {
        return (_416_valueOrError0).PropagateFailure();
      } else {
        let _417_bs = (_416_valueOrError0).Extract();
        let _418_o = Std_JSON_Serializer.__default.CheckLength(_417_bs, Std_JSON_Errors.SerializationError.create_StringTooLong(str));
        if ((_418_o).is_Pass) {
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.jstring.create_JString(Std_JSON_Grammar.__default.DOUBLEQUOTE, Std_JSON_Utils_Views_Core.View__.OfBytes(_417_bs), Std_JSON_Grammar.__default.DOUBLEQUOTE));
        } else {
          return Std_Wrappers.Result.create_Failure((_418_o).dtor_error);
        }
      }
    };
    static Sign(n) {
      return Std_JSON_Utils_Views_Core.View__.OfBytes((((n).isLessThan(_dafny.ZERO)) ? (_dafny.Seq.of((new _dafny.CodePoint('-'.codePointAt(0))).value)) : (_dafny.Seq.of())));
    };
    static Int_k(n) {
      return Std_JSON_ByteStrConversion.__default.OfInt(n, Std_JSON_Serializer.__default.MINUS);
    };
    static Int(n) {
      let _419_bs = Std_JSON_Serializer.__default.Int_k(n);
      let _420_o = Std_JSON_Serializer.__default.CheckLength(_419_bs, Std_JSON_Errors.SerializationError.create_IntTooLarge(n));
      if ((_420_o).is_Pass) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Views_Core.View__.OfBytes(_419_bs));
      } else {
        return Std_Wrappers.Result.create_Failure((_420_o).dtor_error);
      }
    };
    static Number(dec) {
      let _pat_let_tv2 = dec;
      let _pat_let_tv3 = dec;
      let _421_minus = Std_JSON_Serializer.__default.Sign((dec).dtor_n);
      let _422_valueOrError0 = Std_JSON_Serializer.__default.Int(Std_Math.__default.Abs((dec).dtor_n));
      if ((_422_valueOrError0).IsFailure()) {
        return (_422_valueOrError0).PropagateFailure();
      } else {
        let _423_num = (_422_valueOrError0).Extract();
        let _424_frac = Std_JSON_Grammar.Maybe.create_Empty();
        let _425_valueOrError1 = ((((dec).dtor_e10).isEqualTo(_dafny.ZERO)) ? (Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Maybe.create_Empty())) : (function (_pat_let2_0) {
          return function (_426_e) {
            return function (_pat_let3_0) {
              return function (_427_sign) {
                return function (_pat_let4_0) {
                  return function (_428_valueOrError2) {
                    return (((_428_valueOrError2).IsFailure()) ? ((_428_valueOrError2).PropagateFailure()) : (function (_pat_let5_0) {
                      return function (_429_num) {
                        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Maybe.create_NonEmpty(Std_JSON_Grammar.jexp.create_JExp(_426_e, _427_sign, _429_num)));
                      }(_pat_let5_0);
                    }((_428_valueOrError2).Extract())));
                  }(_pat_let4_0);
                }(Std_JSON_Serializer.__default.Int(Std_Math.__default.Abs((_pat_let_tv3).dtor_e10)));
              }(_pat_let3_0);
            }(Std_JSON_Serializer.__default.Sign((_pat_let_tv2).dtor_e10));
          }(_pat_let2_0);
        }(Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('e'.codePointAt(0))).value)))));
        if ((_425_valueOrError1).IsFailure()) {
          return (_425_valueOrError1).PropagateFailure();
        } else {
          let _430_exp = (_425_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.jnumber.create_JNumber(_421_minus, _423_num, Std_JSON_Grammar.Maybe.create_Empty(), _430_exp));
        }
      }
    };
    static MkStructural(v) {
      return Std_JSON_Grammar.Structural.create_Structural(Std_JSON_Grammar.__default.EMPTY, v, Std_JSON_Grammar.__default.EMPTY);
    };
    static KeyValue(kv) {
      let _431_valueOrError0 = Std_JSON_Serializer.__default.String((kv)[0]);
      if ((_431_valueOrError0).IsFailure()) {
        return (_431_valueOrError0).PropagateFailure();
      } else {
        let _432_k = (_431_valueOrError0).Extract();
        let _433_valueOrError1 = Std_JSON_Serializer.__default.Value((kv)[1]);
        if ((_433_valueOrError1).IsFailure()) {
          return (_433_valueOrError1).PropagateFailure();
        } else {
          let _434_v = (_433_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.jKeyValue.create_KeyValue(_432_k, Std_JSON_Serializer.__default.COLON, _434_v));
        }
      }
    };
    static MkSuffixedSequence(ds, suffix, start) {
      let _435___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((ds).length)).isLessThanOrEqualTo(start)) {
          return _dafny.Seq.Concat(_435___accumulator, _dafny.Seq.of());
        } else if ((start).isEqualTo((new BigNumber((ds).length)).minus(_dafny.ONE))) {
          return _dafny.Seq.Concat(_435___accumulator, _dafny.Seq.of(Std_JSON_Grammar.Suffixed.create_Suffixed((ds)[start], Std_JSON_Grammar.Maybe.create_Empty())));
        } else {
          _435___accumulator = _dafny.Seq.Concat(_435___accumulator, _dafny.Seq.of(Std_JSON_Grammar.Suffixed.create_Suffixed((ds)[start], Std_JSON_Grammar.Maybe.create_NonEmpty(suffix))));
          let _in78 = ds;
          let _in79 = suffix;
          let _in80 = (start).plus(_dafny.ONE);
          ds = _in78;
          suffix = _in79;
          start = _in80;
          continue TAIL_CALL_START;
        }
      }
    };
    static Object(obj) {
      let _436_valueOrError0 = Std_Collections_Seq.__default.MapWithResult(((_437_obj) => function (_438_v) {
        return Std_JSON_Serializer.__default.KeyValue(_438_v);
      })(obj), obj);
      if ((_436_valueOrError0).IsFailure()) {
        return (_436_valueOrError0).PropagateFailure();
      } else {
        let _439_items = (_436_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Bracketed.create_Bracketed(Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.LBRACE), Std_JSON_Serializer.__default.MkSuffixedSequence(_439_items, Std_JSON_Serializer.__default.COMMA, _dafny.ZERO), Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.RBRACE)));
      }
    };
    static Array(arr) {
      let _440_valueOrError0 = Std_Collections_Seq.__default.MapWithResult(((_441_arr) => function (_442_v) {
        return Std_JSON_Serializer.__default.Value(_442_v);
      })(arr), arr);
      if ((_440_valueOrError0).IsFailure()) {
        return (_440_valueOrError0).PropagateFailure();
      } else {
        let _443_items = (_440_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Bracketed.create_Bracketed(Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.LBRACKET), Std_JSON_Serializer.__default.MkSuffixedSequence(_443_items, Std_JSON_Serializer.__default.COMMA, _dafny.ZERO), Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.RBRACKET)));
      }
    };
    static Value(js) {
      let _source16 = js;
      if (_source16.is_Null) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Null(Std_JSON_Utils_Views_Core.View__.OfBytes(Std_JSON_Grammar.__default.NULL)));
      } else if (_source16.is_Bool) {
        let _444___mcc_h0 = (_source16).b;
        let _445_b = _444___mcc_h0;
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Bool(Std_JSON_Serializer.__default.Bool(_445_b)));
      } else if (_source16.is_String) {
        let _446___mcc_h1 = (_source16).str;
        let _447_str = _446___mcc_h1;
        let _448_valueOrError0 = Std_JSON_Serializer.__default.String(_447_str);
        if ((_448_valueOrError0).IsFailure()) {
          return (_448_valueOrError0).PropagateFailure();
        } else {
          let _449_s = (_448_valueOrError0).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_String(_449_s));
        }
      } else if (_source16.is_Number) {
        let _450___mcc_h2 = (_source16).num;
        let _451_dec = _450___mcc_h2;
        let _452_valueOrError1 = Std_JSON_Serializer.__default.Number(_451_dec);
        if ((_452_valueOrError1).IsFailure()) {
          return (_452_valueOrError1).PropagateFailure();
        } else {
          let _453_n = (_452_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Number(_453_n));
        }
      } else if (_source16.is_Object) {
        let _454___mcc_h3 = (_source16).obj;
        let _455_obj = _454___mcc_h3;
        let _456_valueOrError2 = Std_JSON_Serializer.__default.Object(_455_obj);
        if ((_456_valueOrError2).IsFailure()) {
          return (_456_valueOrError2).PropagateFailure();
        } else {
          let _457_o = (_456_valueOrError2).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Object(_457_o));
        }
      } else {
        let _458___mcc_h4 = (_source16).arr;
        let _459_arr = _458___mcc_h4;
        let _460_valueOrError3 = Std_JSON_Serializer.__default.Array(_459_arr);
        if ((_460_valueOrError3).IsFailure()) {
          return (_460_valueOrError3).PropagateFailure();
        } else {
          let _461_a = (_460_valueOrError3).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Array(_461_a));
        }
      }
    };
    static JSON(js) {
      let _462_valueOrError0 = Std_JSON_Serializer.__default.Value(js);
      if ((_462_valueOrError0).IsFailure()) {
        return (_462_valueOrError0).PropagateFailure();
      } else {
        let _463_val = (_462_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(Std_JSON_Serializer.__default.MkStructural(_463_val));
      }
    };
    static get DIGITS() {
      return Std_JSON_ByteStrConversion.__default.chars;
    };
    static get MINUS() {
      return (new _dafny.CodePoint('-'.codePointAt(0))).value;
    };
    static get COLON() {
      return Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.COLON);
    };
    static get COMMA() {
      return Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.COMMA);
    };
  };

  $module.bytes32 = class bytes32 {
    constructor () {
    }
    static get Default() {
      return _dafny.Seq.of();
    }
  };

  $module.string32 = class string32 {
    constructor () {
    }
    static get Default() {
      return '';
    }
  };
  return $module;
})(); // end of module Std_JSON_Serializer
let Std_JSON_Deserializer_Uint16StrConversion = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Deserializer.Uint16StrConversion._default";
    }
    _parentTraits() {
      return [];
    }
    static BASE() {
      return Std_JSON_Deserializer_Uint16StrConversion.__default.base;
    };
    static IsDigitChar(c) {
      return (Std_JSON_Deserializer_Uint16StrConversion.__default.charToDigit).contains(c);
    };
    static OfDigits(digits) {
      let _464___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _464___accumulator);
        } else {
          _464___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_JSON_Deserializer_Uint16StrConversion.__default.chars)[(digits)[_dafny.ZERO]]), _464___accumulator);
          let _in81 = (digits).slice(_dafny.ONE);
          digits = _in81;
          continue TAIL_CALL_START;
        }
      }
    };
    static OfNat(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of((Std_JSON_Deserializer_Uint16StrConversion.__default.chars)[_dafny.ZERO]);
      } else {
        return Std_JSON_Deserializer_Uint16StrConversion.__default.OfDigits(Std_JSON_Deserializer_Uint16StrConversion.__default.FromNat(n));
      }
    };
    static IsNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((((str)[_dafny.ZERO]) === (minus)) || ((Std_JSON_Deserializer_Uint16StrConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_4) {
        let _465_c = _forall_var_4;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _465_c)) || (Std_JSON_Deserializer_Uint16StrConversion.__default.IsDigitChar(_465_c));
      })));
    };
    static OfInt(n, minus) {
      if ((_dafny.ZERO).isLessThanOrEqualTo(n)) {
        return Std_JSON_Deserializer_Uint16StrConversion.__default.OfNat(n);
      } else {
        return _dafny.Seq.Concat(_dafny.Seq.of(minus), Std_JSON_Deserializer_Uint16StrConversion.__default.OfNat((_dafny.ZERO).minus(n)));
      }
    };
    static ToNat(str) {
      if (_dafny.areEqual(str, _dafny.Seq.of())) {
        return _dafny.ZERO;
      } else {
        let _466_c = (str)[(new BigNumber((str).length)).minus(_dafny.ONE)];
        return ((Std_JSON_Deserializer_Uint16StrConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_JSON_Deserializer_Uint16StrConversion.__default.base)).plus((Std_JSON_Deserializer_Uint16StrConversion.__default.charToDigit).get(_466_c));
      }
    };
    static ToInt(str, minus) {
      if (_dafny.Seq.IsPrefixOf(_dafny.Seq.of(minus), str)) {
        return (_dafny.ZERO).minus((Std_JSON_Deserializer_Uint16StrConversion.__default.ToNat((str).slice(_dafny.ONE))));
      } else {
        return Std_JSON_Deserializer_Uint16StrConversion.__default.ToNat(str);
      }
    };
    static ToNatRight(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.ZERO;
      } else {
        return ((Std_JSON_Deserializer_Uint16StrConversion.__default.ToNatRight(Std_Collections_Seq.__default.DropFirst(xs))).multipliedBy(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE())).plus(Std_Collections_Seq.__default.First(xs));
      }
    };
    static ToNatLeft(xs) {
      let _467___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_467___accumulator);
        } else {
          _467___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_467___accumulator);
          let _in82 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in82;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _468___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_468___accumulator, _dafny.Seq.of());
        } else {
          _468___accumulator = _dafny.Seq.Concat(_468___accumulator, _dafny.Seq.of((n).mod(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE())));
          let _in83 = _dafny.EuclideanDivision(n, Std_JSON_Deserializer_Uint16StrConversion.__default.BASE());
          n = _in83;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in84 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in85 = n;
          xs = _in84;
          n = _in85;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _469_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_JSON_Deserializer_Uint16StrConversion.__default.SeqExtend(xs, _469_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_JSON_Deserializer_Uint16StrConversion.__default.SeqExtend(Std_JSON_Deserializer_Uint16StrConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _470_xs = Std_JSON_Deserializer_Uint16StrConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _470_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs13 = Std_JSON_Deserializer_Uint16StrConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _471_zs_k = (_let_tmp_rhs13)[0];
        let _472_cin = (_let_tmp_rhs13)[1];
        let _473_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_472_cin);
        let _let_tmp_rhs14 = (((_473_sum).isLessThan(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE())) ? (_dafny.Tuple.of(_473_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_473_sum).minus(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE()), _dafny.ONE)));
        let _474_sum__out = (_let_tmp_rhs14)[0];
        let _475_cout = (_let_tmp_rhs14)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_471_zs_k, _dafny.Seq.of(_474_sum__out)), _475_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs15 = Std_JSON_Deserializer_Uint16StrConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _476_zs = (_let_tmp_rhs15)[0];
        let _477_cin = (_let_tmp_rhs15)[1];
        let _let_tmp_rhs16 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_477_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_477_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_JSON_Deserializer_Uint16StrConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_477_cin), _dafny.ONE)));
        let _478_diff__out = (_let_tmp_rhs16)[0];
        let _479_cout = (_let_tmp_rhs16)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_476_zs, _dafny.Seq.of(_478_diff__out)), _479_cout);
      }
    };
    static get chars() {
      return _dafny.Seq.of((new _dafny.CodePoint('0'.codePointAt(0))).value, (new _dafny.CodePoint('1'.codePointAt(0))).value, (new _dafny.CodePoint('2'.codePointAt(0))).value, (new _dafny.CodePoint('3'.codePointAt(0))).value, (new _dafny.CodePoint('4'.codePointAt(0))).value, (new _dafny.CodePoint('5'.codePointAt(0))).value, (new _dafny.CodePoint('6'.codePointAt(0))).value, (new _dafny.CodePoint('7'.codePointAt(0))).value, (new _dafny.CodePoint('8'.codePointAt(0))).value, (new _dafny.CodePoint('9'.codePointAt(0))).value, (new _dafny.CodePoint('a'.codePointAt(0))).value, (new _dafny.CodePoint('b'.codePointAt(0))).value, (new _dafny.CodePoint('c'.codePointAt(0))).value, (new _dafny.CodePoint('d'.codePointAt(0))).value, (new _dafny.CodePoint('e'.codePointAt(0))).value, (new _dafny.CodePoint('f'.codePointAt(0))).value, (new _dafny.CodePoint('A'.codePointAt(0))).value, (new _dafny.CodePoint('B'.codePointAt(0))).value, (new _dafny.CodePoint('C'.codePointAt(0))).value, (new _dafny.CodePoint('D'.codePointAt(0))).value, (new _dafny.CodePoint('E'.codePointAt(0))).value, (new _dafny.CodePoint('F'.codePointAt(0))).value);
    };
    static get base() {
      return new BigNumber((Std_JSON_Deserializer_Uint16StrConversion.__default.chars).length);
    };
    static get charToDigit() {
      return _dafny.Map.Empty.slice().updateUnsafe((new _dafny.CodePoint('0'.codePointAt(0))).value,_dafny.ZERO).updateUnsafe((new _dafny.CodePoint('1'.codePointAt(0))).value,_dafny.ONE).updateUnsafe((new _dafny.CodePoint('2'.codePointAt(0))).value,new BigNumber(2)).updateUnsafe((new _dafny.CodePoint('3'.codePointAt(0))).value,new BigNumber(3)).updateUnsafe((new _dafny.CodePoint('4'.codePointAt(0))).value,new BigNumber(4)).updateUnsafe((new _dafny.CodePoint('5'.codePointAt(0))).value,new BigNumber(5)).updateUnsafe((new _dafny.CodePoint('6'.codePointAt(0))).value,new BigNumber(6)).updateUnsafe((new _dafny.CodePoint('7'.codePointAt(0))).value,new BigNumber(7)).updateUnsafe((new _dafny.CodePoint('8'.codePointAt(0))).value,new BigNumber(8)).updateUnsafe((new _dafny.CodePoint('9'.codePointAt(0))).value,new BigNumber(9)).updateUnsafe((new _dafny.CodePoint('a'.codePointAt(0))).value,new BigNumber(10)).updateUnsafe((new _dafny.CodePoint('b'.codePointAt(0))).value,new BigNumber(11)).updateUnsafe((new _dafny.CodePoint('c'.codePointAt(0))).value,new BigNumber(12)).updateUnsafe((new _dafny.CodePoint('d'.codePointAt(0))).value,new BigNumber(13)).updateUnsafe((new _dafny.CodePoint('e'.codePointAt(0))).value,new BigNumber(14)).updateUnsafe((new _dafny.CodePoint('f'.codePointAt(0))).value,new BigNumber(15)).updateUnsafe((new _dafny.CodePoint('A'.codePointAt(0))).value,new BigNumber(10)).updateUnsafe((new _dafny.CodePoint('B'.codePointAt(0))).value,new BigNumber(11)).updateUnsafe((new _dafny.CodePoint('C'.codePointAt(0))).value,new BigNumber(12)).updateUnsafe((new _dafny.CodePoint('D'.codePointAt(0))).value,new BigNumber(13)).updateUnsafe((new _dafny.CodePoint('E'.codePointAt(0))).value,new BigNumber(14)).updateUnsafe((new _dafny.CodePoint('F'.codePointAt(0))).value,new BigNumber(15));
    };
  };

  $module.CharSeq = class CharSeq {
    constructor () {
    }
    static get Default() {
      return _dafny.Seq.of();
    }
  };

  $module.digit = class digit {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module Std_JSON_Deserializer_Uint16StrConversion
let Std_JSON_Deserializer = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.Deserializer._default";
    }
    _parentTraits() {
      return [];
    }
    static Bool(js) {
      return ((js).At(0)) === ((new _dafny.CodePoint('t'.codePointAt(0))).value);
    };
    static UnsupportedEscape16(code) {
      return Std_JSON_Errors.DeserializationError.create_UnsupportedEscape((Std_Unicode_UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(code)).GetOr(_dafny.Seq.UnicodeFromString("Couldn't decode UTF-16")));
    };
    static ToNat16(str) {
      let _480_hd = Std_JSON_Deserializer_Uint16StrConversion.__default.ToNat(str);
      return (_480_hd).toNumber();
    };
    static Unescape(str, start, prefix) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((str).length)).isLessThanOrEqualTo(start)) {
          return Std_Wrappers.Result.create_Success(prefix);
        } else if (((str)[start]) === ((new _dafny.CodePoint('\\'.codePointAt(0))).value)) {
          if ((new BigNumber((str).length)).isEqualTo((start).plus(_dafny.ONE))) {
            return Std_Wrappers.Result.create_Failure(Std_JSON_Errors.DeserializationError.create_EscapeAtEOS());
          } else {
            let _481_c = (str)[(start).plus(_dafny.ONE)];
            if ((_481_c) === ((new _dafny.CodePoint('u'.codePointAt(0))).value)) {
              if ((new BigNumber((str).length)).isLessThanOrEqualTo((start).plus(new BigNumber(6)))) {
                return Std_Wrappers.Result.create_Failure(Std_JSON_Errors.DeserializationError.create_EscapeAtEOS());
              } else {
                let _482_code = (str).slice((start).plus(new BigNumber(2)), (start).plus(new BigNumber(6)));
                if (_dafny.Quantifier((_482_code).UniqueElements, false, function (_exists_var_0) {
                  let _483_c = _exists_var_0;
                  return (_dafny.Seq.contains(_482_code, _483_c)) && (!(Std_JSON_Deserializer.__default.HEX__TABLE__16).contains(_483_c));
                })) {
                  return Std_Wrappers.Result.create_Failure(Std_JSON_Deserializer.__default.UnsupportedEscape16(_482_code));
                } else {
                  let _484_hd = Std_JSON_Deserializer.__default.ToNat16(_482_code);
                  let _in86 = str;
                  let _in87 = (start).plus(new BigNumber(6));
                  let _in88 = _dafny.Seq.Concat(prefix, _dafny.Seq.of(_484_hd));
                  str = _in86;
                  start = _in87;
                  prefix = _in88;
                  continue TAIL_CALL_START;
                }
              }
            } else {
              let _485_unescaped = (((_481_c) === (34)) ? ((34)) : ((((_481_c) === (92)) ? ((92)) : ((((_481_c) === (98)) ? ((8)) : ((((_481_c) === (102)) ? ((12)) : ((((_481_c) === (110)) ? ((10)) : ((((_481_c) === (114)) ? ((13)) : ((((_481_c) === (116)) ? ((9)) : ((0)))))))))))))));
              if ((new BigNumber(_485_unescaped)).isEqualTo(_dafny.ZERO)) {
                return Std_Wrappers.Result.create_Failure(Std_JSON_Deserializer.__default.UnsupportedEscape16((str).slice(start, (start).plus(new BigNumber(2)))));
              } else {
                let _in89 = str;
                let _in90 = (start).plus(new BigNumber(2));
                let _in91 = _dafny.Seq.Concat(prefix, _dafny.Seq.of(_485_unescaped));
                str = _in89;
                start = _in90;
                prefix = _in91;
                continue TAIL_CALL_START;
              }
            }
          }
        } else {
          let _in92 = str;
          let _in93 = (start).plus(_dafny.ONE);
          let _in94 = _dafny.Seq.Concat(prefix, _dafny.Seq.of((str)[start]));
          str = _in92;
          start = _in93;
          prefix = _in94;
          continue TAIL_CALL_START;
        }
      }
    };
    static String(js) {
      let _486_valueOrError0 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.FromUTF8Checked(((js).dtor_contents).Bytes())).ToResult(Std_JSON_Errors.DeserializationError.create_InvalidUnicode());
      if ((_486_valueOrError0).IsFailure()) {
        return (_486_valueOrError0).PropagateFailure();
      } else {
        let _487_asUtf32 = (_486_valueOrError0).Extract();
        let _488_valueOrError1 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(_487_asUtf32)).ToResult(Std_JSON_Errors.DeserializationError.create_InvalidUnicode());
        if ((_488_valueOrError1).IsFailure()) {
          return (_488_valueOrError1).PropagateFailure();
        } else {
          let _489_asUint16 = (_488_valueOrError1).Extract();
          let _490_valueOrError2 = Std_JSON_Deserializer.__default.Unescape(_489_asUint16, _dafny.ZERO, _dafny.Seq.of());
          if ((_490_valueOrError2).IsFailure()) {
            return (_490_valueOrError2).PropagateFailure();
          } else {
            let _491_unescaped = (_490_valueOrError2).Extract();
            return (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_491_unescaped)).ToResult(Std_JSON_Errors.DeserializationError.create_InvalidUnicode());
          }
        }
      }
    };
    static ToInt(sign, n) {
      let _492_n = Std_JSON_ByteStrConversion.__default.ToNat((n).Bytes());
      return Std_Wrappers.Result.create_Success((((sign).Char_q(new _dafny.CodePoint('-'.codePointAt(0)))) ? ((_dafny.ZERO).minus(_492_n)) : (_492_n)));
    };
    static Number(js) {
      let _let_tmp_rhs17 = js;
      let _493_minus = (_let_tmp_rhs17).minus;
      let _494_num = (_let_tmp_rhs17).num;
      let _495_frac = (_let_tmp_rhs17).frac;
      let _496_exp = (_let_tmp_rhs17).exp;
      let _497_valueOrError0 = Std_JSON_Deserializer.__default.ToInt(_493_minus, _494_num);
      if ((_497_valueOrError0).IsFailure()) {
        return (_497_valueOrError0).PropagateFailure();
      } else {
        let _498_n = (_497_valueOrError0).Extract();
        let _499_valueOrError1 = function (_source17) {
          if (_source17.is_Empty) {
            return Std_Wrappers.Result.create_Success(_dafny.ZERO);
          } else {
            let _500___mcc_h0 = (_source17).t;
            let _source18 = _500___mcc_h0;
            let _501___mcc_h1 = (_source18).e;
            let _502___mcc_h2 = (_source18).sign;
            let _503___mcc_h3 = (_source18).num;
            let _504_num = _503___mcc_h3;
            let _505_sign = _502___mcc_h2;
            return Std_JSON_Deserializer.__default.ToInt(_505_sign, _504_num);
          }
        }(_496_exp);
        if ((_499_valueOrError1).IsFailure()) {
          return (_499_valueOrError1).PropagateFailure();
        } else {
          let _506_e10 = (_499_valueOrError1).Extract();
          let _source19 = _495_frac;
          if (_source19.is_Empty) {
            return Std_Wrappers.Result.create_Success(Std_JSON_Values.Decimal.create_Decimal(_498_n, _506_e10));
          } else {
            let _507___mcc_h4 = (_source19).t;
            let _source20 = _507___mcc_h4;
            let _508___mcc_h5 = (_source20).period;
            let _509___mcc_h6 = (_source20).num;
            let _510_num = _509___mcc_h6;
            let _511_pow10 = new BigNumber((_510_num).Length());
            let _512_valueOrError2 = Std_JSON_Deserializer.__default.ToInt(_493_minus, _510_num);
            if ((_512_valueOrError2).IsFailure()) {
              return (_512_valueOrError2).PropagateFailure();
            } else {
              let _513_frac = (_512_valueOrError2).Extract();
              return Std_Wrappers.Result.create_Success(Std_JSON_Values.Decimal.create_Decimal(((_498_n).multipliedBy(Std_Arithmetic_Power.__default.Pow(new BigNumber(10), _511_pow10))).plus(_513_frac), (_506_e10).minus(_511_pow10)));
            }
          }
        }
      }
    };
    static KeyValue(js) {
      let _514_valueOrError0 = Std_JSON_Deserializer.__default.String((js).dtor_k);
      if ((_514_valueOrError0).IsFailure()) {
        return (_514_valueOrError0).PropagateFailure();
      } else {
        let _515_k = (_514_valueOrError0).Extract();
        let _516_valueOrError1 = Std_JSON_Deserializer.__default.Value((js).dtor_v);
        if ((_516_valueOrError1).IsFailure()) {
          return (_516_valueOrError1).PropagateFailure();
        } else {
          let _517_v = (_516_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(_dafny.Tuple.of(_515_k, _517_v));
        }
      }
    };
    static Object(js) {
      return Std_Collections_Seq.__default.MapWithResult(((_518_js) => function (_519_d) {
        return Std_JSON_Deserializer.__default.KeyValue((_519_d).dtor_t);
      })(js), (js).dtor_data);
    };
    static Array(js) {
      return Std_Collections_Seq.__default.MapWithResult(((_520_js) => function (_521_d) {
        return Std_JSON_Deserializer.__default.Value((_521_d).dtor_t);
      })(js), (js).dtor_data);
    };
    static Value(js) {
      let _source21 = js;
      if (_source21.is_Null) {
        let _522___mcc_h0 = (_source21).n;
        return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Null());
      } else if (_source21.is_Bool) {
        let _523___mcc_h1 = (_source21).b;
        let _524_b = _523___mcc_h1;
        return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Bool(Std_JSON_Deserializer.__default.Bool(_524_b)));
      } else if (_source21.is_String) {
        let _525___mcc_h2 = (_source21).str;
        let _526_str = _525___mcc_h2;
        let _527_valueOrError0 = Std_JSON_Deserializer.__default.String(_526_str);
        if ((_527_valueOrError0).IsFailure()) {
          return (_527_valueOrError0).PropagateFailure();
        } else {
          let _528_s = (_527_valueOrError0).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_String(_528_s));
        }
      } else if (_source21.is_Number) {
        let _529___mcc_h3 = (_source21).num;
        let _530_dec = _529___mcc_h3;
        let _531_valueOrError1 = Std_JSON_Deserializer.__default.Number(_530_dec);
        if ((_531_valueOrError1).IsFailure()) {
          return (_531_valueOrError1).PropagateFailure();
        } else {
          let _532_n = (_531_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Number(_532_n));
        }
      } else if (_source21.is_Object) {
        let _533___mcc_h4 = (_source21).obj;
        let _534_obj = _533___mcc_h4;
        let _535_valueOrError2 = Std_JSON_Deserializer.__default.Object(_534_obj);
        if ((_535_valueOrError2).IsFailure()) {
          return (_535_valueOrError2).PropagateFailure();
        } else {
          let _536_o = (_535_valueOrError2).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Object(_536_o));
        }
      } else {
        let _537___mcc_h5 = (_source21).arr;
        let _538_arr = _537___mcc_h5;
        let _539_valueOrError3 = Std_JSON_Deserializer.__default.Array(_538_arr);
        if ((_539_valueOrError3).IsFailure()) {
          return (_539_valueOrError3).PropagateFailure();
        } else {
          let _540_a = (_539_valueOrError3).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Array(_540_a));
        }
      }
    };
    static JSON(js) {
      return Std_JSON_Deserializer.__default.Value((js).dtor_t);
    };
    static get HEX__TABLE__16() {
      return Std_JSON_Deserializer_Uint16StrConversion.__default.charToDigit;
    };
    static get DIGITS() {
      return Std_JSON_ByteStrConversion.__default.charToDigit;
    };
    static get MINUS() {
      return (new _dafny.CodePoint('-'.codePointAt(0))).value;
    };
  };
  return $module;
})(); // end of module Std_JSON_Deserializer
let Std_JSON_ConcreteSyntax_Spec = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ConcreteSyntax.Spec._default";
    }
    _parentTraits() {
      return [];
    }
    static View(v) {
      return (v).Bytes();
    };
    static Structural(self, fT) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_before), (fT)((self).dtor_t)), Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_after));
    };
    static StructuralView(self) {
      return Std_JSON_ConcreteSyntax_Spec.__default.Structural(self, Std_JSON_ConcreteSyntax_Spec.__default.View);
    };
    static Maybe(self, fT) {
      if ((self).is_Empty) {
        return _dafny.Seq.of();
      } else {
        return (fT)((self).dtor_t);
      }
    };
    static ConcatBytes(ts, fT) {
      let _541___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((ts).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_541___accumulator, _dafny.Seq.of());
        } else {
          _541___accumulator = _dafny.Seq.Concat(_541___accumulator, (fT)((ts)[_dafny.ZERO]));
          let _in95 = (ts).slice(_dafny.ONE);
          let _in96 = fT;
          ts = _in95;
          fT = _in96;
          continue TAIL_CALL_START;
        }
      }
    };
    static Bracketed(self, fDatum) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.StructuralView((self).dtor_l), Std_JSON_ConcreteSyntax_Spec.__default.ConcatBytes((self).dtor_data, fDatum)), Std_JSON_ConcreteSyntax_Spec.__default.StructuralView((self).dtor_r));
    };
    static KeyValue(self) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.String((self).dtor_k), Std_JSON_ConcreteSyntax_Spec.__default.StructuralView((self).dtor_colon)), Std_JSON_ConcreteSyntax_Spec.__default.Value((self).dtor_v));
    };
    static Frac(self) {
      return _dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_period), Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_num));
    };
    static Exp(self) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_e), Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_sign)), Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_num));
    };
    static Number(self) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_minus), Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_num)), Std_JSON_ConcreteSyntax_Spec.__default.Maybe((self).dtor_frac, Std_JSON_ConcreteSyntax_Spec.__default.Frac)), Std_JSON_ConcreteSyntax_Spec.__default.Maybe((self).dtor_exp, Std_JSON_ConcreteSyntax_Spec.__default.Exp));
    };
    static String(self) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_lq), Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_contents)), Std_JSON_ConcreteSyntax_Spec.__default.View((self).dtor_rq));
    };
    static CommaSuffix(c) {
      return Std_JSON_ConcreteSyntax_Spec.__default.Maybe(c, Std_JSON_ConcreteSyntax_Spec.__default.StructuralView);
    };
    static Member(self) {
      return _dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.KeyValue((self).dtor_t), Std_JSON_ConcreteSyntax_Spec.__default.CommaSuffix((self).dtor_suffix));
    };
    static Item(self) {
      return _dafny.Seq.Concat(Std_JSON_ConcreteSyntax_Spec.__default.Value((self).dtor_t), Std_JSON_ConcreteSyntax_Spec.__default.CommaSuffix((self).dtor_suffix));
    };
    static Object(obj) {
      return Std_JSON_ConcreteSyntax_Spec.__default.Bracketed(obj, ((_542_obj) => function (_543_d) {
        return Std_JSON_ConcreteSyntax_Spec.__default.Member(_543_d);
      })(obj));
    };
    static Array(arr) {
      return Std_JSON_ConcreteSyntax_Spec.__default.Bracketed(arr, ((_544_arr) => function (_545_d) {
        return Std_JSON_ConcreteSyntax_Spec.__default.Item(_545_d);
      })(arr));
    };
    static Value(self) {
      let _source22 = self;
      if (_source22.is_Null) {
        let _546___mcc_h0 = (_source22).n;
        let _547_n = _546___mcc_h0;
        return Std_JSON_ConcreteSyntax_Spec.__default.View(_547_n);
      } else if (_source22.is_Bool) {
        let _548___mcc_h1 = (_source22).b;
        let _549_b = _548___mcc_h1;
        return Std_JSON_ConcreteSyntax_Spec.__default.View(_549_b);
      } else if (_source22.is_String) {
        let _550___mcc_h2 = (_source22).str;
        let _551_str = _550___mcc_h2;
        return Std_JSON_ConcreteSyntax_Spec.__default.String(_551_str);
      } else if (_source22.is_Number) {
        let _552___mcc_h3 = (_source22).num;
        let _553_num = _552___mcc_h3;
        return Std_JSON_ConcreteSyntax_Spec.__default.Number(_553_num);
      } else if (_source22.is_Object) {
        let _554___mcc_h4 = (_source22).obj;
        let _555_obj = _554___mcc_h4;
        return Std_JSON_ConcreteSyntax_Spec.__default.Object(_555_obj);
      } else {
        let _556___mcc_h5 = (_source22).arr;
        let _557_arr = _556___mcc_h5;
        return Std_JSON_ConcreteSyntax_Spec.__default.Array(_557_arr);
      }
    };
    static JSON(js) {
      return Std_JSON_ConcreteSyntax_Spec.__default.Structural(js, Std_JSON_ConcreteSyntax_Spec.__default.Value);
    };
  };
  return $module;
})(); // end of module Std_JSON_ConcreteSyntax_Spec
let Std_JSON_ConcreteSyntax_SpecProperties = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON_ConcreteSyntax_SpecProperties
let Std_JSON_ConcreteSyntax = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON_ConcreteSyntax
let Std_JSON_ZeroCopy_Serializer = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Serializer._default";
    }
    _parentTraits() {
      return [];
    }
    static Serialize(js) {
      let rbs = Std_Wrappers.Result.Default([]);
      let _558_writer;
      _558_writer = Std_JSON_ZeroCopy_Serializer.__default.Text(js);
      let _559_valueOrError0 = Std_Wrappers.OutcomeResult.Default();
      _559_valueOrError0 = Std_Wrappers.__default.Need((_558_writer).Unsaturated_q, Std_JSON_Errors.SerializationError.create_OutOfMemory());
      if ((_559_valueOrError0).IsFailure()) {
        rbs = (_559_valueOrError0).PropagateFailure();
        return rbs;
      }
      let _560_bs;
      let _out6;
      _out6 = (_558_writer).ToArray();
      _560_bs = _out6;
      rbs = Std_Wrappers.Result.create_Success(_560_bs);
      return rbs;
      return rbs;
    }
    static SerializeTo(js, dest) {
      let len = Std_Wrappers.Result.Default(0);
      let _561_writer;
      _561_writer = Std_JSON_ZeroCopy_Serializer.__default.Text(js);
      let _562_valueOrError0 = Std_Wrappers.OutcomeResult.Default();
      _562_valueOrError0 = Std_Wrappers.__default.Need((_561_writer).Unsaturated_q, Std_JSON_Errors.SerializationError.create_OutOfMemory());
      if ((_562_valueOrError0).IsFailure()) {
        len = (_562_valueOrError0).PropagateFailure();
        return len;
      }
      let _563_valueOrError1 = Std_Wrappers.OutcomeResult.Default();
      _563_valueOrError1 = Std_Wrappers.__default.Need((new BigNumber((_561_writer).dtor_length)).isLessThanOrEqualTo(new BigNumber((dest).length)), Std_JSON_Errors.SerializationError.create_OutOfMemory());
      if ((_563_valueOrError1).IsFailure()) {
        len = (_563_valueOrError1).PropagateFailure();
        return len;
      }
      (_561_writer).CopyTo(dest);
      len = Std_Wrappers.Result.create_Success((_561_writer).dtor_length);
      return len;
      return len;
    }
    static Text(js) {
      return Std_JSON_ZeroCopy_Serializer.__default.JSON(js, Std_JSON_Utils_Views_Writers.Writer__.Empty);
    };
    static JSON(js, writer) {
      return (((writer).Append((js).dtor_before)).Then(((_564_js) => function (_565_wr) {
        return Std_JSON_ZeroCopy_Serializer.__default.Value((_564_js).dtor_t, _565_wr);
      })(js))).Append((js).dtor_after);
    };
    static Value(v, writer) {
      let _source23 = v;
      if (_source23.is_Null) {
        let _566___mcc_h0 = (_source23).n;
        let _567_n = _566___mcc_h0;
        let _568_wr = (writer).Append(_567_n);
        return _568_wr;
      } else if (_source23.is_Bool) {
        let _569___mcc_h1 = (_source23).b;
        let _570_b = _569___mcc_h1;
        let _571_wr = (writer).Append(_570_b);
        return _571_wr;
      } else if (_source23.is_String) {
        let _572___mcc_h2 = (_source23).str;
        let _573_str = _572___mcc_h2;
        let _574_wr = Std_JSON_ZeroCopy_Serializer.__default.String(_573_str, writer);
        return _574_wr;
      } else if (_source23.is_Number) {
        let _575___mcc_h3 = (_source23).num;
        let _576_num = _575___mcc_h3;
        let _577_wr = Std_JSON_ZeroCopy_Serializer.__default.Number(_576_num, writer);
        return _577_wr;
      } else if (_source23.is_Object) {
        let _578___mcc_h4 = (_source23).obj;
        let _579_obj = _578___mcc_h4;
        let _580_wr = Std_JSON_ZeroCopy_Serializer.__default.Object(_579_obj, writer);
        return _580_wr;
      } else {
        let _581___mcc_h5 = (_source23).arr;
        let _582_arr = _581___mcc_h5;
        let _583_wr = Std_JSON_ZeroCopy_Serializer.__default.Array(_582_arr, writer);
        return _583_wr;
      }
    };
    static String(str, writer) {
      return (((writer).Append((str).dtor_lq)).Append((str).dtor_contents)).Append((str).dtor_rq);
    };
    static Number(num, writer) {
      let _584_wr1 = ((writer).Append((num).dtor_minus)).Append((num).dtor_num);
      let _585_wr2 = ((((num).dtor_frac).is_NonEmpty) ? (((_584_wr1).Append((((num).dtor_frac).dtor_t).dtor_period)).Append((((num).dtor_frac).dtor_t).dtor_num)) : (_584_wr1));
      let _586_wr3 = ((((num).dtor_exp).is_NonEmpty) ? ((((_585_wr2).Append((((num).dtor_exp).dtor_t).dtor_e)).Append((((num).dtor_exp).dtor_t).dtor_sign)).Append((((num).dtor_exp).dtor_t).dtor_num)) : (_585_wr2));
      let _587_wr = _586_wr3;
      return _587_wr;
    };
    static StructuralView(st, writer) {
      return (((writer).Append((st).dtor_before)).Append((st).dtor_t)).Append((st).dtor_after);
    };
    static Object(obj, writer) {
      let _588_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((obj).dtor_l, writer);
      let _589_wr = Std_JSON_ZeroCopy_Serializer.__default.Members(obj, _588_wr);
      let _590_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((obj).dtor_r, _589_wr);
      return _590_wr;
    };
    static Array(arr, writer) {
      let _591_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((arr).dtor_l, writer);
      let _592_wr = Std_JSON_ZeroCopy_Serializer.__default.Items(arr, _591_wr);
      let _593_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((arr).dtor_r, _592_wr);
      return _593_wr;
    };
    static Members(obj, writer) {
      let wr = Std_JSON_Utils_Views_Writers.Writer.Default;
      let _out7;
      _out7 = Std_JSON_ZeroCopy_Serializer.__default.MembersImpl(obj, writer);
      wr = _out7;
      return wr;
    }
    static Items(arr, writer) {
      let wr = Std_JSON_Utils_Views_Writers.Writer.Default;
      let _out8;
      _out8 = Std_JSON_ZeroCopy_Serializer.__default.ItemsImpl(arr, writer);
      wr = _out8;
      return wr;
    }
    static MembersImpl(obj, writer) {
      let wr = Std_JSON_Utils_Views_Writers.Writer.Default;
      wr = writer;
      let _594_members;
      _594_members = (obj).dtor_data;
      let _hi1 = new BigNumber((_594_members).length);
      for (let _595_i = _dafny.ZERO; _595_i.isLessThan(_hi1); _595_i = _595_i.plus(_dafny.ONE)) {
        wr = Std_JSON_ZeroCopy_Serializer.__default.Member((_594_members)[_595_i], wr);
      }
      return wr;
    }
    static ItemsImpl(arr, writer) {
      let wr = Std_JSON_Utils_Views_Writers.Writer.Default;
      wr = writer;
      let _596_items;
      _596_items = (arr).dtor_data;
      let _hi2 = new BigNumber((_596_items).length);
      for (let _597_i = _dafny.ZERO; _597_i.isLessThan(_hi2); _597_i = _597_i.plus(_dafny.ONE)) {
        wr = Std_JSON_ZeroCopy_Serializer.__default.Item((_596_items)[_597_i], wr);
      }
      return wr;
    }
    static Member(m, writer) {
      let _598_wr = Std_JSON_ZeroCopy_Serializer.__default.String(((m).dtor_t).dtor_k, writer);
      let _599_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView(((m).dtor_t).dtor_colon, _598_wr);
      let _600_wr = Std_JSON_ZeroCopy_Serializer.__default.Value(((m).dtor_t).dtor_v, _599_wr);
      let _601_wr = ((((m).dtor_suffix).is_Empty) ? (_600_wr) : (Std_JSON_ZeroCopy_Serializer.__default.StructuralView(((m).dtor_suffix).dtor_t, _600_wr)));
      return _601_wr;
    };
    static Item(m, writer) {
      let _602_wr = Std_JSON_ZeroCopy_Serializer.__default.Value((m).dtor_t, writer);
      let _603_wr = ((((m).dtor_suffix).is_Empty) ? (_602_wr) : (Std_JSON_ZeroCopy_Serializer.__default.StructuralView(((m).dtor_suffix).dtor_t, _602_wr)));
      return _603_wr;
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Serializer
let Std_JSON_ZeroCopy_Deserializer_Core = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.Core._default";
    }
    _parentTraits() {
      return [];
    }
    static Get(cs, err) {
      let _604_valueOrError0 = (cs).Get(err);
      if ((_604_valueOrError0).IsFailure()) {
        return (_604_valueOrError0).PropagateFailure();
      } else {
        let _605_cs = (_604_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_605_cs).Split());
      }
    };
    static WS(cs) {
      let sp = Std_JSON_Utils_Cursors.Split.Default(Std_JSON_Grammar.jblanks.Default);
      let _606_point_k;
      _606_point_k = (cs).dtor_point;
      let _607_end;
      _607_end = (cs).dtor_end;
      while (((_606_point_k) < (_607_end)) && (Std_JSON_Grammar.__default.Blank_q(((cs).dtor_s)[_606_point_k]))) {
        _606_point_k = (_606_point_k) + (1);
      }
      sp = (Std_JSON_Utils_Cursors.Cursor__.create_Cursor((cs).dtor_s, (cs).dtor_beg, _606_point_k, (cs).dtor_end)).Split();
      return sp;
      return sp;
    }
    static Structural(cs, parser) {
      let _let_tmp_rhs18 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(cs);
      let _608_before = (_let_tmp_rhs18).t;
      let _609_cs = (_let_tmp_rhs18).cs;
      let _610_valueOrError0 = ((parser))(_609_cs);
      if ((_610_valueOrError0).IsFailure()) {
        return (_610_valueOrError0).PropagateFailure();
      } else {
        let _let_tmp_rhs19 = (_610_valueOrError0).Extract();
        let _611_val = (_let_tmp_rhs19).t;
        let _612_cs = (_let_tmp_rhs19).cs;
        let _let_tmp_rhs20 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(_612_cs);
        let _613_after = (_let_tmp_rhs20).t;
        let _614_cs = (_let_tmp_rhs20).cs;
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Structural.create_Structural(_608_before, _611_val, _613_after), _614_cs));
      }
    };
    static TryStructural(cs) {
      let _let_tmp_rhs21 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(cs);
      let _615_before = (_let_tmp_rhs21).t;
      let _616_cs = (_let_tmp_rhs21).cs;
      let _let_tmp_rhs22 = ((_616_cs).SkipByte()).Split();
      let _617_val = (_let_tmp_rhs22).t;
      let _618_cs = (_let_tmp_rhs22).cs;
      let _let_tmp_rhs23 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(_618_cs);
      let _619_after = (_let_tmp_rhs23).t;
      let _620_cs = (_let_tmp_rhs23).cs;
      return Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Structural.create_Structural(_615_before, _617_val, _619_after), _620_cs);
    };
    static get SpecView() {
      return function (_621_v) {
        return Std_JSON_ConcreteSyntax_Spec.__default.View(_621_v);
      };
    };
  };

  $module.jopt = class jopt {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of());
    }
    static get Default() {
      return Std_JSON_ZeroCopy_Deserializer_Core.jopt.Witness;
    }
  };

  $module.ValueParser = class ValueParser {
    constructor () {
    }
    static get Default() {
      return Std_JSON_Utils_Parsers.SubParser.Default;
    }
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_Core
let Std_JSON_ZeroCopy_Deserializer_Strings = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.Strings._default";
    }
    _parentTraits() {
      return [];
    }
    static StringBody(cs) {
      let pr = Std_Wrappers.Result.Default(Std_JSON_Utils_Cursors.Cursor.Default);
      let _622_escaped;
      _622_escaped = false;
      let _hi3 = (cs).dtor_end;
      for (let _623_point_k = (cs).dtor_point; _623_point_k < _hi3; _623_point_k++) {
        let _624_byte;
        _624_byte = ((cs).dtor_s)[_623_point_k];
        if (((_624_byte) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) && (!(_622_escaped))) {
          pr = Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Cursor__.create_Cursor((cs).dtor_s, (cs).dtor_beg, _623_point_k, (cs).dtor_end));
          return pr;
        } else if ((_624_byte) === ((new _dafny.CodePoint('\\'.codePointAt(0))).value)) {
          _622_escaped = !(_622_escaped);
        } else {
          _622_escaped = false;
        }
      }
      pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
      return pr;
      return pr;
    }
    static Quote(cs) {
      let _625_valueOrError0 = (cs).AssertChar(new _dafny.CodePoint('\"'.codePointAt(0)));
      if ((_625_valueOrError0).IsFailure()) {
        return (_625_valueOrError0).PropagateFailure();
      } else {
        let _626_cs = (_625_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_626_cs).Split());
      }
    };
    static String(cs) {
      let _627_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.Quote(cs);
      if ((_627_valueOrError0).IsFailure()) {
        return (_627_valueOrError0).PropagateFailure();
      } else {
        let _let_tmp_rhs24 = (_627_valueOrError0).Extract();
        let _628_lq = (_let_tmp_rhs24).t;
        let _629_cs = (_let_tmp_rhs24).cs;
        let _630_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.StringBody(_629_cs);
        if ((_630_valueOrError1).IsFailure()) {
          return (_630_valueOrError1).PropagateFailure();
        } else {
          let _631_contents = (_630_valueOrError1).Extract();
          let _let_tmp_rhs25 = (_631_contents).Split();
          let _632_contents = (_let_tmp_rhs25).t;
          let _633_cs = (_let_tmp_rhs25).cs;
          let _634_valueOrError2 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.Quote(_633_cs);
          if ((_634_valueOrError2).IsFailure()) {
            return (_634_valueOrError2).PropagateFailure();
          } else {
            let _let_tmp_rhs26 = (_634_valueOrError2).Extract();
            let _635_rq = (_let_tmp_rhs26).t;
            let _636_cs = (_let_tmp_rhs26).cs;
            return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.jstring.create_JString(_628_lq, _632_contents, _635_rq), _636_cs));
          }
        }
      }
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_Strings
let Std_JSON_ZeroCopy_Deserializer_Numbers = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.Numbers._default";
    }
    _parentTraits() {
      return [];
    }
    static Digits(cs) {
      return ((cs).SkipWhile(Std_JSON_Grammar.__default.Digit_q)).Split();
    };
    static NonEmptyDigits(cs) {
      let _637_sp = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Digits(cs);
      if (((_637_sp).dtor_t).Empty_q) {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_OtherError(Std_JSON_Errors.DeserializationError.create_EmptyNumber()));
      } else {
        return Std_Wrappers.Result.create_Success(_637_sp);
      }
    };
    static NonZeroInt(cs) {
      return Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonEmptyDigits(cs);
    };
    static OptionalMinus(cs) {
      return ((cs).SkipIf(function (_638_c) {
        return (_638_c) === ((new _dafny.CodePoint('-'.codePointAt(0))).value);
      })).Split();
    };
    static OptionalSign(cs) {
      return ((cs).SkipIf(function (_639_c) {
        return ((_639_c) === ((new _dafny.CodePoint('-'.codePointAt(0))).value)) || ((_639_c) === ((new _dafny.CodePoint('+'.codePointAt(0))).value));
      })).Split();
    };
    static TrimmedInt(cs) {
      let _640_sp = ((cs).SkipIf(function (_641_c) {
        return (_641_c) === ((new _dafny.CodePoint('0'.codePointAt(0))).value);
      })).Split();
      if (((_640_sp).dtor_t).Empty_q) {
        return Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonZeroInt((_640_sp).dtor_cs);
      } else {
        return Std_Wrappers.Result.create_Success(_640_sp);
      }
    };
    static Exp(cs) {
      let _let_tmp_rhs27 = ((cs).SkipIf(function (_642_c) {
        return ((_642_c) === ((new _dafny.CodePoint('e'.codePointAt(0))).value)) || ((_642_c) === ((new _dafny.CodePoint('E'.codePointAt(0))).value));
      })).Split();
      let _643_e = (_let_tmp_rhs27).t;
      let _644_cs = (_let_tmp_rhs27).cs;
      if ((_643_e).Empty_q) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_Empty(), _644_cs));
      } else {
        let _let_tmp_rhs28 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.OptionalSign(_644_cs);
        let _645_sign = (_let_tmp_rhs28).t;
        let _646_cs = (_let_tmp_rhs28).cs;
        let _647_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonEmptyDigits(_646_cs);
        if ((_647_valueOrError0).IsFailure()) {
          return (_647_valueOrError0).PropagateFailure();
        } else {
          let _let_tmp_rhs29 = (_647_valueOrError0).Extract();
          let _648_num = (_let_tmp_rhs29).t;
          let _649_cs = (_let_tmp_rhs29).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_NonEmpty(Std_JSON_Grammar.jexp.create_JExp(_643_e, _645_sign, _648_num)), _649_cs));
        }
      }
    };
    static Frac(cs) {
      let _let_tmp_rhs30 = ((cs).SkipIf(function (_650_c) {
        return (_650_c) === ((new _dafny.CodePoint('.'.codePointAt(0))).value);
      })).Split();
      let _651_period = (_let_tmp_rhs30).t;
      let _652_cs = (_let_tmp_rhs30).cs;
      if ((_651_period).Empty_q) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_Empty(), _652_cs));
      } else {
        let _653_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonEmptyDigits(_652_cs);
        if ((_653_valueOrError0).IsFailure()) {
          return (_653_valueOrError0).PropagateFailure();
        } else {
          let _let_tmp_rhs31 = (_653_valueOrError0).Extract();
          let _654_num = (_let_tmp_rhs31).t;
          let _655_cs = (_let_tmp_rhs31).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_NonEmpty(Std_JSON_Grammar.jfrac.create_JFrac(_651_period, _654_num)), _655_cs));
        }
      }
    };
    static NumberFromParts(minus, num, frac, exp) {
      let _656_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.jnumber.create_JNumber((minus).dtor_t, (num).dtor_t, (frac).dtor_t, (exp).dtor_t), (exp).dtor_cs);
      return _656_sp;
    };
    static Number(cs) {
      let _657_minus = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.OptionalMinus(cs);
      let _658_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.TrimmedInt((_657_minus).dtor_cs);
      if ((_658_valueOrError0).IsFailure()) {
        return (_658_valueOrError0).PropagateFailure();
      } else {
        let _659_num = (_658_valueOrError0).Extract();
        let _660_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Frac((_659_num).dtor_cs);
        if ((_660_valueOrError1).IsFailure()) {
          return (_660_valueOrError1).PropagateFailure();
        } else {
          let _661_frac = (_660_valueOrError1).Extract();
          let _662_valueOrError2 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Exp((_661_frac).dtor_cs);
          if ((_662_valueOrError2).IsFailure()) {
            return (_662_valueOrError2).PropagateFailure();
          } else {
            let _663_exp = (_662_valueOrError2).Extract();
            return Std_Wrappers.Result.create_Success(Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NumberFromParts(_657_minus, _659_num, _661_frac, _663_exp));
          }
        }
      }
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_Numbers
let Std_JSON_ZeroCopy_Deserializer_ObjectParams = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.ObjectParams._default";
    }
    _parentTraits() {
      return [];
    }
    static Colon(cs) {
      let _664_valueOrError0 = (cs).AssertChar(new _dafny.CodePoint(':'.codePointAt(0)));
      if ((_664_valueOrError0).IsFailure()) {
        return (_664_valueOrError0).PropagateFailure();
      } else {
        let _665_cs = (_664_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_665_cs).Split());
      }
    };
    static KeyValueFromParts(k, colon, v) {
      let _666_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.jKeyValue.create_KeyValue((k).dtor_t, (colon).dtor_t, (v).dtor_t), (v).dtor_cs);
      return _666_sp;
    };
    static ElementSpec(t) {
      return Std_JSON_ConcreteSyntax_Spec.__default.KeyValue(t);
    };
    static Element(cs, json) {
      let _667_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.String(cs);
      if ((_667_valueOrError0).IsFailure()) {
        return (_667_valueOrError0).PropagateFailure();
      } else {
        let _668_k = (_667_valueOrError0).Extract();
        let _669_p = Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.Colon;
        let _670_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural((_668_k).dtor_cs, _669_p);
        if ((_670_valueOrError1).IsFailure()) {
          return (_670_valueOrError1).PropagateFailure();
        } else {
          let _671_colon = (_670_valueOrError1).Extract();
          let _672_valueOrError2 = ((json))((_671_colon).dtor_cs);
          if ((_672_valueOrError2).IsFailure()) {
            return (_672_valueOrError2).PropagateFailure();
          } else {
            let _673_v = (_672_valueOrError2).Extract();
            let _674_kv = Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.KeyValueFromParts(_668_k, _671_colon, _673_v);
            return Std_Wrappers.Result.create_Success(_674_kv);
          }
        }
      }
    };
    static get OPEN() {
      return (new _dafny.CodePoint('{'.codePointAt(0))).value;
    };
    static get CLOSE() {
      return (new _dafny.CodePoint('}'.codePointAt(0))).value;
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_ObjectParams
let Std_JSON_ZeroCopy_Deserializer_Objects = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.Objects._default";
    }
    _parentTraits() {
      return [];
    }
    static Object(cs, json) {
      let _675_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Objects.__default.Bracketed(cs, json);
      if ((_675_valueOrError0).IsFailure()) {
        return (_675_valueOrError0).PropagateFailure();
      } else {
        let _676_sp = (_675_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_676_sp);
      }
    };
    static Open(cs) {
      let _677_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.OPEN);
      if ((_677_valueOrError0).IsFailure()) {
        return (_677_valueOrError0).PropagateFailure();
      } else {
        let _678_cs = (_677_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_678_cs).Split());
      }
    };
    static Close(cs) {
      let _679_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE);
      if ((_679_valueOrError0).IsFailure()) {
        return (_679_valueOrError0).PropagateFailure();
      } else {
        let _680_cs = (_679_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_680_cs).Split());
      }
    };
    static BracketedFromParts(open, elems, close) {
      let _681_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Bracketed.create_Bracketed((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _681_sp;
    };
    static AppendWithSuffix(elems, elem, sep) {
      let _682_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_NonEmpty((sep).dtor_t));
      let _683_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_682_suffixed)), (sep).dtor_cs);
      return _683_elems_k;
    };
    static AppendLast(elems, elem, sep) {
      let _684_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_Empty());
      let _685_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_684_suffixed)), (elem).dtor_cs);
      return _685_elems_k;
    };
    static Elements(json, open, elems) {
      TAIL_CALL_START: while (true) {
        let _686_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.Element((elems).dtor_cs, json);
        if ((_686_valueOrError0).IsFailure()) {
          return (_686_valueOrError0).PropagateFailure();
        } else {
          let _687_elem = (_686_valueOrError0).Extract();
          if (((_687_elem).dtor_cs).EOF_q) {
            return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
          } else {
            let _688_sep = Std_JSON_ZeroCopy_Deserializer_Core.__default.TryStructural((_687_elem).dtor_cs);
            let _689_s0 = (((_688_sep).dtor_t).dtor_t).Peek();
            if (((_689_s0) === (Std_JSON_ZeroCopy_Deserializer_Objects.__default.SEPARATOR)) && (((((_688_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _690_sep = _688_sep;
              let _691_elems = Std_JSON_ZeroCopy_Deserializer_Objects.__default.AppendWithSuffix(elems, _687_elem, _690_sep);
              let _in97 = json;
              let _in98 = open;
              let _in99 = _691_elems;
              json = _in97;
              open = _in98;
              elems = _in99;
              continue TAIL_CALL_START;
            } else if (((_689_s0) === (Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE)) && (((((_688_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _692_sep = _688_sep;
              let _693_elems_k = Std_JSON_ZeroCopy_Deserializer_Objects.__default.AppendLast(elems, _687_elem, _692_sep);
              let _694_bracketed = Std_JSON_ZeroCopy_Deserializer_Objects.__default.BracketedFromParts(open, _693_elems_k, _692_sep);
              return Std_Wrappers.Result.create_Success(_694_bracketed);
            } else {
              let _695_separator = Std_JSON_ZeroCopy_Deserializer_Objects.__default.SEPARATOR;
              let _696_pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_ExpectingAnyByte(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE, _695_separator), _689_s0));
              return _696_pr;
            }
          }
        }
      }
    };
    static Bracketed(cs, json) {
      let _697_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural(cs, Std_JSON_ZeroCopy_Deserializer_Objects.__default.Open);
      if ((_697_valueOrError0).IsFailure()) {
        return (_697_valueOrError0).PropagateFailure();
      } else {
        let _698_open = (_697_valueOrError0).Extract();
        let _699_elems = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.of(), (_698_open).dtor_cs);
        if ((((_698_open).dtor_cs).Peek()) === (Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE)) {
          let _700_p = Std_JSON_ZeroCopy_Deserializer_Objects.__default.Close;
          let _701_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural((_698_open).dtor_cs, _700_p);
          if ((_701_valueOrError1).IsFailure()) {
            return (_701_valueOrError1).PropagateFailure();
          } else {
            let _702_close = (_701_valueOrError1).Extract();
            return Std_Wrappers.Result.create_Success(Std_JSON_ZeroCopy_Deserializer_Objects.__default.BracketedFromParts(_698_open, _699_elems, _702_close));
          }
        } else {
          return Std_JSON_ZeroCopy_Deserializer_Objects.__default.Elements(json, _698_open, _699_elems);
        }
      }
    };
    static get SpecViewOpen() {
      return Std_JSON_ZeroCopy_Deserializer_Core.__default.SpecView;
    };
    static get SpecViewClose() {
      return Std_JSON_ZeroCopy_Deserializer_Core.__default.SpecView;
    };
    static get SEPARATOR() {
      return (new _dafny.CodePoint(','.codePointAt(0))).value;
    };
  };

  $module.jopen = class jopen {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.OPEN));
    }
    static get Default() {
      return Std_JSON_ZeroCopy_Deserializer_Objects.jopen.Witness;
    }
  };

  $module.jclose = class jclose {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE));
    }
    static get Default() {
      return Std_JSON_ZeroCopy_Deserializer_Objects.jclose.Witness;
    }
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_Objects
let Std_JSON_ZeroCopy_Deserializer_ArrayParams = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.ArrayParams._default";
    }
    _parentTraits() {
      return [];
    }
    static ElementSpec(t) {
      return Std_JSON_ConcreteSyntax_Spec.__default.Value(t);
    };
    static Element(cs, json) {
      return ((json))(cs);
    };
    static get OPEN() {
      return (new _dafny.CodePoint('['.codePointAt(0))).value;
    };
    static get CLOSE() {
      return (new _dafny.CodePoint(']'.codePointAt(0))).value;
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_ArrayParams
let Std_JSON_ZeroCopy_Deserializer_Arrays = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.Arrays._default";
    }
    _parentTraits() {
      return [];
    }
    static Array(cs, json) {
      let _703_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Bracketed(cs, json);
      if ((_703_valueOrError0).IsFailure()) {
        return (_703_valueOrError0).PropagateFailure();
      } else {
        let _704_sp = (_703_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_704_sp);
      }
    };
    static Open(cs) {
      let _705_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.OPEN);
      if ((_705_valueOrError0).IsFailure()) {
        return (_705_valueOrError0).PropagateFailure();
      } else {
        let _706_cs = (_705_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_706_cs).Split());
      }
    };
    static Close(cs) {
      let _707_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE);
      if ((_707_valueOrError0).IsFailure()) {
        return (_707_valueOrError0).PropagateFailure();
      } else {
        let _708_cs = (_707_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_708_cs).Split());
      }
    };
    static BracketedFromParts(open, elems, close) {
      let _709_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Bracketed.create_Bracketed((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _709_sp;
    };
    static AppendWithSuffix(elems, elem, sep) {
      let _710_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_NonEmpty((sep).dtor_t));
      let _711_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_710_suffixed)), (sep).dtor_cs);
      return _711_elems_k;
    };
    static AppendLast(elems, elem, sep) {
      let _712_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_Empty());
      let _713_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_712_suffixed)), (elem).dtor_cs);
      return _713_elems_k;
    };
    static Elements(json, open, elems) {
      TAIL_CALL_START: while (true) {
        let _714_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.Element((elems).dtor_cs, json);
        if ((_714_valueOrError0).IsFailure()) {
          return (_714_valueOrError0).PropagateFailure();
        } else {
          let _715_elem = (_714_valueOrError0).Extract();
          if (((_715_elem).dtor_cs).EOF_q) {
            return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
          } else {
            let _716_sep = Std_JSON_ZeroCopy_Deserializer_Core.__default.TryStructural((_715_elem).dtor_cs);
            let _717_s0 = (((_716_sep).dtor_t).dtor_t).Peek();
            if (((_717_s0) === (Std_JSON_ZeroCopy_Deserializer_Arrays.__default.SEPARATOR)) && (((((_716_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _718_sep = _716_sep;
              let _719_elems = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.AppendWithSuffix(elems, _715_elem, _718_sep);
              let _in100 = json;
              let _in101 = open;
              let _in102 = _719_elems;
              json = _in100;
              open = _in101;
              elems = _in102;
              continue TAIL_CALL_START;
            } else if (((_717_s0) === (Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE)) && (((((_716_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _720_sep = _716_sep;
              let _721_elems_k = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.AppendLast(elems, _715_elem, _720_sep);
              let _722_bracketed = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.BracketedFromParts(open, _721_elems_k, _720_sep);
              return Std_Wrappers.Result.create_Success(_722_bracketed);
            } else {
              let _723_separator = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.SEPARATOR;
              let _724_pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_ExpectingAnyByte(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE, _723_separator), _717_s0));
              return _724_pr;
            }
          }
        }
      }
    };
    static Bracketed(cs, json) {
      let _725_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural(cs, Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Open);
      if ((_725_valueOrError0).IsFailure()) {
        return (_725_valueOrError0).PropagateFailure();
      } else {
        let _726_open = (_725_valueOrError0).Extract();
        let _727_elems = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.of(), (_726_open).dtor_cs);
        if ((((_726_open).dtor_cs).Peek()) === (Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE)) {
          let _728_p = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Close;
          let _729_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural((_726_open).dtor_cs, _728_p);
          if ((_729_valueOrError1).IsFailure()) {
            return (_729_valueOrError1).PropagateFailure();
          } else {
            let _730_close = (_729_valueOrError1).Extract();
            return Std_Wrappers.Result.create_Success(Std_JSON_ZeroCopy_Deserializer_Arrays.__default.BracketedFromParts(_726_open, _727_elems, _730_close));
          }
        } else {
          return Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Elements(json, _726_open, _727_elems);
        }
      }
    };
    static get SpecViewOpen() {
      return Std_JSON_ZeroCopy_Deserializer_Core.__default.SpecView;
    };
    static get SpecViewClose() {
      return Std_JSON_ZeroCopy_Deserializer_Core.__default.SpecView;
    };
    static get SEPARATOR() {
      return (new _dafny.CodePoint(','.codePointAt(0))).value;
    };
  };

  $module.jopen = class jopen {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.OPEN));
    }
    static get Default() {
      return Std_JSON_ZeroCopy_Deserializer_Arrays.jopen.Witness;
    }
  };

  $module.jclose = class jclose {
    constructor () {
    }
    static get Witness() {
      return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE));
    }
    static get Default() {
      return Std_JSON_ZeroCopy_Deserializer_Arrays.jclose.Witness;
    }
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_Arrays
let Std_JSON_ZeroCopy_Deserializer_Constants = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.Constants._default";
    }
    _parentTraits() {
      return [];
    }
    static Constant(cs, expected) {
      let _731_valueOrError0 = (cs).AssertBytes(expected, 0);
      if ((_731_valueOrError0).IsFailure()) {
        return (_731_valueOrError0).PropagateFailure();
      } else {
        let _732_cs = (_731_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_732_cs).Split());
      }
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_Constants
let Std_JSON_ZeroCopy_Deserializer_Values = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.Values._default";
    }
    _parentTraits() {
      return [];
    }
    static Value(cs) {
      let _733_c = (cs).Peek();
      if ((_733_c) === ((new _dafny.CodePoint('{'.codePointAt(0))).value)) {
        let _734_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Objects.__default.Object(cs, Std_JSON_ZeroCopy_Deserializer_Values.__default.ValueParser(cs));
        if ((_734_valueOrError0).IsFailure()) {
          return (_734_valueOrError0).PropagateFailure();
        } else {
          let _let_tmp_rhs32 = (_734_valueOrError0).Extract();
          let _735_obj = (_let_tmp_rhs32).t;
          let _736_cs_k = (_let_tmp_rhs32).cs;
          let _737_v = Std_JSON_Grammar.Value.create_Object(_735_obj);
          let _738_sp = Std_JSON_Utils_Cursors.Split.create_SP(_737_v, _736_cs_k);
          return Std_Wrappers.Result.create_Success(_738_sp);
        }
      } else if ((_733_c) === ((new _dafny.CodePoint('['.codePointAt(0))).value)) {
        let _739_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Array(cs, Std_JSON_ZeroCopy_Deserializer_Values.__default.ValueParser(cs));
        if ((_739_valueOrError1).IsFailure()) {
          return (_739_valueOrError1).PropagateFailure();
        } else {
          let _let_tmp_rhs33 = (_739_valueOrError1).Extract();
          let _740_arr = (_let_tmp_rhs33).t;
          let _741_cs_k = (_let_tmp_rhs33).cs;
          let _742_v = Std_JSON_Grammar.Value.create_Array(_740_arr);
          let _743_sp = Std_JSON_Utils_Cursors.Split.create_SP(_742_v, _741_cs_k);
          return Std_Wrappers.Result.create_Success(_743_sp);
        }
      } else if ((_733_c) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) {
        let _744_valueOrError2 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.String(cs);
        if ((_744_valueOrError2).IsFailure()) {
          return (_744_valueOrError2).PropagateFailure();
        } else {
          let _let_tmp_rhs34 = (_744_valueOrError2).Extract();
          let _745_str = (_let_tmp_rhs34).t;
          let _746_cs_k = (_let_tmp_rhs34).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_String(_745_str), _746_cs_k));
        }
      } else if ((_733_c) === ((new _dafny.CodePoint('t'.codePointAt(0))).value)) {
        let _747_valueOrError3 = Std_JSON_ZeroCopy_Deserializer_Constants.__default.Constant(cs, Std_JSON_Grammar.__default.TRUE);
        if ((_747_valueOrError3).IsFailure()) {
          return (_747_valueOrError3).PropagateFailure();
        } else {
          let _let_tmp_rhs35 = (_747_valueOrError3).Extract();
          let _748_cst = (_let_tmp_rhs35).t;
          let _749_cs_k = (_let_tmp_rhs35).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_Bool(_748_cst), _749_cs_k));
        }
      } else if ((_733_c) === ((new _dafny.CodePoint('f'.codePointAt(0))).value)) {
        let _750_valueOrError4 = Std_JSON_ZeroCopy_Deserializer_Constants.__default.Constant(cs, Std_JSON_Grammar.__default.FALSE);
        if ((_750_valueOrError4).IsFailure()) {
          return (_750_valueOrError4).PropagateFailure();
        } else {
          let _let_tmp_rhs36 = (_750_valueOrError4).Extract();
          let _751_cst = (_let_tmp_rhs36).t;
          let _752_cs_k = (_let_tmp_rhs36).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_Bool(_751_cst), _752_cs_k));
        }
      } else if ((_733_c) === ((new _dafny.CodePoint('n'.codePointAt(0))).value)) {
        let _753_valueOrError5 = Std_JSON_ZeroCopy_Deserializer_Constants.__default.Constant(cs, Std_JSON_Grammar.__default.NULL);
        if ((_753_valueOrError5).IsFailure()) {
          return (_753_valueOrError5).PropagateFailure();
        } else {
          let _let_tmp_rhs37 = (_753_valueOrError5).Extract();
          let _754_cst = (_let_tmp_rhs37).t;
          let _755_cs_k = (_let_tmp_rhs37).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_Null(_754_cst), _755_cs_k));
        }
      } else {
        let _756_valueOrError6 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Number(cs);
        if ((_756_valueOrError6).IsFailure()) {
          return (_756_valueOrError6).PropagateFailure();
        } else {
          let _let_tmp_rhs38 = (_756_valueOrError6).Extract();
          let _757_num = (_let_tmp_rhs38).t;
          let _758_cs_k = (_let_tmp_rhs38).cs;
          let _759_v = Std_JSON_Grammar.Value.create_Number(_757_num);
          let _760_sp = Std_JSON_Utils_Cursors.Split.create_SP(_759_v, _758_cs_k);
          return Std_Wrappers.Result.create_Success(_760_sp);
        }
      }
    };
    static ValueParser(cs) {
      let _761_pre = ((_762_cs) => function (_763_ps_k) {
        return ((_763_ps_k).Length()) < ((_762_cs).Length());
      })(cs);
      let _764_fn = ((_765_pre) => function (_766_ps_k) {
        return Std_JSON_ZeroCopy_Deserializer_Values.__default.Value(_766_ps_k);
      })(_761_pre);
      return _764_fn;
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_Values
let Std_JSON_ZeroCopy_Deserializer_API = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.Deserializer.API._default";
    }
    _parentTraits() {
      return [];
    }
    static LiftCursorError(err) {
      let _source24 = err;
      if (_source24.is_EOF) {
        return Std_JSON_Errors.DeserializationError.create_ReachedEOF();
      } else if (_source24.is_ExpectingByte) {
        let _767___mcc_h0 = (_source24).expected;
        let _768___mcc_h1 = (_source24).b;
        let _769_b = _768___mcc_h1;
        let _770_expected = _767___mcc_h0;
        return Std_JSON_Errors.DeserializationError.create_ExpectingByte(_770_expected, _769_b);
      } else if (_source24.is_ExpectingAnyByte) {
        let _771___mcc_h2 = (_source24).expected__sq;
        let _772___mcc_h3 = (_source24).b;
        let _773_b = _772___mcc_h3;
        let _774_expected__sq = _771___mcc_h2;
        return Std_JSON_Errors.DeserializationError.create_ExpectingAnyByte(_774_expected__sq, _773_b);
      } else {
        let _775___mcc_h4 = (_source24).err;
        let _776_err = _775___mcc_h4;
        return _776_err;
      }
    };
    static JSON(cs) {
      return (Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural(cs, Std_JSON_ZeroCopy_Deserializer_Values.__default.Value)).MapFailure(Std_JSON_ZeroCopy_Deserializer_API.__default.LiftCursorError);
    };
    static Text(v) {
      let _777_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_API.__default.JSON(Std_JSON_Utils_Cursors.Cursor__.OfView(v));
      if ((_777_valueOrError0).IsFailure()) {
        return (_777_valueOrError0).PropagateFailure();
      } else {
        let _let_tmp_rhs39 = (_777_valueOrError0).Extract();
        let _778_text = (_let_tmp_rhs39).t;
        let _779_cs = (_let_tmp_rhs39).cs;
        let _780_valueOrError1 = Std_Wrappers.__default.Need((_779_cs).EOF_q, Std_JSON_Errors.DeserializationError.create_ExpectingEOF());
        if ((_780_valueOrError1).IsFailure()) {
          return (_780_valueOrError1).PropagateFailure();
        } else {
          return Std_Wrappers.Result.create_Success(_778_text);
        }
      }
    };
    static OfBytes(bs) {
      let _781_valueOrError0 = Std_Wrappers.__default.Need((new BigNumber((bs).length)).isLessThan(Std_BoundedInts.__default.TWO__TO__THE__32), Std_JSON_Errors.DeserializationError.create_IntOverflow());
      if ((_781_valueOrError0).IsFailure()) {
        return (_781_valueOrError0).PropagateFailure();
      } else {
        return Std_JSON_ZeroCopy_Deserializer_API.__default.Text(Std_JSON_Utils_Views_Core.View__.OfBytes(bs));
      }
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer_API
let Std_JSON_ZeroCopy_Deserializer = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON_ZeroCopy_Deserializer
let Std_JSON_ZeroCopy_API = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.ZeroCopy.API._default";
    }
    _parentTraits() {
      return [];
    }
    static Serialize(js) {
      return Std_Wrappers.Result.create_Success((Std_JSON_ZeroCopy_Serializer.__default.Text(js)).Bytes());
    };
    static SerializeAlloc(js) {
      let bs = Std_Wrappers.Result.Default([]);
      let _out9;
      _out9 = Std_JSON_ZeroCopy_Serializer.__default.Serialize(js);
      bs = _out9;
      return bs;
    }
    static SerializeInto(js, bs) {
      let len = Std_Wrappers.Result.Default(0);
      let _out10;
      _out10 = Std_JSON_ZeroCopy_Serializer.__default.SerializeTo(js, bs);
      len = _out10;
      return len;
    }
    static Deserialize(bs) {
      return Std_JSON_ZeroCopy_Deserializer_API.__default.OfBytes(bs);
    };
  };
  return $module;
})(); // end of module Std_JSON_ZeroCopy_API
let Std_JSON_ZeroCopy = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON_ZeroCopy
let Std_JSON_API = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Std.JSON.API._default";
    }
    _parentTraits() {
      return [];
    }
    static Serialize(js) {
      let _782_valueOrError0 = Std_JSON_Serializer.__default.JSON(js);
      if ((_782_valueOrError0).IsFailure()) {
        return (_782_valueOrError0).PropagateFailure();
      } else {
        let _783_js = (_782_valueOrError0).Extract();
        return Std_JSON_ZeroCopy_API.__default.Serialize(_783_js);
      }
    };
    static SerializeAlloc(js) {
      let bs = Std_Wrappers.Result.Default([]);
      let _784_js;
      let _785_valueOrError0 = Std_Wrappers.Result.Default(Std_JSON_Grammar.Structural.Default(Std_JSON_Grammar.Value.Default()));
      _785_valueOrError0 = Std_JSON_Serializer.__default.JSON(js);
      if ((_785_valueOrError0).IsFailure()) {
        bs = (_785_valueOrError0).PropagateFailure();
        return bs;
      }
      _784_js = (_785_valueOrError0).Extract();
      let _out11;
      _out11 = Std_JSON_ZeroCopy_API.__default.SerializeAlloc(_784_js);
      bs = _out11;
      return bs;
    }
    static SerializeInto(js, bs) {
      let len = Std_Wrappers.Result.Default(0);
      let _786_js;
      let _787_valueOrError0 = Std_Wrappers.Result.Default(Std_JSON_Grammar.Structural.Default(Std_JSON_Grammar.Value.Default()));
      _787_valueOrError0 = Std_JSON_Serializer.__default.JSON(js);
      if ((_787_valueOrError0).IsFailure()) {
        len = (_787_valueOrError0).PropagateFailure();
        return len;
      }
      _786_js = (_787_valueOrError0).Extract();
      let _out12;
      _out12 = Std_JSON_ZeroCopy_API.__default.SerializeInto(_786_js, bs);
      len = _out12;
      return len;
    }
    static Deserialize(bs) {
      let _788_valueOrError0 = Std_JSON_ZeroCopy_API.__default.Deserialize(bs);
      if ((_788_valueOrError0).IsFailure()) {
        return (_788_valueOrError0).PropagateFailure();
      } else {
        let _789_js = (_788_valueOrError0).Extract();
        return Std_JSON_Deserializer.__default.JSON(_789_js);
      }
    };
  };
  return $module;
})(); // end of module Std_JSON_API
let Std_JSON = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JSON
let Std = (function() {
  let $module = {};

  return $module;
})(); // end of module Std
