// Dafny program the_program compiled into JavaScript
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
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return Std_Wrappers.Option.create_None();
      } else if (_dafny.areEqual((xs)[_dafny.ZERO], v)) {
        return Std_Wrappers.Option.create_Some(_dafny.ZERO);
      } else {
        let _73_o_k = Std_Collections_Seq.__default.IndexOfOption((xs).slice(_dafny.ONE), v);
        if ((_73_o_k).is_Some) {
          return Std_Wrappers.Option.create_Some(((_73_o_k).dtor_value).plus(_dafny.ONE));
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
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return Std_Wrappers.Option.create_None();
        } else if (_dafny.areEqual((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)], v)) {
          return Std_Wrappers.Option.create_Some((new BigNumber((xs).length)).minus(_dafny.ONE));
        } else {
          let _in4 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in5 = v;
          xs = _in4;
          v = _in5;
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
        let _74_i = Std_Collections_Seq.__default.IndexOf(xs, v);
        return _dafny.Seq.Concat((xs).slice(0, _74_i), (xs).slice((_74_i).plus(_dafny.ONE)));
      }
    };
    static Insert(xs, a, pos) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat((xs).slice(0, pos), _dafny.Seq.of(a)), (xs).slice(pos));
    };
    static Reverse(xs) {
      let _75___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(xs, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_75___accumulator, _dafny.Seq.of());
        } else {
          _75___accumulator = _dafny.Seq.Concat(_75___accumulator, _dafny.Seq.of((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)]));
          let _in6 = (xs).slice(_dafny.ZERO, (new BigNumber((xs).length)).minus(_dafny.ONE));
          xs = _in6;
          continue TAIL_CALL_START;
        }
      }
    };
    static Repeat(v, length) {
      let _76___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((length).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_76___accumulator, _dafny.Seq.of());
        } else {
          _76___accumulator = _dafny.Seq.Concat(_76___accumulator, _dafny.Seq.of(v));
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
        let _77_a = (_let_tmp_rhs0)[0];
        let _78_b = (_let_tmp_rhs0)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_77_a, _dafny.Seq.of((Std_Collections_Seq.__default.Last(xs))[0])), _dafny.Seq.Concat(_78_b, _dafny.Seq.of((Std_Collections_Seq.__default.Last(xs))[1])));
      }
    };
    static Zip(xs, ys) {
      let _79___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _79___accumulator);
        } else {
          _79___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(_dafny.Tuple.of(Std_Collections_Seq.__default.Last(xs), Std_Collections_Seq.__default.Last(ys))), _79___accumulator);
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
      let _80___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_80___accumulator, _dafny.Seq.of());
        } else {
          _80___accumulator = _dafny.Seq.Concat(_80___accumulator, (xs)[_dafny.ZERO]);
          let _in11 = (xs).slice(_dafny.ONE);
          xs = _in11;
          continue TAIL_CALL_START;
        }
      }
    };
    static FlattenReverse(xs) {
      let _81___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _81___accumulator);
        } else {
          _81___accumulator = _dafny.Seq.Concat(Std_Collections_Seq.__default.Last(xs), _81___accumulator);
          let _in12 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in12;
          continue TAIL_CALL_START;
        }
      }
    };
    static Map(f, xs) {
      let _82___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_82___accumulator, _dafny.Seq.of());
        } else {
          _82___accumulator = _dafny.Seq.Concat(_82___accumulator, _dafny.Seq.of((f)((xs)[_dafny.ZERO])));
          let _in13 = f;
          let _in14 = (xs).slice(_dafny.ONE);
          f = _in13;
          xs = _in14;
          continue TAIL_CALL_START;
        }
      }
    };
    static MapWithResult(f, xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return Std_Wrappers.Result.create_Success(_dafny.Seq.of());
      } else {
        let _83_valueOrError0 = (f)((xs)[_dafny.ZERO]);
        if ((_83_valueOrError0).IsFailure()) {
          return (_83_valueOrError0).PropagateFailure();
        } else {
          let _84_head = (_83_valueOrError0).Extract();
          let _85_valueOrError1 = Std_Collections_Seq.__default.MapWithResult(f, (xs).slice(_dafny.ONE));
          if ((_85_valueOrError1).IsFailure()) {
            return (_85_valueOrError1).PropagateFailure();
          } else {
            let _86_tail = (_85_valueOrError1).Extract();
            return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.of(_84_head), _86_tail));
          }
        }
      }
    };
    static Filter(f, xs) {
      let _87___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_87___accumulator, _dafny.Seq.of());
        } else {
          _87___accumulator = _dafny.Seq.Concat(_87___accumulator, (((f)((xs)[_dafny.ZERO])) ? (_dafny.Seq.of((xs)[_dafny.ZERO])) : (_dafny.Seq.of())));
          let _in15 = f;
          let _in16 = (xs).slice(_dafny.ONE);
          f = _in15;
          xs = _in16;
          continue TAIL_CALL_START;
        }
      }
    };
    static FoldLeft(f, init, xs) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return init;
        } else {
          let _in17 = f;
          let _in18 = (f)(init, (xs)[_dafny.ZERO]);
          let _in19 = (xs).slice(_dafny.ONE);
          f = _in17;
          init = _in18;
          xs = _in19;
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
      let _88_left;
      _88_left = s;
      while (!(_88_left).equals(_dafny.Set.fromElements())) {
        let _89_x;
        L_ASSIGN_SUCH_THAT_0: {
          for (const _assign_such_that_0 of (_88_left).Elements) {
            _89_x = _assign_such_that_0;
            if ((_88_left).contains(_89_x)) {
              break L_ASSIGN_SUCH_THAT_0;
            }
          }
          throw new Error("assign-such-that search produced no value (line 7122)");
        }
        _88_left = (_88_left).Difference(_dafny.Set.fromElements(_89_x));
        xs = _dafny.Seq.Concat(xs, _dafny.Seq.of(_89_x));
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
        let _90_splitIndex = _dafny.EuclideanDivision(new BigNumber((a).length), new BigNumber(2));
        let _91_left = (a).slice(0, _90_splitIndex);
        let _92_right = (a).slice(_90_splitIndex);
        let _93_leftSorted = Std_Collections_Seq.__default.MergeSortBy(lessThanOrEq, _91_left);
        let _94_rightSorted = Std_Collections_Seq.__default.MergeSortBy(lessThanOrEq, _92_right);
        return Std_Collections_Seq.__default.MergeSortedWith(_93_leftSorted, _94_rightSorted, lessThanOrEq);
      }
    };
    static MergeSortedWith(left, right, lessThanOrEq) {
      let _95___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((left).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_95___accumulator, right);
        } else if ((new BigNumber((right).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_95___accumulator, left);
        } else if ((lessThanOrEq)((left)[_dafny.ZERO], (right)[_dafny.ZERO])) {
          _95___accumulator = _dafny.Seq.Concat(_95___accumulator, _dafny.Seq.of((left)[_dafny.ZERO]));
          let _in20 = (left).slice(_dafny.ONE);
          let _in21 = right;
          let _in22 = lessThanOrEq;
          left = _in20;
          right = _in21;
          lessThanOrEq = _in22;
          continue TAIL_CALL_START;
        } else {
          _95___accumulator = _dafny.Seq.Concat(_95___accumulator, _dafny.Seq.of((right)[_dafny.ZERO]));
          let _in23 = left;
          let _in24 = (right).slice(_dafny.ONE);
          let _in25 = lessThanOrEq;
          left = _in23;
          right = _in24;
          lessThanOrEq = _in25;
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
      let _96_lo;
      let _97_hi;
      let _rhs0 = _dafny.ZERO;
      let _rhs1 = new BigNumber((a).length);
      _96_lo = _rhs0;
      _97_hi = _rhs1;
      while ((_96_lo).isLessThan(_97_hi)) {
        let _98_mid;
        _98_mid = _dafny.EuclideanDivision((_96_lo).plus(_97_hi), new BigNumber(2));
        if ((less)(key, (a)[_98_mid])) {
          _97_hi = _98_mid;
        } else if ((less)((a)[_98_mid], key)) {
          _96_lo = (_98_mid).plus(_dafny.ONE);
        } else {
          r = Std_Wrappers.Option.create_Some(_98_mid);
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
          let _99_x = _compr_1;
          if ((m).contains(_99_x)) {
            _coll1.push([_99_x,(m).get(_99_x)]);
          }
        }
        return _coll1;
      }();
    };
    static RemoveKeys(m, xs) {
      return (m).Subtract(xs);
    };
    static Remove(m, x) {
      let _100_m_k = function () {
        let _coll2 = new _dafny.Map();
        for (const _compr_2 of (m).Keys.Elements) {
          let _101_x_k = _compr_2;
          if (((m).contains(_101_x_k)) && (!_dafny.areEqual(_101_x_k, x))) {
            _coll2.push([_101_x_k,(m).get(_101_x_k)]);
          }
        }
        return _coll2;
      }();
      return _100_m_k;
    };
    static Restrict(m, xs) {
      return function () {
        let _coll3 = new _dafny.Map();
        for (const _compr_3 of (xs).Elements) {
          let _102_x = _compr_3;
          if (((xs).contains(_102_x)) && ((m).contains(_102_x))) {
            _coll3.push([_102_x,(m).get(_102_x)]);
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
        let _103_x = undefined;
        L_ASSIGN_SUCH_THAT_1: {
          for (const _assign_such_that_1 of (s).Elements) {
            _103_x = _assign_such_that_1;
            if ((s).contains(_103_x)) {
              break L_ASSIGN_SUCH_THAT_1;
            }
          }
          throw new Error("assign-such-that search produced no value (line 7299)");
        }
        return _103_x;
      }(0);
    };
    static Map(f, xs) {
      let _104_ys = function () {
        let _coll4 = new _dafny.Set();
        for (const _compr_4 of (xs).Elements) {
          let _105_x = _compr_4;
          if ((xs).contains(_105_x)) {
            _coll4.add((f)(_105_x));
          }
        }
        return _coll4;
      }();
      return _104_ys;
    };
    static Filter(f, xs) {
      let _106_ys = function () {
        let _coll5 = new _dafny.Set();
        for (const _compr_5 of (xs).Elements) {
          let _107_x = _compr_5;
          if (((xs).contains(_107_x)) && ((f)(_107_x))) {
            _coll5.add(_107_x);
          }
        }
        return _coll5;
      }();
      return _106_ys;
    };
    static SetRange(a, b) {
      let _108___accumulator = _dafny.Set.fromElements();
      TAIL_CALL_START: while (true) {
        if ((a).isEqualTo(b)) {
          return (_dafny.Set.fromElements()).Union(_108___accumulator);
        } else {
          _108___accumulator = (_108___accumulator).Union(_dafny.Set.fromElements(a));
          let _in26 = (a).plus(_dafny.ONE);
          let _in27 = b;
          a = _in26;
          b = _in27;
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
      let _109_newCapacity;
      _109_newCapacity = _this.capacity;
      while (((_109_newCapacity).minus(_this.size)).isLessThan(reserved)) {
        _109_newCapacity = (_this).DefaultNewCapacity(_109_newCapacity);
      }
      if ((_this.capacity).isLessThan(_109_newCapacity)) {
        (_this).Realloc(defaultValue, _109_newCapacity);
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
      let _110_oldData;
      let _111_oldCapacity;
      let _rhs2 = _this.data;
      let _rhs3 = _this.capacity;
      _110_oldData = _rhs2;
      _111_oldCapacity = _rhs3;
      let _init3 = ((_112_defaultValue) => function (_113___v0) {
        return _112_defaultValue;
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
      (_this).CopyFrom(_110_oldData, _111_oldCapacity);
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
        let _114_index = _guard_loop_0;
        if ((true) && (((_dafny.ZERO).isLessThanOrEqualTo(_114_index)) && ((_114_index).isLessThan(count)))) {
          let _arr2 = _this.data;
          _arr2[(_114_index)] = (newData)[_114_index];
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
      let _115_isError;
      let _116_bytesRead;
      let _117_errorMsg;
      let _out1;
      let _out2;
      let _out3;
      let _outcollector0 = Std_JavaScriptFileIOInternalExterns.__default.INTERNAL__ReadBytesFromFile(path);
      _out1 = _outcollector0[0];
      _out2 = _outcollector0[1];
      _out3 = _outcollector0[2];
      _115_isError = _out1;
      _116_bytesRead = _out2;
      _117_errorMsg = _out3;
      res = ((_115_isError) ? (Std_Wrappers.Result.create_Failure(_117_errorMsg)) : (Std_Wrappers.Result.create_Success(_116_bytesRead)));
      return res;
      return res;
    }
    static WriteBytesToFile(path, bytes) {
      let res = Std_Wrappers.Result.Default(_dafny.Tuple.Default());
      let _118_isError;
      let _119_errorMsg;
      let _out4;
      let _out5;
      let _outcollector1 = Std_JavaScriptFileIOInternalExterns.__default.INTERNAL__WriteBytesToFile(path, bytes);
      _out4 = _outcollector1[0];
      _out5 = _outcollector1[1];
      _118_isError = _out4;
      _119_errorMsg = _out5;
      res = ((_118_isError) ? (Std_Wrappers.Result.create_Failure(_119_errorMsg)) : (Std_Wrappers.Result.create_Success(_dafny.Tuple.of())));
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
      let _120___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((x).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_120___accumulator);
        } else {
          _120___accumulator = (_120___accumulator).plus(y);
          let _in28 = (x).minus(_dafny.ONE);
          let _in29 = y;
          x = _in28;
          y = _in29;
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
          let _in30 = (d).plus(x);
          let _in31 = d;
          x = _in30;
          d = _in31;
          continue TAIL_CALL_START;
        } else if ((x).isLessThan(d)) {
          return x;
        } else {
          let _in32 = (x).minus(d);
          let _in33 = d;
          x = _in32;
          d = _in33;
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
      let _121___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((x).isLessThan(_dafny.ZERO)) {
          _121___accumulator = (_121___accumulator).plus(new BigNumber(-1));
          let _in34 = (x).plus(d);
          let _in35 = d;
          x = _in34;
          d = _in35;
          continue TAIL_CALL_START;
        } else if ((x).isLessThan(d)) {
          return (_dafny.ZERO).plus(_121___accumulator);
        } else {
          _121___accumulator = (_121___accumulator).plus(_dafny.ONE);
          let _in36 = (x).minus(d);
          let _in37 = d;
          x = _in36;
          d = _in37;
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
      let _122___accumulator = _dafny.ONE;
      TAIL_CALL_START: while (true) {
        if ((e).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ONE).multipliedBy(_122___accumulator);
        } else {
          _122___accumulator = (_122___accumulator).multipliedBy(b);
          let _in38 = b;
          let _in39 = (e).minus(_dafny.ONE);
          b = _in38;
          e = _in39;
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
      let _123___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((pow).isLessThan(base)) {
          return (_dafny.ZERO).plus(_123___accumulator);
        } else {
          _123___accumulator = (_123___accumulator).plus(_dafny.ONE);
          let _in40 = base;
          let _in41 = _dafny.EuclideanDivision(pow, base);
          base = _in40;
          pow = _in41;
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
    static OfDigits(digits) {
      let _124___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _124___accumulator);
        } else {
          _124___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_Strings_HexConversion.__default.chars)[(digits)[_dafny.ZERO]]), _124___accumulator);
          let _in42 = (digits).slice(_dafny.ONE);
          digits = _in42;
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
    static OfNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((_dafny.areEqual((str)[_dafny.ZERO], minus)) || (_dafny.Seq.contains(Std_Strings_HexConversion.__default.chars, (str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_1) {
        let _125_c = _forall_var_1;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _125_c)) || (_dafny.Seq.contains(Std_Strings_HexConversion.__default.chars, _125_c));
      })));
    };
    static ToNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((_dafny.areEqual((str)[_dafny.ZERO], minus)) || ((Std_Strings_HexConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_2) {
        let _126_c = _forall_var_2;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _126_c)) || ((Std_Strings_HexConversion.__default.charToDigit).contains(_126_c));
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
        return ((Std_Strings_HexConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_Strings_HexConversion.__default.base)).plus((Std_Strings_HexConversion.__default.charToDigit).get((str)[(new BigNumber((str).length)).minus(_dafny.ONE)]));
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
      let _127___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_127___accumulator);
        } else {
          _127___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_Strings_HexConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_127___accumulator);
          let _in43 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in43;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _128___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_128___accumulator, _dafny.Seq.of());
        } else {
          _128___accumulator = _dafny.Seq.Concat(_128___accumulator, _dafny.Seq.of((n).mod(Std_Strings_HexConversion.__default.BASE())));
          let _in44 = _dafny.EuclideanDivision(n, Std_Strings_HexConversion.__default.BASE());
          n = _in44;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in45 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in46 = n;
          xs = _in45;
          n = _in46;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _129_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_Strings_HexConversion.__default.SeqExtend(xs, _129_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_Strings_HexConversion.__default.SeqExtend(Std_Strings_HexConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _130_xs = Std_Strings_HexConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _130_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs1 = Std_Strings_HexConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _131_zs_k = (_let_tmp_rhs1)[0];
        let _132_cin = (_let_tmp_rhs1)[1];
        let _133_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_132_cin);
        let _let_tmp_rhs2 = (((_133_sum).isLessThan(Std_Strings_HexConversion.__default.BASE())) ? (_dafny.Tuple.of(_133_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_133_sum).minus(Std_Strings_HexConversion.__default.BASE()), _dafny.ONE)));
        let _134_sum__out = (_let_tmp_rhs2)[0];
        let _135_cout = (_let_tmp_rhs2)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_131_zs_k, _dafny.Seq.of(_134_sum__out)), _135_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs3 = Std_Strings_HexConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _136_zs = (_let_tmp_rhs3)[0];
        let _137_cin = (_let_tmp_rhs3)[1];
        let _let_tmp_rhs4 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_137_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_137_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_Strings_HexConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_137_cin), _dafny.ONE)));
        let _138_diff__out = (_let_tmp_rhs4)[0];
        let _139_cout = (_let_tmp_rhs4)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_136_zs, _dafny.Seq.of(_138_diff__out)), _139_cout);
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
    static OfDigits(digits) {
      let _140___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _140___accumulator);
        } else {
          _140___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_Strings_DecimalConversion.__default.chars)[(digits)[_dafny.ZERO]]), _140___accumulator);
          let _in47 = (digits).slice(_dafny.ONE);
          digits = _in47;
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
    static OfNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((_dafny.areEqual((str)[_dafny.ZERO], minus)) || (_dafny.Seq.contains(Std_Strings_DecimalConversion.__default.chars, (str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_3) {
        let _141_c = _forall_var_3;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _141_c)) || (_dafny.Seq.contains(Std_Strings_DecimalConversion.__default.chars, _141_c));
      })));
    };
    static ToNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((_dafny.areEqual((str)[_dafny.ZERO], minus)) || ((Std_Strings_DecimalConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_4) {
        let _142_c = _forall_var_4;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _142_c)) || ((Std_Strings_DecimalConversion.__default.charToDigit).contains(_142_c));
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
        return ((Std_Strings_DecimalConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_Strings_DecimalConversion.__default.base)).plus((Std_Strings_DecimalConversion.__default.charToDigit).get((str)[(new BigNumber((str).length)).minus(_dafny.ONE)]));
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
      let _143___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_143___accumulator);
        } else {
          _143___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_Strings_DecimalConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_143___accumulator);
          let _in48 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in48;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _144___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_144___accumulator, _dafny.Seq.of());
        } else {
          _144___accumulator = _dafny.Seq.Concat(_144___accumulator, _dafny.Seq.of((n).mod(Std_Strings_DecimalConversion.__default.BASE())));
          let _in49 = _dafny.EuclideanDivision(n, Std_Strings_DecimalConversion.__default.BASE());
          n = _in49;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in50 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in51 = n;
          xs = _in50;
          n = _in51;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _145_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_Strings_DecimalConversion.__default.SeqExtend(xs, _145_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_Strings_DecimalConversion.__default.SeqExtend(Std_Strings_DecimalConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _146_xs = Std_Strings_DecimalConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _146_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs5 = Std_Strings_DecimalConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _147_zs_k = (_let_tmp_rhs5)[0];
        let _148_cin = (_let_tmp_rhs5)[1];
        let _149_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_148_cin);
        let _let_tmp_rhs6 = (((_149_sum).isLessThan(Std_Strings_DecimalConversion.__default.BASE())) ? (_dafny.Tuple.of(_149_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_149_sum).minus(Std_Strings_DecimalConversion.__default.BASE()), _dafny.ONE)));
        let _150_sum__out = (_let_tmp_rhs6)[0];
        let _151_cout = (_let_tmp_rhs6)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_147_zs_k, _dafny.Seq.of(_150_sum__out)), _151_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs7 = Std_Strings_DecimalConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _152_zs = (_let_tmp_rhs7)[0];
        let _153_cin = (_let_tmp_rhs7)[1];
        let _let_tmp_rhs8 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_153_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_153_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_Strings_DecimalConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_153_cin), _dafny.ONE)));
        let _154_diff__out = (_let_tmp_rhs8)[0];
        let _155_cout = (_let_tmp_rhs8)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_152_zs, _dafny.Seq.of(_154_diff__out)), _155_cout);
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
      let _156___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(str, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_156___accumulator, str);
        } else if ((mustEscape).contains((str)[_dafny.ZERO])) {
          _156___accumulator = _dafny.Seq.Concat(_156___accumulator, _dafny.Seq.of(escape, (str)[_dafny.ZERO]));
          let _in52 = (str).slice(_dafny.ONE);
          let _in53 = mustEscape;
          let _in54 = escape;
          str = _in52;
          mustEscape = _in53;
          escape = _in54;
          continue TAIL_CALL_START;
        } else {
          _156___accumulator = _dafny.Seq.Concat(_156___accumulator, _dafny.Seq.of((str)[_dafny.ZERO]));
          let _in55 = (str).slice(_dafny.ONE);
          let _in56 = mustEscape;
          let _in57 = escape;
          str = _in55;
          mustEscape = _in56;
          escape = _in57;
          continue TAIL_CALL_START;
        }
      }
    };
    static Unescape(str, escape) {
      if (_dafny.areEqual(str, _dafny.Seq.of())) {
        return Std_Wrappers.Option.create_Some(str);
      } else if (_dafny.areEqual((str)[_dafny.ZERO], escape)) {
        if ((_dafny.ONE).isLessThan(new BigNumber((str).length))) {
          let _157_valueOrError0 = Std_Strings_CharStrEscaping.__default.Unescape((str).slice(new BigNumber(2)), escape);
          if ((_157_valueOrError0).IsFailure()) {
            return (_157_valueOrError0).PropagateFailure();
          } else {
            let _158_tl = (_157_valueOrError0).Extract();
            return Std_Wrappers.Option.create_Some(_dafny.Seq.Concat(_dafny.Seq.of((str)[_dafny.ONE]), _158_tl));
          }
        } else {
          return Std_Wrappers.Option.create_None();
        }
      } else {
        let _159_valueOrError1 = Std_Strings_CharStrEscaping.__default.Unescape((str).slice(_dafny.ONE), escape);
        if ((_159_valueOrError1).IsFailure()) {
          return (_159_valueOrError1).PropagateFailure();
        } else {
          let _160_tl = (_159_valueOrError1).Extract();
          return Std_Wrappers.Option.create_Some(_dafny.Seq.Concat(_dafny.Seq.of((str)[_dafny.ZERO]), _160_tl));
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
    static Join(sep, strs) {
      let _161___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((strs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_161___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else if ((new BigNumber((strs).length)).isEqualTo(_dafny.ONE)) {
          return _dafny.Seq.Concat(_161___accumulator, (strs)[_dafny.ZERO]);
        } else {
          _161___accumulator = _dafny.Seq.Concat(_161___accumulator, _dafny.Seq.Concat((strs)[_dafny.ZERO], sep));
          let _in58 = sep;
          let _in59 = (strs).slice(_dafny.ONE);
          sep = _in58;
          strs = _in59;
          continue TAIL_CALL_START;
        }
      }
    };
    static Concat(strs) {
      let _162___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((strs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_162___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          _162___accumulator = _dafny.Seq.Concat(_162___accumulator, (strs)[_dafny.ZERO]);
          let _in60 = (strs).slice(_dafny.ONE);
          strs = _in60;
          continue TAIL_CALL_START;
        }
      }
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
      let _163_plane = (_dafny.ShiftRight(i, (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      return (Std_Unicode_Base.__default.ASSIGNED__PLANES).contains(_163_plane);
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
        let _164_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedSingleCodeUnitSequence(s);
        return _164_b;
      } else if ((new BigNumber((s).length)).isEqualTo(new BigNumber(2))) {
        let _165_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _165_b;
      } else if ((new BigNumber((s).length)).isEqualTo(new BigNumber(3))) {
        let _166_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedTripleCodeUnitSequence(s);
        return _166_b;
      } else if ((new BigNumber((s).length)).isEqualTo(new BigNumber(4))) {
        let _167_b = Std_Unicode_Utf8EncodingForm.__default.IsWellFormedQuadrupleCodeUnitSequence(s);
        return _167_b;
      } else {
        return false;
      }
    };
    static IsWellFormedSingleCodeUnitSequence(s) {
      let _168_firstByte = (s)[_dafny.ZERO];
      return (true) && (((_dafny.ZERO).isLessThanOrEqualTo(_168_firstByte)) && ((_168_firstByte).isLessThanOrEqualTo(new BigNumber(127))));
    };
    static IsWellFormedDoubleCodeUnitSequence(s) {
      let _169_firstByte = (s)[_dafny.ZERO];
      let _170_secondByte = (s)[_dafny.ONE];
      return (((new BigNumber(194)).isLessThanOrEqualTo(_169_firstByte)) && ((_169_firstByte).isLessThanOrEqualTo(new BigNumber(223)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_170_secondByte)) && ((_170_secondByte).isLessThanOrEqualTo(new BigNumber(191))));
    };
    static IsWellFormedTripleCodeUnitSequence(s) {
      let _171_firstByte = (s)[_dafny.ZERO];
      let _172_secondByte = (s)[_dafny.ONE];
      let _173_thirdByte = (s)[new BigNumber(2)];
      return ((((((_171_firstByte).isEqualTo(new BigNumber(224))) && (((new BigNumber(160)).isLessThanOrEqualTo(_172_secondByte)) && ((_172_secondByte).isLessThanOrEqualTo(new BigNumber(191))))) || ((((new BigNumber(225)).isLessThanOrEqualTo(_171_firstByte)) && ((_171_firstByte).isLessThanOrEqualTo(new BigNumber(236)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_172_secondByte)) && ((_172_secondByte).isLessThanOrEqualTo(new BigNumber(191)))))) || (((_171_firstByte).isEqualTo(new BigNumber(237))) && (((new BigNumber(128)).isLessThanOrEqualTo(_172_secondByte)) && ((_172_secondByte).isLessThanOrEqualTo(new BigNumber(159)))))) || ((((new BigNumber(238)).isLessThanOrEqualTo(_171_firstByte)) && ((_171_firstByte).isLessThanOrEqualTo(new BigNumber(239)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_172_secondByte)) && ((_172_secondByte).isLessThanOrEqualTo(new BigNumber(191)))))) && (((new BigNumber(128)).isLessThanOrEqualTo(_173_thirdByte)) && ((_173_thirdByte).isLessThanOrEqualTo(new BigNumber(191))));
    };
    static IsWellFormedQuadrupleCodeUnitSequence(s) {
      let _174_firstByte = (s)[_dafny.ZERO];
      let _175_secondByte = (s)[_dafny.ONE];
      let _176_thirdByte = (s)[new BigNumber(2)];
      let _177_fourthByte = (s)[new BigNumber(3)];
      return ((((((_174_firstByte).isEqualTo(new BigNumber(240))) && (((new BigNumber(144)).isLessThanOrEqualTo(_175_secondByte)) && ((_175_secondByte).isLessThanOrEqualTo(new BigNumber(191))))) || ((((new BigNumber(241)).isLessThanOrEqualTo(_174_firstByte)) && ((_174_firstByte).isLessThanOrEqualTo(new BigNumber(243)))) && (((new BigNumber(128)).isLessThanOrEqualTo(_175_secondByte)) && ((_175_secondByte).isLessThanOrEqualTo(new BigNumber(191)))))) || (((_174_firstByte).isEqualTo(new BigNumber(244))) && (((new BigNumber(128)).isLessThanOrEqualTo(_175_secondByte)) && ((_175_secondByte).isLessThanOrEqualTo(new BigNumber(143)))))) && (((new BigNumber(128)).isLessThanOrEqualTo(_176_thirdByte)) && ((_176_thirdByte).isLessThanOrEqualTo(new BigNumber(191))))) && (((new BigNumber(128)).isLessThanOrEqualTo(_177_fourthByte)) && ((_177_fourthByte).isLessThanOrEqualTo(new BigNumber(191))));
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
      let _178_x = _dafny.BitwiseAnd(v, new BigNumber(127));
      let _179_firstByte = _178_x;
      return _dafny.Seq.of(_179_firstByte);
    };
    static EncodeScalarValueDoubleByte(v) {
      let _180_x = _dafny.BitwiseAnd(v, new BigNumber(63));
      let _181_y = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(1984)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _182_firstByte = _dafny.BitwiseOr(new BigNumber(192), _181_y);
      let _183_secondByte = _dafny.BitwiseOr(new BigNumber(128), _180_x);
      return _dafny.Seq.of(_182_firstByte, _183_secondByte);
    };
    static EncodeScalarValueTripleByte(v) {
      let _184_x = _dafny.BitwiseAnd(v, new BigNumber(63));
      let _185_y = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(4032)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _186_z = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(61440)), (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _187_firstByte = _dafny.BitwiseOr(new BigNumber(224), _186_z);
      let _188_secondByte = _dafny.BitwiseOr(new BigNumber(128), _185_y);
      let _189_thirdByte = _dafny.BitwiseOr(new BigNumber(128), _184_x);
      return _dafny.Seq.of(_187_firstByte, _188_secondByte, _189_thirdByte);
    };
    static EncodeScalarValueQuadrupleByte(v) {
      let _190_x = _dafny.BitwiseAnd(v, new BigNumber(63));
      let _191_y = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(4032)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _192_z = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(61440)), (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _193_u2 = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(196608)), (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _194_u1 = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(1835008)), (new BigNumber(18)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _195_firstByte = _dafny.BitwiseOr(new BigNumber(240), _194_u1);
      let _196_secondByte = _dafny.BitwiseOr(_dafny.BitwiseOr(new BigNumber(128), (_dafny.ShiftLeft(_193_u2, (new BigNumber(4)).toNumber())).mod(new BigNumber(2).exponentiatedBy(8))), _192_z);
      let _197_thirdByte = _dafny.BitwiseOr(new BigNumber(128), _191_y);
      let _198_fourthByte = _dafny.BitwiseOr(new BigNumber(128), _190_x);
      return _dafny.Seq.of(_195_firstByte, _196_secondByte, _197_thirdByte, _198_fourthByte);
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
      let _199_firstByte = (m)[_dafny.ZERO];
      let _200_x = _199_firstByte;
      return _200_x;
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m) {
      let _201_firstByte = (m)[_dafny.ZERO];
      let _202_secondByte = (m)[_dafny.ONE];
      let _203_y = _dafny.BitwiseAnd(_201_firstByte, new BigNumber(31));
      let _204_x = _dafny.BitwiseAnd(_202_secondByte, new BigNumber(63));
      return _dafny.BitwiseOr((_dafny.ShiftLeft(_203_y, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_204_x));
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m) {
      let _205_firstByte = (m)[_dafny.ZERO];
      let _206_secondByte = (m)[_dafny.ONE];
      let _207_thirdByte = (m)[new BigNumber(2)];
      let _208_z = _dafny.BitwiseAnd(_205_firstByte, new BigNumber(15));
      let _209_y = _dafny.BitwiseAnd(_206_secondByte, new BigNumber(63));
      let _210_x = _dafny.BitwiseAnd(_207_thirdByte, new BigNumber(63));
      return _dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft(_208_z, (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft(_209_y, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_210_x));
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m) {
      let _211_firstByte = (m)[_dafny.ZERO];
      let _212_secondByte = (m)[_dafny.ONE];
      let _213_thirdByte = (m)[new BigNumber(2)];
      let _214_fourthByte = (m)[new BigNumber(3)];
      let _215_u1 = _dafny.BitwiseAnd(_211_firstByte, new BigNumber(7));
      let _216_u2 = (_dafny.ShiftRight(_dafny.BitwiseAnd(_212_secondByte, new BigNumber(48)), (new BigNumber(4)).toNumber())).mod(new BigNumber(2).exponentiatedBy(8));
      let _217_z = _dafny.BitwiseAnd(_212_secondByte, new BigNumber(15));
      let _218_y = _dafny.BitwiseAnd(_213_thirdByte, new BigNumber(63));
      let _219_x = _dafny.BitwiseAnd(_214_fourthByte, new BigNumber(63));
      return _dafny.BitwiseOr(_dafny.BitwiseOr(_dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft(_215_u1, (new BigNumber(18)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft(_216_u2, (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_dafny.ShiftLeft(_217_z, (new BigNumber(12)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_dafny.ShiftLeft(_218_y, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_219_x));
    };
    static PartitionCodeUnitSequenceChecked(s) {
      let maybeParts = Std_Wrappers.Option.Default();
      if (_dafny.areEqual(s, _dafny.Seq.of())) {
        maybeParts = Std_Wrappers.Option.create_Some(_dafny.Seq.of());
        return maybeParts;
      }
      let _220_result;
      _220_result = _dafny.Seq.of();
      let _221_rest;
      _221_rest = s;
      while ((_dafny.ZERO).isLessThan(new BigNumber((_221_rest).length))) {
        let _222_prefix;
        let _223_valueOrError0 = Std_Wrappers.Option.Default();
        _223_valueOrError0 = Std_Unicode_Utf8EncodingForm.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_221_rest);
        if ((_223_valueOrError0).IsFailure()) {
          maybeParts = (_223_valueOrError0).PropagateFailure();
          return maybeParts;
        }
        _222_prefix = (_223_valueOrError0).Extract();
        _220_result = _dafny.Seq.Concat(_220_result, _dafny.Seq.of(_222_prefix));
        _221_rest = (_221_rest).slice(new BigNumber((_222_prefix).length));
      }
      maybeParts = Std_Wrappers.Option.create_Some(_220_result);
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
      for (let _224_i = new BigNumber((vs).length); _lo0.isLessThan(_224_i); ) {
        _224_i = _224_i.minus(_dafny.ONE);
        let _225_next;
        _225_next = Std_Unicode_Utf8EncodingForm.__default.EncodeScalarValue((vs)[_224_i]);
        s = _dafny.Seq.Concat(_225_next, s);
      }
      return s;
    }
    static DecodeCodeUnitSequence(s) {
      let _226_parts = Std_Unicode_Utf8EncodingForm.__default.PartitionCodeUnitSequence(s);
      let _227_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _226_parts);
      return _227_vs;
    };
    static DecodeCodeUnitSequenceChecked(s) {
      let maybeVs = Std_Wrappers.Option.Default();
      let _228_maybeParts;
      _228_maybeParts = Std_Unicode_Utf8EncodingForm.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_228_maybeParts).is_None) {
        maybeVs = Std_Wrappers.Option.create_None();
        return maybeVs;
      }
      let _229_parts;
      _229_parts = (_228_maybeParts).dtor_value;
      let _230_vs;
      _230_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf8EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _229_parts);
      maybeVs = Std_Wrappers.Option.create_Some(_230_vs);
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
        let _231_b = Std_Unicode_Utf16EncodingForm.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _231_b;
      } else {
        return false;
      }
    };
    static IsWellFormedSingleCodeUnitSequence(s) {
      let _232_firstWord = (s)[_dafny.ZERO];
      return (((_dafny.ZERO).isLessThanOrEqualTo(_232_firstWord)) && ((_232_firstWord).isLessThanOrEqualTo(new BigNumber(55295)))) || (((new BigNumber(57344)).isLessThanOrEqualTo(_232_firstWord)) && ((_232_firstWord).isLessThanOrEqualTo(new BigNumber(65535))));
    };
    static IsWellFormedDoubleCodeUnitSequence(s) {
      let _233_firstWord = (s)[_dafny.ZERO];
      let _234_secondWord = (s)[_dafny.ONE];
      return (((new BigNumber(55296)).isLessThanOrEqualTo(_233_firstWord)) && ((_233_firstWord).isLessThanOrEqualTo(new BigNumber(56319)))) && (((new BigNumber(56320)).isLessThanOrEqualTo(_234_secondWord)) && ((_234_secondWord).isLessThanOrEqualTo(new BigNumber(57343))));
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
      let _235_firstWord = v;
      return _dafny.Seq.of(_235_firstWord);
    };
    static EncodeScalarValueDoubleWord(v) {
      let _236_x2 = _dafny.BitwiseAnd(v, new BigNumber(1023));
      let _237_x1 = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(64512)), (new BigNumber(10)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _238_u = (_dafny.ShiftRight(_dafny.BitwiseAnd(v, new BigNumber(2031616)), (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24));
      let _239_w = ((_238_u).minus(_dafny.ONE)).mod(new BigNumber(2).exponentiatedBy(5));
      let _240_firstWord = _dafny.BitwiseOr(_dafny.BitwiseOr(new BigNumber(55296), (_dafny.ShiftLeft(_239_w, (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(16))), _237_x1);
      let _241_secondWord = _dafny.BitwiseOr(new BigNumber(56320), _236_x2);
      return _dafny.Seq.of(_240_firstWord, _241_secondWord);
    };
    static DecodeMinimalWellFormedCodeUnitSubsequence(m) {
      if ((new BigNumber((m).length)).isEqualTo(_dafny.ONE)) {
        return Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m);
      } else {
        return Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m);
      }
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m) {
      let _242_firstWord = (m)[_dafny.ZERO];
      let _243_x = (_242_firstWord);
      return _243_x;
    };
    static DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m) {
      let _244_firstWord = (m)[_dafny.ZERO];
      let _245_secondWord = (m)[_dafny.ONE];
      let _246_x2 = _dafny.BitwiseAnd(_245_secondWord, new BigNumber(1023));
      let _247_x1 = _dafny.BitwiseAnd(_244_firstWord, new BigNumber(63));
      let _248_w = (_dafny.ShiftRight(_dafny.BitwiseAnd(_244_firstWord, new BigNumber(960)), (new BigNumber(6)).toNumber())).mod(new BigNumber(2).exponentiatedBy(16));
      let _249_u = (((_248_w).plus(_dafny.ONE)).mod(new BigNumber(2).exponentiatedBy(24)));
      let _250_v = _dafny.BitwiseOr(_dafny.BitwiseOr((_dafny.ShiftLeft(_249_u, (new BigNumber(16)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24)), (_dafny.ShiftLeft(_247_x1, (new BigNumber(10)).toNumber())).mod(new BigNumber(2).exponentiatedBy(24))), (_246_x2));
      return _250_v;
    };
    static PartitionCodeUnitSequenceChecked(s) {
      let maybeParts = Std_Wrappers.Option.Default();
      if (_dafny.areEqual(s, _dafny.Seq.of())) {
        maybeParts = Std_Wrappers.Option.create_Some(_dafny.Seq.of());
        return maybeParts;
      }
      let _251_result;
      _251_result = _dafny.Seq.of();
      let _252_rest;
      _252_rest = s;
      while ((_dafny.ZERO).isLessThan(new BigNumber((_252_rest).length))) {
        let _253_prefix;
        let _254_valueOrError0 = Std_Wrappers.Option.Default();
        _254_valueOrError0 = Std_Unicode_Utf16EncodingForm.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_252_rest);
        if ((_254_valueOrError0).IsFailure()) {
          maybeParts = (_254_valueOrError0).PropagateFailure();
          return maybeParts;
        }
        _253_prefix = (_254_valueOrError0).Extract();
        _251_result = _dafny.Seq.Concat(_251_result, _dafny.Seq.of(_253_prefix));
        _252_rest = (_252_rest).slice(new BigNumber((_253_prefix).length));
      }
      maybeParts = Std_Wrappers.Option.create_Some(_251_result);
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
      for (let _255_i = new BigNumber((vs).length); _lo1.isLessThan(_255_i); ) {
        _255_i = _255_i.minus(_dafny.ONE);
        let _256_next;
        _256_next = Std_Unicode_Utf16EncodingForm.__default.EncodeScalarValue((vs)[_255_i]);
        s = _dafny.Seq.Concat(_256_next, s);
      }
      return s;
    }
    static DecodeCodeUnitSequence(s) {
      let _257_parts = Std_Unicode_Utf16EncodingForm.__default.PartitionCodeUnitSequence(s);
      let _258_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _257_parts);
      return _258_vs;
    };
    static DecodeCodeUnitSequenceChecked(s) {
      let maybeVs = Std_Wrappers.Option.Default();
      let _259_maybeParts;
      _259_maybeParts = Std_Unicode_Utf16EncodingForm.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_259_maybeParts).is_None) {
        maybeVs = Std_Wrappers.Option.create_None();
        return maybeVs;
      }
      let _260_parts;
      _260_parts = (_259_maybeParts).dtor_value;
      let _261_vs;
      _261_vs = Std_Collections_Seq.__default.Map(Std_Unicode_Utf16EncodingForm.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _260_parts);
      maybeVs = Std_Wrappers.Option.create_Some(_261_vs);
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
      let _262_asCodeUnits = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharAsUnicodeScalarValue, s);
      let _263_asUtf8CodeUnits = Std_Unicode_Utf8EncodingForm.__default.EncodeScalarSequence(_262_asCodeUnits);
      let _264_asBytes = Std_Collections_Seq.__default.Map(function (_265_cu) {
        return (_265_cu).toNumber();
      }, _263_asUtf8CodeUnits);
      return Std_Wrappers.Option.create_Some(_264_asBytes);
    };
    static FromUTF8Checked(bs) {
      let _266_asCodeUnits = Std_Collections_Seq.__default.Map(function (_267_c) {
        return new BigNumber(_267_c);
      }, bs);
      let _268_valueOrError0 = Std_Unicode_Utf8EncodingForm.__default.DecodeCodeUnitSequenceChecked(_266_asCodeUnits);
      if ((_268_valueOrError0).IsFailure()) {
        return (_268_valueOrError0).PropagateFailure();
      } else {
        let _269_utf32 = (_268_valueOrError0).Extract();
        let _270_asChars = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharFromUnicodeScalarValue, _269_utf32);
        return Std_Wrappers.Option.create_Some(_270_asChars);
      }
    };
    static ToUTF16Checked(s) {
      let _271_asCodeUnits = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharAsUnicodeScalarValue, s);
      let _272_asUtf16CodeUnits = Std_Unicode_Utf16EncodingForm.__default.EncodeScalarSequence(_271_asCodeUnits);
      let _273_asBytes = Std_Collections_Seq.__default.Map(function (_274_cu) {
        return (_274_cu).toNumber();
      }, _272_asUtf16CodeUnits);
      return Std_Wrappers.Option.create_Some(_273_asBytes);
    };
    static FromUTF16Checked(bs) {
      let _275_asCodeUnits = Std_Collections_Seq.__default.Map(function (_276_c) {
        return new BigNumber(_276_c);
      }, bs);
      let _277_valueOrError0 = Std_Unicode_Utf16EncodingForm.__default.DecodeCodeUnitSequenceChecked(_275_asCodeUnits);
      if ((_277_valueOrError0).IsFailure()) {
        return (_277_valueOrError0).PropagateFailure();
      } else {
        let _278_utf32 = (_277_valueOrError0).Extract();
        let _279_asChars = Std_Collections_Seq.__default.Map(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.CharFromUnicodeScalarValue, _278_utf32);
        return Std_Wrappers.Option.create_Some(_279_asChars);
      }
    };
    static ASCIIToUTF8(s) {
      return Std_Collections_Seq.__default.Map(function (_280_c) {
        return (_280_c).value;
      }, s);
    };
    static ASCIIToUTF16(s) {
      return Std_Collections_Seq.__default.Map(function (_281_c) {
        return (_281_c).value;
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
      return Std_Collections_Seq.__default.Map(function (_282_c) {
        return (_282_c).toNumber();
      }, s);
    };
    static Deserialize(b) {
      return Std_Collections_Seq.__default.Map(function (_283_b) {
        return new BigNumber(_283_b);
      }, b);
    };
  };
  return $module;
})(); // end of module Std_Unicode_Utf8EncodingScheme
let Std_Unicode = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_Unicode
let Std_ConcurrentDafny = (function() {
  let $module = {};


  $module.MutableMap = class MutableMap {
    constructor () {
      this._tname = "Std.ConcurrentDafny.MutableMap";
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
      this._tname = "Std.ConcurrentDafny.AtomicBox";
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
      this._tname = "Std.ConcurrentDafny.Lock";
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
})(); // end of module Std_ConcurrentDafny
let Std_JavaScriptFileIOInternalExterns = (function() {
  let $module = {};

  return $module;
})(); // end of module Std_JavaScriptFileIOInternalExterns
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
        let _284___mcc_h0 = (_source10).str;
        let _285_str = _284___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Unsupported escape sequence: "), _285_str);
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
        let _286___mcc_h1 = (_source10).expected;
        let _287___mcc_h2 = (_source10).b;
        let _288_b = _287___mcc_h2;
        let _289_b0 = _286___mcc_h1;
        let _290_c = (((_288_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_288_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting '"), _dafny.Seq.of(new _dafny.CodePoint((_289_b0)))), _dafny.Seq.UnicodeFromString("', read ")), _290_c);
      } else if (_source10.is_ExpectingAnyByte) {
        let _291___mcc_h3 = (_source10).expected__sq;
        let _292___mcc_h4 = (_source10).b;
        let _293_b = _292___mcc_h4;
        let _294_bs0 = _291___mcc_h3;
        let _295_c = (((_293_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_293_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        let _296_c0s = _dafny.Seq.Create(new BigNumber((_294_bs0).length), ((_297_bs0) => function (_298_idx) {
          return new _dafny.CodePoint(((_297_bs0)[_298_idx]));
        })(_294_bs0));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting one of '"), _296_c0s), _dafny.Seq.UnicodeFromString("', read ")), _295_c);
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
        let _299___mcc_h0 = (_source11).i;
        let _300_i = _299___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Integer too large: "), Std_Strings.__default.OfInt(_300_i));
      } else if (_source11.is_StringTooLong) {
        let _301___mcc_h1 = (_source11).s;
        let _302_s = _301___mcc_h1;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("String too long: "), _302_s);
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
      let _303_sStr = Std_Strings_HexConversion.__default.OfNat(new BigNumber(c));
      let _304_s = Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_303_sStr);
      return _dafny.Seq.Concat(_304_s, _dafny.Seq.Create((new BigNumber(4)).minus(new BigNumber((_304_s).length)), function (_305___v8) {
        return (new _dafny.CodePoint(' '.codePointAt(0))).value;
      }));
    };
    static Escape(str, start) {
      let _306___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _pat_let_tv0 = str;
        let _pat_let_tv1 = start;
        if ((new BigNumber((str).length)).isLessThanOrEqualTo(start)) {
          return _dafny.Seq.Concat(_306___accumulator, _dafny.Seq.of());
        } else {
          _306___accumulator = _dafny.Seq.Concat(_306___accumulator, ((((str)[start]) === (34)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\\""))) : (((((str)[start]) === (92)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\\\"))) : (((((str)[start]) === (8)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\b"))) : (((((str)[start]) === (12)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\f"))) : (((((str)[start]) === (10)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\n"))) : (((((str)[start]) === (13)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\r"))) : (((((str)[start]) === (9)) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\t"))) : (function (_pat_let1_0) {
            return function (_307_c) {
              return (((_307_c) < (31)) ? (_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF16(_dafny.Seq.UnicodeFromString("\\u")), Std_JSON_Spec.__default.EscapeUnicode(_307_c))) : (_dafny.Seq.of((_pat_let_tv0)[_pat_let_tv1])));
            }(_pat_let1_0);
          }((str)[start]))))))))))))))));
          let _in61 = str;
          let _in62 = (start).plus(_dafny.ONE);
          str = _in61;
          start = _in62;
          continue TAIL_CALL_START;
        }
      }
    };
    static EscapeToUTF8(str, start) {
      let _308_valueOrError0 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(str)).ToResult(Std_JSON_Errors.SerializationError.create_InvalidUnicode());
      if ((_308_valueOrError0).IsFailure()) {
        return (_308_valueOrError0).PropagateFailure();
      } else {
        let _309_utf16 = (_308_valueOrError0).Extract();
        let _310_escaped = Std_JSON_Spec.__default.Escape(_309_utf16, _dafny.ZERO);
        let _311_valueOrError1 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_310_escaped)).ToResult(Std_JSON_Errors.SerializationError.create_InvalidUnicode());
        if ((_311_valueOrError1).IsFailure()) {
          return (_311_valueOrError1).PropagateFailure();
        } else {
          let _312_utf32 = (_311_valueOrError1).Extract();
          return (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ToUTF8Checked(_312_utf32)).ToResult(Std_JSON_Errors.SerializationError.create_InvalidUnicode());
        }
      }
    };
    static String(str) {
      let _313_valueOrError0 = Std_JSON_Spec.__default.EscapeToUTF8(str, _dafny.ZERO);
      if ((_313_valueOrError0).IsFailure()) {
        return (_313_valueOrError0).PropagateFailure();
      } else {
        let _314_inBytes = (_313_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("\"")), _314_inBytes), Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("\""))));
      }
    };
    static IntToBytes(n) {
      let _315_s = Std_Strings.__default.OfInt(n);
      return Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_315_s);
    };
    static Number(dec) {
      return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(Std_JSON_Spec.__default.IntToBytes((dec).dtor_n), ((((dec).dtor_e10).isEqualTo(_dafny.ZERO)) ? (_dafny.Seq.of()) : (_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("e")), Std_JSON_Spec.__default.IntToBytes((dec).dtor_e10))))));
    };
    static KeyValue(kv) {
      let _316_valueOrError0 = Std_JSON_Spec.__default.String((kv)[0]);
      if ((_316_valueOrError0).IsFailure()) {
        return (_316_valueOrError0).PropagateFailure();
      } else {
        let _317_key = (_316_valueOrError0).Extract();
        let _318_valueOrError1 = Std_JSON_Spec.__default.JSON((kv)[1]);
        if ((_318_valueOrError1).IsFailure()) {
          return (_318_valueOrError1).PropagateFailure();
        } else {
          let _319_value = (_318_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(_317_key, Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString(":"))), _319_value));
        }
      }
    };
    static Join(sep, items) {
      if ((new BigNumber((items).length)).isEqualTo(_dafny.ZERO)) {
        return Std_Wrappers.Result.create_Success(_dafny.Seq.of());
      } else {
        let _320_valueOrError0 = (items)[_dafny.ZERO];
        if ((_320_valueOrError0).IsFailure()) {
          return (_320_valueOrError0).PropagateFailure();
        } else {
          let _321_first = (_320_valueOrError0).Extract();
          if ((new BigNumber((items).length)).isEqualTo(_dafny.ONE)) {
            return Std_Wrappers.Result.create_Success(_321_first);
          } else {
            let _322_valueOrError1 = Std_JSON_Spec.__default.Join(sep, (items).slice(_dafny.ONE));
            if ((_322_valueOrError1).IsFailure()) {
              return (_322_valueOrError1).PropagateFailure();
            } else {
              let _323_rest = (_322_valueOrError1).Extract();
              return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(_321_first, sep), _323_rest));
            }
          }
        }
      }
    };
    static Object(obj) {
      let _324_valueOrError0 = Std_JSON_Spec.__default.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString(",")), _dafny.Seq.Create(new BigNumber((obj).length), ((_325_obj) => function (_326_i) {
        return Std_JSON_Spec.__default.KeyValue((_325_obj)[_326_i]);
      })(obj)));
      if ((_324_valueOrError0).IsFailure()) {
        return (_324_valueOrError0).PropagateFailure();
      } else {
        let _327_middle = (_324_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("{")), _327_middle), Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("}"))));
      }
    };
    static Array(arr) {
      let _328_valueOrError0 = Std_JSON_Spec.__default.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString(",")), _dafny.Seq.Create(new BigNumber((arr).length), ((_329_arr) => function (_330_i) {
        return Std_JSON_Spec.__default.JSON((_329_arr)[_330_i]);
      })(arr)));
      if ((_328_valueOrError0).IsFailure()) {
        return (_328_valueOrError0).PropagateFailure();
      } else {
        let _331_middle = (_328_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_dafny.Seq.Concat(_dafny.Seq.Concat(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("[")), _331_middle), Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("]"))));
      }
    };
    static JSON(js) {
      let _source12 = js;
      if (_source12.is_Null) {
        return Std_Wrappers.Result.create_Success(Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("null")));
      } else if (_source12.is_Bool) {
        let _332___mcc_h0 = (_source12).b;
        let _333_b = _332___mcc_h0;
        return Std_Wrappers.Result.create_Success(((_333_b) ? (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("true"))) : (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ASCIIToUTF8(_dafny.Seq.UnicodeFromString("false")))));
      } else if (_source12.is_String) {
        let _334___mcc_h1 = (_source12).str;
        let _335_str = _334___mcc_h1;
        return Std_JSON_Spec.__default.String(_335_str);
      } else if (_source12.is_Number) {
        let _336___mcc_h2 = (_source12).num;
        let _337_dec = _336___mcc_h2;
        return Std_JSON_Spec.__default.Number(_337_dec);
      } else if (_source12.is_Object) {
        let _338___mcc_h3 = (_source12).obj;
        let _339_obj = _338___mcc_h3;
        return Std_JSON_Spec.__default.Object(_339_obj);
      } else {
        let _340___mcc_h4 = (_source12).arr;
        let _341_arr = _340___mcc_h4;
        return Std_JSON_Spec.__default.Array(_341_arr);
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
      let _342_dt__update__tmp_h0 = lv;
      let _343_dt__update_hend_h0 = (rv).dtor_end;
      return Std_JSON_Utils_Views_Core.View__.create_View((_342_dt__update__tmp_h0).dtor_s, (_342_dt__update__tmp_h0).dtor_beg, _343_dt__update_hend_h0);
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
      return _dafny.Seq.Create(new BigNumber((s).length), ((_344_s) => function (_345_i) {
        return ((_344_s)[_345_i]).value;
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
      for (let _346_idx = 0; _346_idx < _hi0; _346_idx++) {
        let _index6 = (start) + (_346_idx);
        (dest)[_index6] = ((_this).dtor_s)[((_this).dtor_beg) + (_346_idx)];
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
      let _347___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((_this).is_Empty) {
          return (_dafny.ZERO).plus(_347___accumulator);
        } else {
          _347___accumulator = (new BigNumber(((_this).dtor_v).Length())).plus(_347___accumulator);
          let _in63 = (_this).dtor_previous;
          _this = _in63;
          ;
          continue TAIL_CALL_START;
        }
      }
    };
    Count() {
      let _this = this;
      let _348___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((_this).is_Empty) {
          return (_dafny.ZERO).plus(_348___accumulator);
        } else {
          _348___accumulator = (_dafny.ONE).plus(_348___accumulator);
          let _in64 = (_this).dtor_previous;
          _this = _in64;
          ;
          continue TAIL_CALL_START;
        }
      }
    };
    Bytes() {
      let _this = this;
      let _349___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((_this).is_Empty) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _349___accumulator);
        } else {
          _349___accumulator = _dafny.Seq.Concat(((_this).dtor_v).Bytes(), _349___accumulator);
          let _in65 = (_this).dtor_previous;
          _this = _in65;
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
          let _350_end;
          _350_end = (end) - (((_this).dtor_v).Length());
          ((_this).dtor_v).CopyTo(dest, _350_end);
          let _in66 = (_this).dtor_previous;
          let _in67 = dest;
          let _in68 = _350_end;
          _this = _in66;
          ;
          dest = _in67;
          end = _in68;
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
      let _init4 = function (_351_i) {
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
        let _352___mcc_h0 = (_source13).escaped;
        let _353_escaped = _352___mcc_h0;
        if ((_$$_byte) === ((new _dafny.CodePoint('\\'.codePointAt(0))).value)) {
          return Std_JSON_Utils_Lexers_Core.LexerResult.create_Partial(Std_JSON_Utils_Lexers_Strings.StringLexerState.create_Body(!(_353_escaped)));
        } else if (((_$$_byte) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) && (!(_353_escaped))) {
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
        let _354___mcc_h0 = (_source14).expected;
        let _355___mcc_h1 = (_source14).b;
        let _356_b = _355___mcc_h1;
        let _357_b0 = _354___mcc_h0;
        let _358_c = (((_356_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_356_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting '"), _dafny.Seq.of(new _dafny.CodePoint((_357_b0)))), _dafny.Seq.UnicodeFromString("', read ")), _358_c);
      } else if (_source14.is_ExpectingAnyByte) {
        let _359___mcc_h2 = (_source14).expected__sq;
        let _360___mcc_h3 = (_source14).b;
        let _361_b = _360___mcc_h3;
        let _362_bs0 = _359___mcc_h2;
        let _363_c = (((_361_b) > (0)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), _dafny.Seq.of(new _dafny.CodePoint((_361_b)))), _dafny.Seq.UnicodeFromString("'"))) : (_dafny.Seq.UnicodeFromString("EOF")));
        let _364_c0s = _dafny.Seq.Create(new BigNumber((_362_bs0).length), ((_365_bs0) => function (_366_idx) {
          return new _dafny.CodePoint(((_365_bs0)[_366_idx]));
        })(_362_bs0));
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Expecting one of '"), _364_c0s), _dafny.Seq.UnicodeFromString("', read ")), _363_c);
      } else {
        let _367___mcc_h4 = (_source14).err;
        let _368_err = _367___mcc_h4;
        return (pr)(_368_err);
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
      let _369_dt__update__tmp_h0 = _this;
      let _370_dt__update_hbeg_h0 = (_this).dtor_point;
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_369_dt__update__tmp_h0).dtor_s, _370_dt__update_hbeg_h0, (_369_dt__update__tmp_h0).dtor_point, (_369_dt__update__tmp_h0).dtor_end);
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
      let _371_dt__update__tmp_h0 = _this;
      let _372_dt__update_hpoint_h0 = ((_this).dtor_point) + (n);
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_371_dt__update__tmp_h0).dtor_s, (_371_dt__update__tmp_h0).dtor_beg, _372_dt__update_hpoint_h0, (_371_dt__update__tmp_h0).dtor_end);
    };
    Unskip(n) {
      let _this = this;
      let _373_dt__update__tmp_h0 = _this;
      let _374_dt__update_hpoint_h0 = ((_this).dtor_point) - (n);
      return Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_373_dt__update__tmp_h0).dtor_s, (_373_dt__update__tmp_h0).dtor_beg, _374_dt__update_hpoint_h0, (_373_dt__update__tmp_h0).dtor_end);
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
      let _375_nxt = (_this).Peek();
      if ((_375_nxt) === (b)) {
        return Std_Wrappers.Result.create_Success((_this).Skip(1));
      } else {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_ExpectingByte(b, _375_nxt));
      }
    };
    AssertBytes(bs, offset) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((offset) === ((bs).length)) {
          return Std_Wrappers.Result.create_Success(_this);
        } else {
          let _376_valueOrError0 = (_this).AssertByte(((bs)[offset]));
          if ((_376_valueOrError0).IsFailure()) {
            return (_376_valueOrError0).PropagateFailure();
          } else {
            let _377_ps = (_376_valueOrError0).Extract();
            let _in69 = _377_ps;
            let _in70 = bs;
            let _in71 = (offset) + (1);
            _this = _in69;
            ;
            bs = _in70;
            offset = _in71;
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
      let _378_point_k;
      _378_point_k = (_this).dtor_point;
      let _379_end;
      _379_end = (_this).dtor_end;
      while (((_378_point_k) < (_379_end)) && ((p)(((_this).dtor_s)[_378_point_k]))) {
        _378_point_k = (_378_point_k) + (1);
      }
      ps = Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_this).dtor_s, (_this).dtor_beg, _378_point_k, (_this).dtor_end);
      return ps;
      return ps;
    }
    SkipWhileLexer(step, st) {
      let _this = this;
      let pr = Std_Wrappers.Result.Default(Std_JSON_Utils_Cursors.Cursor.Default);
      let _380_point_k;
      _380_point_k = (_this).dtor_point;
      let _381_end;
      _381_end = (_this).dtor_end;
      let _382_st_k;
      _382_st_k = st;
      while (true) {
        let _383_eof;
        _383_eof = (_380_point_k) === (_381_end);
        let _384_minusone;
        _384_minusone = -1;
        let _385_c;
        _385_c = ((_383_eof) ? (_384_minusone) : (((_this).dtor_s)[_380_point_k]));
        let _source15 = (step)(_382_st_k, _385_c);
        if (_source15.is_Accept) {
          pr = Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Cursor__.create_Cursor((_this).dtor_s, (_this).dtor_beg, _380_point_k, (_this).dtor_end));
          return pr;
        } else if (_source15.is_Reject) {
          let _386___mcc_h0 = (_source15).err;
          let _387_err = _386___mcc_h0;
          pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_OtherError(_387_err));
          return pr;
        } else {
          let _388___mcc_h1 = (_source15).st;
          let _389_st_k_k = _388___mcc_h1;
          if (_383_eof) {
            pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
            return pr;
          } else {
            _382_st_k = _389_st_k_k;
            _380_point_k = (_380_point_k) + (1);
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
      return function (_390___v9) {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
      };
    };
    static SubParserWitness() {
      return function (_391_cs) {
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
    static OfDigits(digits) {
      let _392___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _392___accumulator);
        } else {
          _392___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_JSON_ByteStrConversion.__default.chars)[(digits)[_dafny.ZERO]]), _392___accumulator);
          let _in72 = (digits).slice(_dafny.ONE);
          digits = _in72;
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
    static OfNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((((str)[_dafny.ZERO]) === (minus)) || (_dafny.Seq.contains(Std_JSON_ByteStrConversion.__default.chars, (str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_5) {
        let _393_c = _forall_var_5;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _393_c)) || (_dafny.Seq.contains(Std_JSON_ByteStrConversion.__default.chars, _393_c));
      })));
    };
    static ToNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((((str)[_dafny.ZERO]) === (minus)) || ((Std_JSON_ByteStrConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_6) {
        let _394_c = _forall_var_6;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _394_c)) || ((Std_JSON_ByteStrConversion.__default.charToDigit).contains(_394_c));
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
        return ((Std_JSON_ByteStrConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_JSON_ByteStrConversion.__default.base)).plus((Std_JSON_ByteStrConversion.__default.charToDigit).get((str)[(new BigNumber((str).length)).minus(_dafny.ONE)]));
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
      let _395___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_395___accumulator);
        } else {
          _395___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_JSON_ByteStrConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_395___accumulator);
          let _in73 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in73;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _396___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_396___accumulator, _dafny.Seq.of());
        } else {
          _396___accumulator = _dafny.Seq.Concat(_396___accumulator, _dafny.Seq.of((n).mod(Std_JSON_ByteStrConversion.__default.BASE())));
          let _in74 = _dafny.EuclideanDivision(n, Std_JSON_ByteStrConversion.__default.BASE());
          n = _in74;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in75 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in76 = n;
          xs = _in75;
          n = _in76;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _397_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_JSON_ByteStrConversion.__default.SeqExtend(xs, _397_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_JSON_ByteStrConversion.__default.SeqExtend(Std_JSON_ByteStrConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _398_xs = Std_JSON_ByteStrConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _398_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs9 = Std_JSON_ByteStrConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _399_zs_k = (_let_tmp_rhs9)[0];
        let _400_cin = (_let_tmp_rhs9)[1];
        let _401_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_400_cin);
        let _let_tmp_rhs10 = (((_401_sum).isLessThan(Std_JSON_ByteStrConversion.__default.BASE())) ? (_dafny.Tuple.of(_401_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_401_sum).minus(Std_JSON_ByteStrConversion.__default.BASE()), _dafny.ONE)));
        let _402_sum__out = (_let_tmp_rhs10)[0];
        let _403_cout = (_let_tmp_rhs10)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_399_zs_k, _dafny.Seq.of(_402_sum__out)), _403_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs11 = Std_JSON_ByteStrConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _404_zs = (_let_tmp_rhs11)[0];
        let _405_cin = (_let_tmp_rhs11)[1];
        let _let_tmp_rhs12 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_405_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_405_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_JSON_ByteStrConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_405_cin), _dafny.ONE)));
        let _406_diff__out = (_let_tmp_rhs12)[0];
        let _407_cout = (_let_tmp_rhs12)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_404_zs, _dafny.Seq.of(_406_diff__out)), _407_cout);
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
      let _408_valueOrError0 = Std_JSON_Spec.__default.EscapeToUTF8(str, _dafny.ZERO);
      if ((_408_valueOrError0).IsFailure()) {
        return (_408_valueOrError0).PropagateFailure();
      } else {
        let _409_bs = (_408_valueOrError0).Extract();
        let _410_o = Std_JSON_Serializer.__default.CheckLength(_409_bs, Std_JSON_Errors.SerializationError.create_StringTooLong(str));
        if ((_410_o).is_Pass) {
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.jstring.create_JString(Std_JSON_Grammar.__default.DOUBLEQUOTE, Std_JSON_Utils_Views_Core.View__.OfBytes(_409_bs), Std_JSON_Grammar.__default.DOUBLEQUOTE));
        } else {
          return Std_Wrappers.Result.create_Failure((_410_o).dtor_error);
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
      let _411_bs = Std_JSON_Serializer.__default.Int_k(n);
      let _412_o = Std_JSON_Serializer.__default.CheckLength(_411_bs, Std_JSON_Errors.SerializationError.create_IntTooLarge(n));
      if ((_412_o).is_Pass) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Views_Core.View__.OfBytes(_411_bs));
      } else {
        return Std_Wrappers.Result.create_Failure((_412_o).dtor_error);
      }
    };
    static Number(dec) {
      let _pat_let_tv2 = dec;
      let _pat_let_tv3 = dec;
      let _413_minus = Std_JSON_Serializer.__default.Sign((dec).dtor_n);
      let _414_valueOrError0 = Std_JSON_Serializer.__default.Int(Std_Math.__default.Abs((dec).dtor_n));
      if ((_414_valueOrError0).IsFailure()) {
        return (_414_valueOrError0).PropagateFailure();
      } else {
        let _415_num = (_414_valueOrError0).Extract();
        let _416_frac = Std_JSON_Grammar.Maybe.create_Empty();
        let _417_valueOrError1 = ((((dec).dtor_e10).isEqualTo(_dafny.ZERO)) ? (Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Maybe.create_Empty())) : (function (_pat_let2_0) {
          return function (_418_e) {
            return function (_pat_let3_0) {
              return function (_419_sign) {
                return function (_pat_let4_0) {
                  return function (_420_valueOrError2) {
                    return (((_420_valueOrError2).IsFailure()) ? ((_420_valueOrError2).PropagateFailure()) : (function (_pat_let5_0) {
                      return function (_421_num) {
                        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Maybe.create_NonEmpty(Std_JSON_Grammar.jexp.create_JExp(_418_e, _419_sign, _421_num)));
                      }(_pat_let5_0);
                    }((_420_valueOrError2).Extract())));
                  }(_pat_let4_0);
                }(Std_JSON_Serializer.__default.Int(Std_Math.__default.Abs((_pat_let_tv3).dtor_e10)));
              }(_pat_let3_0);
            }(Std_JSON_Serializer.__default.Sign((_pat_let_tv2).dtor_e10));
          }(_pat_let2_0);
        }(Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.Seq.of((new _dafny.CodePoint('e'.codePointAt(0))).value)))));
        if ((_417_valueOrError1).IsFailure()) {
          return (_417_valueOrError1).PropagateFailure();
        } else {
          let _422_exp = (_417_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.jnumber.create_JNumber(_413_minus, _415_num, Std_JSON_Grammar.Maybe.create_Empty(), _422_exp));
        }
      }
    };
    static MkStructural(v) {
      return Std_JSON_Grammar.Structural.create_Structural(Std_JSON_Grammar.__default.EMPTY, v, Std_JSON_Grammar.__default.EMPTY);
    };
    static KeyValue(kv) {
      let _423_valueOrError0 = Std_JSON_Serializer.__default.String((kv)[0]);
      if ((_423_valueOrError0).IsFailure()) {
        return (_423_valueOrError0).PropagateFailure();
      } else {
        let _424_k = (_423_valueOrError0).Extract();
        let _425_valueOrError1 = Std_JSON_Serializer.__default.Value((kv)[1]);
        if ((_425_valueOrError1).IsFailure()) {
          return (_425_valueOrError1).PropagateFailure();
        } else {
          let _426_v = (_425_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.jKeyValue.create_KeyValue(_424_k, Std_JSON_Serializer.__default.COLON, _426_v));
        }
      }
    };
    static MkSuffixedSequence(ds, suffix, start) {
      let _427___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((ds).length)).isLessThanOrEqualTo(start)) {
          return _dafny.Seq.Concat(_427___accumulator, _dafny.Seq.of());
        } else if ((start).isEqualTo((new BigNumber((ds).length)).minus(_dafny.ONE))) {
          return _dafny.Seq.Concat(_427___accumulator, _dafny.Seq.of(Std_JSON_Grammar.Suffixed.create_Suffixed((ds)[start], Std_JSON_Grammar.Maybe.create_Empty())));
        } else {
          _427___accumulator = _dafny.Seq.Concat(_427___accumulator, _dafny.Seq.of(Std_JSON_Grammar.Suffixed.create_Suffixed((ds)[start], Std_JSON_Grammar.Maybe.create_NonEmpty(suffix))));
          let _in77 = ds;
          let _in78 = suffix;
          let _in79 = (start).plus(_dafny.ONE);
          ds = _in77;
          suffix = _in78;
          start = _in79;
          continue TAIL_CALL_START;
        }
      }
    };
    static Object(obj) {
      let _428_valueOrError0 = Std_Collections_Seq.__default.MapWithResult(((_429_obj) => function (_430_v) {
        return Std_JSON_Serializer.__default.KeyValue(_430_v);
      })(obj), obj);
      if ((_428_valueOrError0).IsFailure()) {
        return (_428_valueOrError0).PropagateFailure();
      } else {
        let _431_items = (_428_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Bracketed.create_Bracketed(Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.LBRACE), Std_JSON_Serializer.__default.MkSuffixedSequence(_431_items, Std_JSON_Serializer.__default.COMMA, _dafny.ZERO), Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.RBRACE)));
      }
    };
    static Array(arr) {
      let _432_valueOrError0 = Std_Collections_Seq.__default.MapWithResult(((_433_arr) => function (_434_v) {
        return Std_JSON_Serializer.__default.Value(_434_v);
      })(arr), arr);
      if ((_432_valueOrError0).IsFailure()) {
        return (_432_valueOrError0).PropagateFailure();
      } else {
        let _435_items = (_432_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Bracketed.create_Bracketed(Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.LBRACKET), Std_JSON_Serializer.__default.MkSuffixedSequence(_435_items, Std_JSON_Serializer.__default.COMMA, _dafny.ZERO), Std_JSON_Serializer.__default.MkStructural(Std_JSON_Grammar.__default.RBRACKET)));
      }
    };
    static Value(js) {
      let _source16 = js;
      if (_source16.is_Null) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Null(Std_JSON_Utils_Views_Core.View__.OfBytes(Std_JSON_Grammar.__default.NULL)));
      } else if (_source16.is_Bool) {
        let _436___mcc_h0 = (_source16).b;
        let _437_b = _436___mcc_h0;
        return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Bool(Std_JSON_Serializer.__default.Bool(_437_b)));
      } else if (_source16.is_String) {
        let _438___mcc_h1 = (_source16).str;
        let _439_str = _438___mcc_h1;
        let _440_valueOrError0 = Std_JSON_Serializer.__default.String(_439_str);
        if ((_440_valueOrError0).IsFailure()) {
          return (_440_valueOrError0).PropagateFailure();
        } else {
          let _441_s = (_440_valueOrError0).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_String(_441_s));
        }
      } else if (_source16.is_Number) {
        let _442___mcc_h2 = (_source16).num;
        let _443_dec = _442___mcc_h2;
        let _444_valueOrError1 = Std_JSON_Serializer.__default.Number(_443_dec);
        if ((_444_valueOrError1).IsFailure()) {
          return (_444_valueOrError1).PropagateFailure();
        } else {
          let _445_n = (_444_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Number(_445_n));
        }
      } else if (_source16.is_Object) {
        let _446___mcc_h3 = (_source16).obj;
        let _447_obj = _446___mcc_h3;
        let _448_valueOrError2 = Std_JSON_Serializer.__default.Object(_447_obj);
        if ((_448_valueOrError2).IsFailure()) {
          return (_448_valueOrError2).PropagateFailure();
        } else {
          let _449_o = (_448_valueOrError2).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Object(_449_o));
        }
      } else {
        let _450___mcc_h4 = (_source16).arr;
        let _451_arr = _450___mcc_h4;
        let _452_valueOrError3 = Std_JSON_Serializer.__default.Array(_451_arr);
        if ((_452_valueOrError3).IsFailure()) {
          return (_452_valueOrError3).PropagateFailure();
        } else {
          let _453_a = (_452_valueOrError3).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Grammar.Value.create_Array(_453_a));
        }
      }
    };
    static JSON(js) {
      let _454_valueOrError0 = Std_JSON_Serializer.__default.Value(js);
      if ((_454_valueOrError0).IsFailure()) {
        return (_454_valueOrError0).PropagateFailure();
      } else {
        let _455_val = (_454_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(Std_JSON_Serializer.__default.MkStructural(_455_val));
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
    static OfDigits(digits) {
      let _456___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual(digits, _dafny.Seq.of())) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _456___accumulator);
        } else {
          _456___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((Std_JSON_Deserializer_Uint16StrConversion.__default.chars)[(digits)[_dafny.ZERO]]), _456___accumulator);
          let _in80 = (digits).slice(_dafny.ONE);
          digits = _in80;
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
    static OfNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((((str)[_dafny.ZERO]) === (minus)) || (_dafny.Seq.contains(Std_JSON_Deserializer_Uint16StrConversion.__default.chars, (str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_7) {
        let _457_c = _forall_var_7;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _457_c)) || (_dafny.Seq.contains(Std_JSON_Deserializer_Uint16StrConversion.__default.chars, _457_c));
      })));
    };
    static ToNumberStr(str, minus) {
      return !(!_dafny.areEqual(str, _dafny.Seq.of())) || (((((str)[_dafny.ZERO]) === (minus)) || ((Std_JSON_Deserializer_Uint16StrConversion.__default.charToDigit).contains((str)[_dafny.ZERO]))) && (_dafny.Quantifier(((str).slice(_dafny.ONE)).UniqueElements, true, function (_forall_var_8) {
        let _458_c = _forall_var_8;
        return !(_dafny.Seq.contains((str).slice(_dafny.ONE), _458_c)) || ((Std_JSON_Deserializer_Uint16StrConversion.__default.charToDigit).contains(_458_c));
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
        return ((Std_JSON_Deserializer_Uint16StrConversion.__default.ToNat((str).slice(0, (new BigNumber((str).length)).minus(_dafny.ONE)))).multipliedBy(Std_JSON_Deserializer_Uint16StrConversion.__default.base)).plus((Std_JSON_Deserializer_Uint16StrConversion.__default.charToDigit).get((str)[(new BigNumber((str).length)).minus(_dafny.ONE)]));
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
      let _459___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_459___accumulator);
        } else {
          _459___accumulator = ((Std_Collections_Seq.__default.Last(xs)).multipliedBy(Std_Arithmetic_Power.__default.Pow(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE(), (new BigNumber((xs).length)).minus(_dafny.ONE)))).plus(_459___accumulator);
          let _in81 = Std_Collections_Seq.__default.DropLast(xs);
          xs = _in81;
          continue TAIL_CALL_START;
        }
      }
    };
    static FromNat(n) {
      let _460___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_460___accumulator, _dafny.Seq.of());
        } else {
          _460___accumulator = _dafny.Seq.Concat(_460___accumulator, _dafny.Seq.of((n).mod(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE())));
          let _in82 = _dafny.EuclideanDivision(n, Std_JSON_Deserializer_Uint16StrConversion.__default.BASE());
          n = _in82;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtend(xs, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(new BigNumber((xs).length))) {
          return xs;
        } else {
          let _in83 = _dafny.Seq.Concat(xs, _dafny.Seq.of(_dafny.ZERO));
          let _in84 = n;
          xs = _in83;
          n = _in84;
          continue TAIL_CALL_START;
        }
      }
    };
    static SeqExtendMultiple(xs, n) {
      let _461_newLen = ((new BigNumber((xs).length)).plus(n)).minus((new BigNumber((xs).length)).mod(n));
      return Std_JSON_Deserializer_Uint16StrConversion.__default.SeqExtend(xs, _461_newLen);
    };
    static FromNatWithLen(n, len) {
      return Std_JSON_Deserializer_Uint16StrConversion.__default.SeqExtend(Std_JSON_Deserializer_Uint16StrConversion.__default.FromNat(n), len);
    };
    static SeqZero(len) {
      let _462_xs = Std_JSON_Deserializer_Uint16StrConversion.__default.FromNatWithLen(_dafny.ZERO, len);
      return _462_xs;
    };
    static SeqAdd(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs13 = Std_JSON_Deserializer_Uint16StrConversion.__default.SeqAdd(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _463_zs_k = (_let_tmp_rhs13)[0];
        let _464_cin = (_let_tmp_rhs13)[1];
        let _465_sum = ((Std_Collections_Seq.__default.Last(xs)).plus(Std_Collections_Seq.__default.Last(ys))).plus(_464_cin);
        let _let_tmp_rhs14 = (((_465_sum).isLessThan(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE())) ? (_dafny.Tuple.of(_465_sum, _dafny.ZERO)) : (_dafny.Tuple.of((_465_sum).minus(Std_JSON_Deserializer_Uint16StrConversion.__default.BASE()), _dafny.ONE)));
        let _466_sum__out = (_let_tmp_rhs14)[0];
        let _467_cout = (_let_tmp_rhs14)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_463_zs_k, _dafny.Seq.of(_466_sum__out)), _467_cout);
      }
    };
    static SeqSub(xs, ys) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(_dafny.Seq.of(), _dafny.ZERO);
      } else {
        let _let_tmp_rhs15 = Std_JSON_Deserializer_Uint16StrConversion.__default.SeqSub(Std_Collections_Seq.__default.DropLast(xs), Std_Collections_Seq.__default.DropLast(ys));
        let _468_zs = (_let_tmp_rhs15)[0];
        let _469_cin = (_let_tmp_rhs15)[1];
        let _let_tmp_rhs16 = ((((Std_Collections_Seq.__default.Last(ys)).plus(_469_cin)).isLessThanOrEqualTo(Std_Collections_Seq.__default.Last(xs))) ? (_dafny.Tuple.of(((Std_Collections_Seq.__default.Last(xs)).minus(Std_Collections_Seq.__default.Last(ys))).minus(_469_cin), _dafny.ZERO)) : (_dafny.Tuple.of((((Std_JSON_Deserializer_Uint16StrConversion.__default.BASE()).plus(Std_Collections_Seq.__default.Last(xs))).minus(Std_Collections_Seq.__default.Last(ys))).minus(_469_cin), _dafny.ONE)));
        let _470_diff__out = (_let_tmp_rhs16)[0];
        let _471_cout = (_let_tmp_rhs16)[1];
        return _dafny.Tuple.of(_dafny.Seq.Concat(_468_zs, _dafny.Seq.of(_470_diff__out)), _471_cout);
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
      let _472_hd = Std_JSON_Deserializer_Uint16StrConversion.__default.ToNat(str);
      return (_472_hd).toNumber();
    };
    static Unescape(str, start, prefix) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((str).length)).isLessThanOrEqualTo(start)) {
          return Std_Wrappers.Result.create_Success(prefix);
        } else if (((str)[start]) === ((new _dafny.CodePoint('\\'.codePointAt(0))).value)) {
          if ((new BigNumber((str).length)).isEqualTo((start).plus(_dafny.ONE))) {
            return Std_Wrappers.Result.create_Failure(Std_JSON_Errors.DeserializationError.create_EscapeAtEOS());
          } else {
            let _473_c = (str)[(start).plus(_dafny.ONE)];
            if ((_473_c) === ((new _dafny.CodePoint('u'.codePointAt(0))).value)) {
              if ((new BigNumber((str).length)).isLessThanOrEqualTo((start).plus(new BigNumber(6)))) {
                return Std_Wrappers.Result.create_Failure(Std_JSON_Errors.DeserializationError.create_EscapeAtEOS());
              } else {
                let _474_code = (str).slice((start).plus(new BigNumber(2)), (start).plus(new BigNumber(6)));
                if (_dafny.Quantifier((_474_code).UniqueElements, false, function (_exists_var_0) {
                  let _475_c = _exists_var_0;
                  return (_dafny.Seq.contains(_474_code, _475_c)) && (!(Std_JSON_Deserializer.__default.HEX__TABLE__16).contains(_475_c));
                })) {
                  return Std_Wrappers.Result.create_Failure(Std_JSON_Deserializer.__default.UnsupportedEscape16(_474_code));
                } else {
                  let _476_hd = Std_JSON_Deserializer.__default.ToNat16(_474_code);
                  let _in85 = str;
                  let _in86 = (start).plus(new BigNumber(6));
                  let _in87 = _dafny.Seq.Concat(prefix, _dafny.Seq.of(_476_hd));
                  str = _in85;
                  start = _in86;
                  prefix = _in87;
                  continue TAIL_CALL_START;
                }
              }
            } else {
              let _477_unescaped = (((_473_c) === (34)) ? ((34)) : ((((_473_c) === (92)) ? ((92)) : ((((_473_c) === (98)) ? ((8)) : ((((_473_c) === (102)) ? ((12)) : ((((_473_c) === (110)) ? ((10)) : ((((_473_c) === (114)) ? ((13)) : ((((_473_c) === (116)) ? ((9)) : ((0)))))))))))))));
              if ((new BigNumber(_477_unescaped)).isEqualTo(_dafny.ZERO)) {
                return Std_Wrappers.Result.create_Failure(Std_JSON_Deserializer.__default.UnsupportedEscape16((str).slice(start, (start).plus(new BigNumber(2)))));
              } else {
                let _in88 = str;
                let _in89 = (start).plus(new BigNumber(2));
                let _in90 = _dafny.Seq.Concat(prefix, _dafny.Seq.of(_477_unescaped));
                str = _in88;
                start = _in89;
                prefix = _in90;
                continue TAIL_CALL_START;
              }
            }
          }
        } else {
          let _in91 = str;
          let _in92 = (start).plus(_dafny.ONE);
          let _in93 = _dafny.Seq.Concat(prefix, _dafny.Seq.of((str)[start]));
          str = _in91;
          start = _in92;
          prefix = _in93;
          continue TAIL_CALL_START;
        }
      }
    };
    static String(js) {
      let _478_valueOrError0 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.FromUTF8Checked(((js).dtor_contents).Bytes())).ToResult(Std_JSON_Errors.DeserializationError.create_InvalidUnicode());
      if ((_478_valueOrError0).IsFailure()) {
        return (_478_valueOrError0).PropagateFailure();
      } else {
        let _479_asUtf32 = (_478_valueOrError0).Extract();
        let _480_valueOrError1 = (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.ToUTF16Checked(_479_asUtf32)).ToResult(Std_JSON_Errors.DeserializationError.create_InvalidUnicode());
        if ((_480_valueOrError1).IsFailure()) {
          return (_480_valueOrError1).PropagateFailure();
        } else {
          let _481_asUint16 = (_480_valueOrError1).Extract();
          let _482_valueOrError2 = Std_JSON_Deserializer.__default.Unescape(_481_asUint16, _dafny.ZERO, _dafny.Seq.of());
          if ((_482_valueOrError2).IsFailure()) {
            return (_482_valueOrError2).PropagateFailure();
          } else {
            let _483_unescaped = (_482_valueOrError2).Extract();
            return (Std_Unicode_UnicodeStringsWithUnicodeChar.__default.FromUTF16Checked(_483_unescaped)).ToResult(Std_JSON_Errors.DeserializationError.create_InvalidUnicode());
          }
        }
      }
    };
    static ToInt(sign, n) {
      let _484_n = Std_JSON_ByteStrConversion.__default.ToNat((n).Bytes());
      return Std_Wrappers.Result.create_Success((((sign).Char_q(new _dafny.CodePoint('-'.codePointAt(0)))) ? ((_dafny.ZERO).minus(_484_n)) : (_484_n)));
    };
    static Number(js) {
      let _let_tmp_rhs17 = js;
      let _485_minus = (_let_tmp_rhs17).minus;
      let _486_num = (_let_tmp_rhs17).num;
      let _487_frac = (_let_tmp_rhs17).frac;
      let _488_exp = (_let_tmp_rhs17).exp;
      let _489_valueOrError0 = Std_JSON_Deserializer.__default.ToInt(_485_minus, _486_num);
      if ((_489_valueOrError0).IsFailure()) {
        return (_489_valueOrError0).PropagateFailure();
      } else {
        let _490_n = (_489_valueOrError0).Extract();
        let _491_valueOrError1 = function (_source17) {
          if (_source17.is_Empty) {
            return Std_Wrappers.Result.create_Success(_dafny.ZERO);
          } else {
            let _492___mcc_h0 = (_source17).t;
            let _source18 = _492___mcc_h0;
            let _493___mcc_h1 = (_source18).e;
            let _494___mcc_h2 = (_source18).sign;
            let _495___mcc_h3 = (_source18).num;
            let _496_num = _495___mcc_h3;
            let _497_sign = _494___mcc_h2;
            return Std_JSON_Deserializer.__default.ToInt(_497_sign, _496_num);
          }
        }(_488_exp);
        if ((_491_valueOrError1).IsFailure()) {
          return (_491_valueOrError1).PropagateFailure();
        } else {
          let _498_e10 = (_491_valueOrError1).Extract();
          let _source19 = _487_frac;
          if (_source19.is_Empty) {
            return Std_Wrappers.Result.create_Success(Std_JSON_Values.Decimal.create_Decimal(_490_n, _498_e10));
          } else {
            let _499___mcc_h4 = (_source19).t;
            let _source20 = _499___mcc_h4;
            let _500___mcc_h5 = (_source20).period;
            let _501___mcc_h6 = (_source20).num;
            let _502_num = _501___mcc_h6;
            let _503_pow10 = new BigNumber((_502_num).Length());
            let _504_valueOrError2 = Std_JSON_Deserializer.__default.ToInt(_485_minus, _502_num);
            if ((_504_valueOrError2).IsFailure()) {
              return (_504_valueOrError2).PropagateFailure();
            } else {
              let _505_frac = (_504_valueOrError2).Extract();
              return Std_Wrappers.Result.create_Success(Std_JSON_Values.Decimal.create_Decimal(((_490_n).multipliedBy(Std_Arithmetic_Power.__default.Pow(new BigNumber(10), _503_pow10))).plus(_505_frac), (_498_e10).minus(_503_pow10)));
            }
          }
        }
      }
    };
    static KeyValue(js) {
      let _506_valueOrError0 = Std_JSON_Deserializer.__default.String((js).dtor_k);
      if ((_506_valueOrError0).IsFailure()) {
        return (_506_valueOrError0).PropagateFailure();
      } else {
        let _507_k = (_506_valueOrError0).Extract();
        let _508_valueOrError1 = Std_JSON_Deserializer.__default.Value((js).dtor_v);
        if ((_508_valueOrError1).IsFailure()) {
          return (_508_valueOrError1).PropagateFailure();
        } else {
          let _509_v = (_508_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(_dafny.Tuple.of(_507_k, _509_v));
        }
      }
    };
    static Object(js) {
      return Std_Collections_Seq.__default.MapWithResult(((_510_js) => function (_511_d) {
        return Std_JSON_Deserializer.__default.KeyValue((_511_d).dtor_t);
      })(js), (js).dtor_data);
    };
    static Array(js) {
      return Std_Collections_Seq.__default.MapWithResult(((_512_js) => function (_513_d) {
        return Std_JSON_Deserializer.__default.Value((_513_d).dtor_t);
      })(js), (js).dtor_data);
    };
    static Value(js) {
      let _source21 = js;
      if (_source21.is_Null) {
        let _514___mcc_h0 = (_source21).n;
        return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Null());
      } else if (_source21.is_Bool) {
        let _515___mcc_h1 = (_source21).b;
        let _516_b = _515___mcc_h1;
        return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Bool(Std_JSON_Deserializer.__default.Bool(_516_b)));
      } else if (_source21.is_String) {
        let _517___mcc_h2 = (_source21).str;
        let _518_str = _517___mcc_h2;
        let _519_valueOrError0 = Std_JSON_Deserializer.__default.String(_518_str);
        if ((_519_valueOrError0).IsFailure()) {
          return (_519_valueOrError0).PropagateFailure();
        } else {
          let _520_s = (_519_valueOrError0).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_String(_520_s));
        }
      } else if (_source21.is_Number) {
        let _521___mcc_h3 = (_source21).num;
        let _522_dec = _521___mcc_h3;
        let _523_valueOrError1 = Std_JSON_Deserializer.__default.Number(_522_dec);
        if ((_523_valueOrError1).IsFailure()) {
          return (_523_valueOrError1).PropagateFailure();
        } else {
          let _524_n = (_523_valueOrError1).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Number(_524_n));
        }
      } else if (_source21.is_Object) {
        let _525___mcc_h4 = (_source21).obj;
        let _526_obj = _525___mcc_h4;
        let _527_valueOrError2 = Std_JSON_Deserializer.__default.Object(_526_obj);
        if ((_527_valueOrError2).IsFailure()) {
          return (_527_valueOrError2).PropagateFailure();
        } else {
          let _528_o = (_527_valueOrError2).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Object(_528_o));
        }
      } else {
        let _529___mcc_h5 = (_source21).arr;
        let _530_arr = _529___mcc_h5;
        let _531_valueOrError3 = Std_JSON_Deserializer.__default.Array(_530_arr);
        if ((_531_valueOrError3).IsFailure()) {
          return (_531_valueOrError3).PropagateFailure();
        } else {
          let _532_a = (_531_valueOrError3).Extract();
          return Std_Wrappers.Result.create_Success(Std_JSON_Values.JSON.create_Array(_532_a));
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
      let _533___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((ts).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_533___accumulator, _dafny.Seq.of());
        } else {
          _533___accumulator = _dafny.Seq.Concat(_533___accumulator, (fT)((ts)[_dafny.ZERO]));
          let _in94 = (ts).slice(_dafny.ONE);
          let _in95 = fT;
          ts = _in94;
          fT = _in95;
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
      return Std_JSON_ConcreteSyntax_Spec.__default.Bracketed(obj, ((_534_obj) => function (_535_d) {
        return Std_JSON_ConcreteSyntax_Spec.__default.Member(_535_d);
      })(obj));
    };
    static Array(arr) {
      return Std_JSON_ConcreteSyntax_Spec.__default.Bracketed(arr, ((_536_arr) => function (_537_d) {
        return Std_JSON_ConcreteSyntax_Spec.__default.Item(_537_d);
      })(arr));
    };
    static Value(self) {
      let _source22 = self;
      if (_source22.is_Null) {
        let _538___mcc_h0 = (_source22).n;
        let _539_n = _538___mcc_h0;
        return Std_JSON_ConcreteSyntax_Spec.__default.View(_539_n);
      } else if (_source22.is_Bool) {
        let _540___mcc_h1 = (_source22).b;
        let _541_b = _540___mcc_h1;
        return Std_JSON_ConcreteSyntax_Spec.__default.View(_541_b);
      } else if (_source22.is_String) {
        let _542___mcc_h2 = (_source22).str;
        let _543_str = _542___mcc_h2;
        return Std_JSON_ConcreteSyntax_Spec.__default.String(_543_str);
      } else if (_source22.is_Number) {
        let _544___mcc_h3 = (_source22).num;
        let _545_num = _544___mcc_h3;
        return Std_JSON_ConcreteSyntax_Spec.__default.Number(_545_num);
      } else if (_source22.is_Object) {
        let _546___mcc_h4 = (_source22).obj;
        let _547_obj = _546___mcc_h4;
        return Std_JSON_ConcreteSyntax_Spec.__default.Object(_547_obj);
      } else {
        let _548___mcc_h5 = (_source22).arr;
        let _549_arr = _548___mcc_h5;
        return Std_JSON_ConcreteSyntax_Spec.__default.Array(_549_arr);
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
      let _550_writer;
      _550_writer = Std_JSON_ZeroCopy_Serializer.__default.Text(js);
      let _551_valueOrError0 = Std_Wrappers.OutcomeResult.Default();
      _551_valueOrError0 = Std_Wrappers.__default.Need((_550_writer).Unsaturated_q, Std_JSON_Errors.SerializationError.create_OutOfMemory());
      if ((_551_valueOrError0).IsFailure()) {
        rbs = (_551_valueOrError0).PropagateFailure();
        return rbs;
      }
      let _552_bs;
      let _out6;
      _out6 = (_550_writer).ToArray();
      _552_bs = _out6;
      rbs = Std_Wrappers.Result.create_Success(_552_bs);
      return rbs;
      return rbs;
    }
    static SerializeTo(js, dest) {
      let len = Std_Wrappers.Result.Default(0);
      let _553_writer;
      _553_writer = Std_JSON_ZeroCopy_Serializer.__default.Text(js);
      let _554_valueOrError0 = Std_Wrappers.OutcomeResult.Default();
      _554_valueOrError0 = Std_Wrappers.__default.Need((_553_writer).Unsaturated_q, Std_JSON_Errors.SerializationError.create_OutOfMemory());
      if ((_554_valueOrError0).IsFailure()) {
        len = (_554_valueOrError0).PropagateFailure();
        return len;
      }
      let _555_valueOrError1 = Std_Wrappers.OutcomeResult.Default();
      _555_valueOrError1 = Std_Wrappers.__default.Need((new BigNumber((_553_writer).dtor_length)).isLessThanOrEqualTo(new BigNumber((dest).length)), Std_JSON_Errors.SerializationError.create_OutOfMemory());
      if ((_555_valueOrError1).IsFailure()) {
        len = (_555_valueOrError1).PropagateFailure();
        return len;
      }
      (_553_writer).CopyTo(dest);
      len = Std_Wrappers.Result.create_Success((_553_writer).dtor_length);
      return len;
      return len;
    }
    static Text(js) {
      return Std_JSON_ZeroCopy_Serializer.__default.JSON(js, Std_JSON_Utils_Views_Writers.Writer__.Empty);
    };
    static JSON(js, writer) {
      return (((writer).Append((js).dtor_before)).Then(((_556_js) => function (_557_wr) {
        return Std_JSON_ZeroCopy_Serializer.__default.Value((_556_js).dtor_t, _557_wr);
      })(js))).Append((js).dtor_after);
    };
    static Value(v, writer) {
      let _source23 = v;
      if (_source23.is_Null) {
        let _558___mcc_h0 = (_source23).n;
        let _559_n = _558___mcc_h0;
        let _560_wr = (writer).Append(_559_n);
        return _560_wr;
      } else if (_source23.is_Bool) {
        let _561___mcc_h1 = (_source23).b;
        let _562_b = _561___mcc_h1;
        let _563_wr = (writer).Append(_562_b);
        return _563_wr;
      } else if (_source23.is_String) {
        let _564___mcc_h2 = (_source23).str;
        let _565_str = _564___mcc_h2;
        let _566_wr = Std_JSON_ZeroCopy_Serializer.__default.String(_565_str, writer);
        return _566_wr;
      } else if (_source23.is_Number) {
        let _567___mcc_h3 = (_source23).num;
        let _568_num = _567___mcc_h3;
        let _569_wr = Std_JSON_ZeroCopy_Serializer.__default.Number(_568_num, writer);
        return _569_wr;
      } else if (_source23.is_Object) {
        let _570___mcc_h4 = (_source23).obj;
        let _571_obj = _570___mcc_h4;
        let _572_wr = Std_JSON_ZeroCopy_Serializer.__default.Object(_571_obj, writer);
        return _572_wr;
      } else {
        let _573___mcc_h5 = (_source23).arr;
        let _574_arr = _573___mcc_h5;
        let _575_wr = Std_JSON_ZeroCopy_Serializer.__default.Array(_574_arr, writer);
        return _575_wr;
      }
    };
    static String(str, writer) {
      return (((writer).Append((str).dtor_lq)).Append((str).dtor_contents)).Append((str).dtor_rq);
    };
    static Number(num, writer) {
      let _576_wr1 = ((writer).Append((num).dtor_minus)).Append((num).dtor_num);
      let _577_wr2 = ((((num).dtor_frac).is_NonEmpty) ? (((_576_wr1).Append((((num).dtor_frac).dtor_t).dtor_period)).Append((((num).dtor_frac).dtor_t).dtor_num)) : (_576_wr1));
      let _578_wr3 = ((((num).dtor_exp).is_NonEmpty) ? ((((_577_wr2).Append((((num).dtor_exp).dtor_t).dtor_e)).Append((((num).dtor_exp).dtor_t).dtor_sign)).Append((((num).dtor_exp).dtor_t).dtor_num)) : (_577_wr2));
      let _579_wr = _578_wr3;
      return _579_wr;
    };
    static StructuralView(st, writer) {
      return (((writer).Append((st).dtor_before)).Append((st).dtor_t)).Append((st).dtor_after);
    };
    static Object(obj, writer) {
      let _580_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((obj).dtor_l, writer);
      let _581_wr = Std_JSON_ZeroCopy_Serializer.__default.Members(obj, _580_wr);
      let _582_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((obj).dtor_r, _581_wr);
      return _582_wr;
    };
    static Array(arr, writer) {
      let _583_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((arr).dtor_l, writer);
      let _584_wr = Std_JSON_ZeroCopy_Serializer.__default.Items(arr, _583_wr);
      let _585_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView((arr).dtor_r, _584_wr);
      return _585_wr;
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
      let _586_members;
      _586_members = (obj).dtor_data;
      let _hi1 = new BigNumber((_586_members).length);
      for (let _587_i = _dafny.ZERO; _587_i.isLessThan(_hi1); _587_i = _587_i.plus(_dafny.ONE)) {
        wr = Std_JSON_ZeroCopy_Serializer.__default.Member((_586_members)[_587_i], wr);
      }
      return wr;
    }
    static ItemsImpl(arr, writer) {
      let wr = Std_JSON_Utils_Views_Writers.Writer.Default;
      wr = writer;
      let _588_items;
      _588_items = (arr).dtor_data;
      let _hi2 = new BigNumber((_588_items).length);
      for (let _589_i = _dafny.ZERO; _589_i.isLessThan(_hi2); _589_i = _589_i.plus(_dafny.ONE)) {
        wr = Std_JSON_ZeroCopy_Serializer.__default.Item((_588_items)[_589_i], wr);
      }
      return wr;
    }
    static Member(m, writer) {
      let _590_wr = Std_JSON_ZeroCopy_Serializer.__default.String(((m).dtor_t).dtor_k, writer);
      let _591_wr = Std_JSON_ZeroCopy_Serializer.__default.StructuralView(((m).dtor_t).dtor_colon, _590_wr);
      let _592_wr = Std_JSON_ZeroCopy_Serializer.__default.Value(((m).dtor_t).dtor_v, _591_wr);
      let _593_wr = ((((m).dtor_suffix).is_Empty) ? (_592_wr) : (Std_JSON_ZeroCopy_Serializer.__default.StructuralView(((m).dtor_suffix).dtor_t, _592_wr)));
      return _593_wr;
    };
    static Item(m, writer) {
      let _594_wr = Std_JSON_ZeroCopy_Serializer.__default.Value((m).dtor_t, writer);
      let _595_wr = ((((m).dtor_suffix).is_Empty) ? (_594_wr) : (Std_JSON_ZeroCopy_Serializer.__default.StructuralView(((m).dtor_suffix).dtor_t, _594_wr)));
      return _595_wr;
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
      let _596_valueOrError0 = (cs).Get(err);
      if ((_596_valueOrError0).IsFailure()) {
        return (_596_valueOrError0).PropagateFailure();
      } else {
        let _597_cs = (_596_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_597_cs).Split());
      }
    };
    static WS(cs) {
      let sp = Std_JSON_Utils_Cursors.Split.Default(Std_JSON_Grammar.jblanks.Default);
      let _598_point_k;
      _598_point_k = (cs).dtor_point;
      let _599_end;
      _599_end = (cs).dtor_end;
      while (((_598_point_k) < (_599_end)) && (Std_JSON_Grammar.__default.Blank_q(((cs).dtor_s)[_598_point_k]))) {
        _598_point_k = (_598_point_k) + (1);
      }
      sp = (Std_JSON_Utils_Cursors.Cursor__.create_Cursor((cs).dtor_s, (cs).dtor_beg, _598_point_k, (cs).dtor_end)).Split();
      return sp;
      return sp;
    }
    static Structural(cs, parser) {
      let _let_tmp_rhs18 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(cs);
      let _600_before = (_let_tmp_rhs18).t;
      let _601_cs = (_let_tmp_rhs18).cs;
      let _602_valueOrError0 = ((parser))(_601_cs);
      if ((_602_valueOrError0).IsFailure()) {
        return (_602_valueOrError0).PropagateFailure();
      } else {
        let _let_tmp_rhs19 = (_602_valueOrError0).Extract();
        let _603_val = (_let_tmp_rhs19).t;
        let _604_cs = (_let_tmp_rhs19).cs;
        let _let_tmp_rhs20 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(_604_cs);
        let _605_after = (_let_tmp_rhs20).t;
        let _606_cs = (_let_tmp_rhs20).cs;
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Structural.create_Structural(_600_before, _603_val, _605_after), _606_cs));
      }
    };
    static TryStructural(cs) {
      let _let_tmp_rhs21 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(cs);
      let _607_before = (_let_tmp_rhs21).t;
      let _608_cs = (_let_tmp_rhs21).cs;
      let _let_tmp_rhs22 = ((_608_cs).SkipByte()).Split();
      let _609_val = (_let_tmp_rhs22).t;
      let _610_cs = (_let_tmp_rhs22).cs;
      let _let_tmp_rhs23 = Std_JSON_ZeroCopy_Deserializer_Core.__default.WS(_610_cs);
      let _611_after = (_let_tmp_rhs23).t;
      let _612_cs = (_let_tmp_rhs23).cs;
      return Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Structural.create_Structural(_607_before, _609_val, _611_after), _612_cs);
    };
    static get SpecView() {
      return function (_613_v) {
        return Std_JSON_ConcreteSyntax_Spec.__default.View(_613_v);
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
      let _614_escaped;
      _614_escaped = false;
      let _hi3 = (cs).dtor_end;
      for (let _615_point_k = (cs).dtor_point; _615_point_k < _hi3; _615_point_k++) {
        let _616_byte;
        _616_byte = ((cs).dtor_s)[_615_point_k];
        if (((_616_byte) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) && (!(_614_escaped))) {
          pr = Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Cursor__.create_Cursor((cs).dtor_s, (cs).dtor_beg, _615_point_k, (cs).dtor_end));
          return pr;
        } else if ((_616_byte) === ((new _dafny.CodePoint('\\'.codePointAt(0))).value)) {
          _614_escaped = !(_614_escaped);
        } else {
          _614_escaped = false;
        }
      }
      pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
      return pr;
      return pr;
    }
    static Quote(cs) {
      let _617_valueOrError0 = (cs).AssertChar(new _dafny.CodePoint('\"'.codePointAt(0)));
      if ((_617_valueOrError0).IsFailure()) {
        return (_617_valueOrError0).PropagateFailure();
      } else {
        let _618_cs = (_617_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_618_cs).Split());
      }
    };
    static String(cs) {
      let _619_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.Quote(cs);
      if ((_619_valueOrError0).IsFailure()) {
        return (_619_valueOrError0).PropagateFailure();
      } else {
        let _let_tmp_rhs24 = (_619_valueOrError0).Extract();
        let _620_lq = (_let_tmp_rhs24).t;
        let _621_cs = (_let_tmp_rhs24).cs;
        let _622_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.StringBody(_621_cs);
        if ((_622_valueOrError1).IsFailure()) {
          return (_622_valueOrError1).PropagateFailure();
        } else {
          let _623_contents = (_622_valueOrError1).Extract();
          let _let_tmp_rhs25 = (_623_contents).Split();
          let _624_contents = (_let_tmp_rhs25).t;
          let _625_cs = (_let_tmp_rhs25).cs;
          let _626_valueOrError2 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.Quote(_625_cs);
          if ((_626_valueOrError2).IsFailure()) {
            return (_626_valueOrError2).PropagateFailure();
          } else {
            let _let_tmp_rhs26 = (_626_valueOrError2).Extract();
            let _627_rq = (_let_tmp_rhs26).t;
            let _628_cs = (_let_tmp_rhs26).cs;
            return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.jstring.create_JString(_620_lq, _624_contents, _627_rq), _628_cs));
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
      let _629_sp = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Digits(cs);
      if (((_629_sp).dtor_t).Empty_q) {
        return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_OtherError(Std_JSON_Errors.DeserializationError.create_EmptyNumber()));
      } else {
        return Std_Wrappers.Result.create_Success(_629_sp);
      }
    };
    static NonZeroInt(cs) {
      return Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonEmptyDigits(cs);
    };
    static OptionalMinus(cs) {
      return ((cs).SkipIf(function (_630_c) {
        return (_630_c) === ((new _dafny.CodePoint('-'.codePointAt(0))).value);
      })).Split();
    };
    static OptionalSign(cs) {
      return ((cs).SkipIf(function (_631_c) {
        return ((_631_c) === ((new _dafny.CodePoint('-'.codePointAt(0))).value)) || ((_631_c) === ((new _dafny.CodePoint('+'.codePointAt(0))).value));
      })).Split();
    };
    static TrimmedInt(cs) {
      let _632_sp = ((cs).SkipIf(function (_633_c) {
        return (_633_c) === ((new _dafny.CodePoint('0'.codePointAt(0))).value);
      })).Split();
      if (((_632_sp).dtor_t).Empty_q) {
        return Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonZeroInt((_632_sp).dtor_cs);
      } else {
        return Std_Wrappers.Result.create_Success(_632_sp);
      }
    };
    static Exp(cs) {
      let _let_tmp_rhs27 = ((cs).SkipIf(function (_634_c) {
        return ((_634_c) === ((new _dafny.CodePoint('e'.codePointAt(0))).value)) || ((_634_c) === ((new _dafny.CodePoint('E'.codePointAt(0))).value));
      })).Split();
      let _635_e = (_let_tmp_rhs27).t;
      let _636_cs = (_let_tmp_rhs27).cs;
      if ((_635_e).Empty_q) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_Empty(), _636_cs));
      } else {
        let _let_tmp_rhs28 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.OptionalSign(_636_cs);
        let _637_sign = (_let_tmp_rhs28).t;
        let _638_cs = (_let_tmp_rhs28).cs;
        let _639_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonEmptyDigits(_638_cs);
        if ((_639_valueOrError0).IsFailure()) {
          return (_639_valueOrError0).PropagateFailure();
        } else {
          let _let_tmp_rhs29 = (_639_valueOrError0).Extract();
          let _640_num = (_let_tmp_rhs29).t;
          let _641_cs = (_let_tmp_rhs29).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_NonEmpty(Std_JSON_Grammar.jexp.create_JExp(_635_e, _637_sign, _640_num)), _641_cs));
        }
      }
    };
    static Frac(cs) {
      let _let_tmp_rhs30 = ((cs).SkipIf(function (_642_c) {
        return (_642_c) === ((new _dafny.CodePoint('.'.codePointAt(0))).value);
      })).Split();
      let _643_period = (_let_tmp_rhs30).t;
      let _644_cs = (_let_tmp_rhs30).cs;
      if ((_643_period).Empty_q) {
        return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_Empty(), _644_cs));
      } else {
        let _645_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NonEmptyDigits(_644_cs);
        if ((_645_valueOrError0).IsFailure()) {
          return (_645_valueOrError0).PropagateFailure();
        } else {
          let _let_tmp_rhs31 = (_645_valueOrError0).Extract();
          let _646_num = (_let_tmp_rhs31).t;
          let _647_cs = (_let_tmp_rhs31).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Maybe.create_NonEmpty(Std_JSON_Grammar.jfrac.create_JFrac(_643_period, _646_num)), _647_cs));
        }
      }
    };
    static NumberFromParts(minus, num, frac, exp) {
      let _648_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.jnumber.create_JNumber((minus).dtor_t, (num).dtor_t, (frac).dtor_t, (exp).dtor_t), (exp).dtor_cs);
      return _648_sp;
    };
    static Number(cs) {
      let _649_minus = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.OptionalMinus(cs);
      let _650_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.TrimmedInt((_649_minus).dtor_cs);
      if ((_650_valueOrError0).IsFailure()) {
        return (_650_valueOrError0).PropagateFailure();
      } else {
        let _651_num = (_650_valueOrError0).Extract();
        let _652_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Frac((_651_num).dtor_cs);
        if ((_652_valueOrError1).IsFailure()) {
          return (_652_valueOrError1).PropagateFailure();
        } else {
          let _653_frac = (_652_valueOrError1).Extract();
          let _654_valueOrError2 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Exp((_653_frac).dtor_cs);
          if ((_654_valueOrError2).IsFailure()) {
            return (_654_valueOrError2).PropagateFailure();
          } else {
            let _655_exp = (_654_valueOrError2).Extract();
            return Std_Wrappers.Result.create_Success(Std_JSON_ZeroCopy_Deserializer_Numbers.__default.NumberFromParts(_649_minus, _651_num, _653_frac, _655_exp));
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
      let _656_valueOrError0 = (cs).AssertChar(new _dafny.CodePoint(':'.codePointAt(0)));
      if ((_656_valueOrError0).IsFailure()) {
        return (_656_valueOrError0).PropagateFailure();
      } else {
        let _657_cs = (_656_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_657_cs).Split());
      }
    };
    static KeyValueFromParts(k, colon, v) {
      let _658_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.jKeyValue.create_KeyValue((k).dtor_t, (colon).dtor_t, (v).dtor_t), (v).dtor_cs);
      return _658_sp;
    };
    static ElementSpec(t) {
      return Std_JSON_ConcreteSyntax_Spec.__default.KeyValue(t);
    };
    static Element(cs, json) {
      let _659_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.String(cs);
      if ((_659_valueOrError0).IsFailure()) {
        return (_659_valueOrError0).PropagateFailure();
      } else {
        let _660_k = (_659_valueOrError0).Extract();
        let _661_p = Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.Colon;
        let _662_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural((_660_k).dtor_cs, _661_p);
        if ((_662_valueOrError1).IsFailure()) {
          return (_662_valueOrError1).PropagateFailure();
        } else {
          let _663_colon = (_662_valueOrError1).Extract();
          let _664_valueOrError2 = ((json))((_663_colon).dtor_cs);
          if ((_664_valueOrError2).IsFailure()) {
            return (_664_valueOrError2).PropagateFailure();
          } else {
            let _665_v = (_664_valueOrError2).Extract();
            let _666_kv = Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.KeyValueFromParts(_660_k, _663_colon, _665_v);
            return Std_Wrappers.Result.create_Success(_666_kv);
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
      let _667_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Objects.__default.Bracketed(cs, json);
      if ((_667_valueOrError0).IsFailure()) {
        return (_667_valueOrError0).PropagateFailure();
      } else {
        let _668_sp = (_667_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_668_sp);
      }
    };
    static Open(cs) {
      let _669_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.OPEN);
      if ((_669_valueOrError0).IsFailure()) {
        return (_669_valueOrError0).PropagateFailure();
      } else {
        let _670_cs = (_669_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_670_cs).Split());
      }
    };
    static Close(cs) {
      let _671_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE);
      if ((_671_valueOrError0).IsFailure()) {
        return (_671_valueOrError0).PropagateFailure();
      } else {
        let _672_cs = (_671_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_672_cs).Split());
      }
    };
    static BracketedFromParts(open, elems, close) {
      let _673_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Bracketed.create_Bracketed((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _673_sp;
    };
    static AppendWithSuffix(elems, elem, sep) {
      let _674_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_NonEmpty((sep).dtor_t));
      let _675_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_674_suffixed)), (sep).dtor_cs);
      return _675_elems_k;
    };
    static AppendLast(elems, elem, sep) {
      let _676_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_Empty());
      let _677_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_676_suffixed)), (elem).dtor_cs);
      return _677_elems_k;
    };
    static Elements(json, open, elems) {
      TAIL_CALL_START: while (true) {
        let _678_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.Element((elems).dtor_cs, json);
        if ((_678_valueOrError0).IsFailure()) {
          return (_678_valueOrError0).PropagateFailure();
        } else {
          let _679_elem = (_678_valueOrError0).Extract();
          if (((_679_elem).dtor_cs).EOF_q) {
            return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
          } else {
            let _680_sep = Std_JSON_ZeroCopy_Deserializer_Core.__default.TryStructural((_679_elem).dtor_cs);
            let _681_s0 = (((_680_sep).dtor_t).dtor_t).Peek();
            if (((_681_s0) === (Std_JSON_ZeroCopy_Deserializer_Objects.__default.SEPARATOR)) && (((((_680_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _682_sep = _680_sep;
              let _683_elems = Std_JSON_ZeroCopy_Deserializer_Objects.__default.AppendWithSuffix(elems, _679_elem, _682_sep);
              let _in96 = json;
              let _in97 = open;
              let _in98 = _683_elems;
              json = _in96;
              open = _in97;
              elems = _in98;
              continue TAIL_CALL_START;
            } else if (((_681_s0) === (Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE)) && (((((_680_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _684_sep = _680_sep;
              let _685_elems_k = Std_JSON_ZeroCopy_Deserializer_Objects.__default.AppendLast(elems, _679_elem, _684_sep);
              let _686_bracketed = Std_JSON_ZeroCopy_Deserializer_Objects.__default.BracketedFromParts(open, _685_elems_k, _684_sep);
              return Std_Wrappers.Result.create_Success(_686_bracketed);
            } else {
              let _687_separator = Std_JSON_ZeroCopy_Deserializer_Objects.__default.SEPARATOR;
              let _688_pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_ExpectingAnyByte(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE, _687_separator), _681_s0));
              return _688_pr;
            }
          }
        }
      }
    };
    static Bracketed(cs, json) {
      let _689_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural(cs, Std_JSON_ZeroCopy_Deserializer_Objects.__default.Open);
      if ((_689_valueOrError0).IsFailure()) {
        return (_689_valueOrError0).PropagateFailure();
      } else {
        let _690_open = (_689_valueOrError0).Extract();
        let _691_elems = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.of(), (_690_open).dtor_cs);
        if ((((_690_open).dtor_cs).Peek()) === (Std_JSON_ZeroCopy_Deserializer_ObjectParams.__default.CLOSE)) {
          let _692_p = Std_JSON_ZeroCopy_Deserializer_Objects.__default.Close;
          let _693_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural((_690_open).dtor_cs, _692_p);
          if ((_693_valueOrError1).IsFailure()) {
            return (_693_valueOrError1).PropagateFailure();
          } else {
            let _694_close = (_693_valueOrError1).Extract();
            return Std_Wrappers.Result.create_Success(Std_JSON_ZeroCopy_Deserializer_Objects.__default.BracketedFromParts(_690_open, _691_elems, _694_close));
          }
        } else {
          return Std_JSON_ZeroCopy_Deserializer_Objects.__default.Elements(json, _690_open, _691_elems);
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
      let _695_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Bracketed(cs, json);
      if ((_695_valueOrError0).IsFailure()) {
        return (_695_valueOrError0).PropagateFailure();
      } else {
        let _696_sp = (_695_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success(_696_sp);
      }
    };
    static Open(cs) {
      let _697_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.OPEN);
      if ((_697_valueOrError0).IsFailure()) {
        return (_697_valueOrError0).PropagateFailure();
      } else {
        let _698_cs = (_697_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_698_cs).Split());
      }
    };
    static Close(cs) {
      let _699_valueOrError0 = (cs).AssertByte(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE);
      if ((_699_valueOrError0).IsFailure()) {
        return (_699_valueOrError0).PropagateFailure();
      } else {
        let _700_cs = (_699_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_700_cs).Split());
      }
    };
    static BracketedFromParts(open, elems, close) {
      let _701_sp = Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Bracketed.create_Bracketed((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _701_sp;
    };
    static AppendWithSuffix(elems, elem, sep) {
      let _702_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_NonEmpty((sep).dtor_t));
      let _703_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_702_suffixed)), (sep).dtor_cs);
      return _703_elems_k;
    };
    static AppendLast(elems, elem, sep) {
      let _704_suffixed = Std_JSON_Grammar.Suffixed.create_Suffixed((elem).dtor_t, Std_JSON_Grammar.Maybe.create_Empty());
      let _705_elems_k = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.Concat((elems).dtor_t, _dafny.Seq.of(_704_suffixed)), (elem).dtor_cs);
      return _705_elems_k;
    };
    static Elements(json, open, elems) {
      TAIL_CALL_START: while (true) {
        let _706_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.Element((elems).dtor_cs, json);
        if ((_706_valueOrError0).IsFailure()) {
          return (_706_valueOrError0).PropagateFailure();
        } else {
          let _707_elem = (_706_valueOrError0).Extract();
          if (((_707_elem).dtor_cs).EOF_q) {
            return Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_EOF());
          } else {
            let _708_sep = Std_JSON_ZeroCopy_Deserializer_Core.__default.TryStructural((_707_elem).dtor_cs);
            let _709_s0 = (((_708_sep).dtor_t).dtor_t).Peek();
            if (((_709_s0) === (Std_JSON_ZeroCopy_Deserializer_Arrays.__default.SEPARATOR)) && (((((_708_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _710_sep = _708_sep;
              let _711_elems = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.AppendWithSuffix(elems, _707_elem, _710_sep);
              let _in99 = json;
              let _in100 = open;
              let _in101 = _711_elems;
              json = _in99;
              open = _in100;
              elems = _in101;
              continue TAIL_CALL_START;
            } else if (((_709_s0) === (Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE)) && (((((_708_sep).dtor_t).dtor_t).Length()) === (1))) {
              let _712_sep = _708_sep;
              let _713_elems_k = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.AppendLast(elems, _707_elem, _712_sep);
              let _714_bracketed = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.BracketedFromParts(open, _713_elems_k, _712_sep);
              return Std_Wrappers.Result.create_Success(_714_bracketed);
            } else {
              let _715_separator = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.SEPARATOR;
              let _716_pr = Std_Wrappers.Result.create_Failure(Std_JSON_Utils_Cursors.CursorError.create_ExpectingAnyByte(_dafny.Seq.of(Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE, _715_separator), _709_s0));
              return _716_pr;
            }
          }
        }
      }
    };
    static Bracketed(cs, json) {
      let _717_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural(cs, Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Open);
      if ((_717_valueOrError0).IsFailure()) {
        return (_717_valueOrError0).PropagateFailure();
      } else {
        let _718_open = (_717_valueOrError0).Extract();
        let _719_elems = Std_JSON_Utils_Cursors.Split.create_SP(_dafny.Seq.of(), (_718_open).dtor_cs);
        if ((((_718_open).dtor_cs).Peek()) === (Std_JSON_ZeroCopy_Deserializer_ArrayParams.__default.CLOSE)) {
          let _720_p = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Close;
          let _721_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural((_718_open).dtor_cs, _720_p);
          if ((_721_valueOrError1).IsFailure()) {
            return (_721_valueOrError1).PropagateFailure();
          } else {
            let _722_close = (_721_valueOrError1).Extract();
            return Std_Wrappers.Result.create_Success(Std_JSON_ZeroCopy_Deserializer_Arrays.__default.BracketedFromParts(_718_open, _719_elems, _722_close));
          }
        } else {
          return Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Elements(json, _718_open, _719_elems);
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
      let _723_valueOrError0 = (cs).AssertBytes(expected, 0);
      if ((_723_valueOrError0).IsFailure()) {
        return (_723_valueOrError0).PropagateFailure();
      } else {
        let _724_cs = (_723_valueOrError0).Extract();
        return Std_Wrappers.Result.create_Success((_724_cs).Split());
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
      let _725_c = (cs).Peek();
      if ((_725_c) === ((new _dafny.CodePoint('{'.codePointAt(0))).value)) {
        let _726_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_Objects.__default.Object(cs, Std_JSON_ZeroCopy_Deserializer_Values.__default.ValueParser(cs));
        if ((_726_valueOrError0).IsFailure()) {
          return (_726_valueOrError0).PropagateFailure();
        } else {
          let _let_tmp_rhs32 = (_726_valueOrError0).Extract();
          let _727_obj = (_let_tmp_rhs32).t;
          let _728_cs_k = (_let_tmp_rhs32).cs;
          let _729_v = Std_JSON_Grammar.Value.create_Object(_727_obj);
          let _730_sp = Std_JSON_Utils_Cursors.Split.create_SP(_729_v, _728_cs_k);
          return Std_Wrappers.Result.create_Success(_730_sp);
        }
      } else if ((_725_c) === ((new _dafny.CodePoint('['.codePointAt(0))).value)) {
        let _731_valueOrError1 = Std_JSON_ZeroCopy_Deserializer_Arrays.__default.Array(cs, Std_JSON_ZeroCopy_Deserializer_Values.__default.ValueParser(cs));
        if ((_731_valueOrError1).IsFailure()) {
          return (_731_valueOrError1).PropagateFailure();
        } else {
          let _let_tmp_rhs33 = (_731_valueOrError1).Extract();
          let _732_arr = (_let_tmp_rhs33).t;
          let _733_cs_k = (_let_tmp_rhs33).cs;
          let _734_v = Std_JSON_Grammar.Value.create_Array(_732_arr);
          let _735_sp = Std_JSON_Utils_Cursors.Split.create_SP(_734_v, _733_cs_k);
          return Std_Wrappers.Result.create_Success(_735_sp);
        }
      } else if ((_725_c) === ((new _dafny.CodePoint('\"'.codePointAt(0))).value)) {
        let _736_valueOrError2 = Std_JSON_ZeroCopy_Deserializer_Strings.__default.String(cs);
        if ((_736_valueOrError2).IsFailure()) {
          return (_736_valueOrError2).PropagateFailure();
        } else {
          let _let_tmp_rhs34 = (_736_valueOrError2).Extract();
          let _737_str = (_let_tmp_rhs34).t;
          let _738_cs_k = (_let_tmp_rhs34).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_String(_737_str), _738_cs_k));
        }
      } else if ((_725_c) === ((new _dafny.CodePoint('t'.codePointAt(0))).value)) {
        let _739_valueOrError3 = Std_JSON_ZeroCopy_Deserializer_Constants.__default.Constant(cs, Std_JSON_Grammar.__default.TRUE);
        if ((_739_valueOrError3).IsFailure()) {
          return (_739_valueOrError3).PropagateFailure();
        } else {
          let _let_tmp_rhs35 = (_739_valueOrError3).Extract();
          let _740_cst = (_let_tmp_rhs35).t;
          let _741_cs_k = (_let_tmp_rhs35).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_Bool(_740_cst), _741_cs_k));
        }
      } else if ((_725_c) === ((new _dafny.CodePoint('f'.codePointAt(0))).value)) {
        let _742_valueOrError4 = Std_JSON_ZeroCopy_Deserializer_Constants.__default.Constant(cs, Std_JSON_Grammar.__default.FALSE);
        if ((_742_valueOrError4).IsFailure()) {
          return (_742_valueOrError4).PropagateFailure();
        } else {
          let _let_tmp_rhs36 = (_742_valueOrError4).Extract();
          let _743_cst = (_let_tmp_rhs36).t;
          let _744_cs_k = (_let_tmp_rhs36).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_Bool(_743_cst), _744_cs_k));
        }
      } else if ((_725_c) === ((new _dafny.CodePoint('n'.codePointAt(0))).value)) {
        let _745_valueOrError5 = Std_JSON_ZeroCopy_Deserializer_Constants.__default.Constant(cs, Std_JSON_Grammar.__default.NULL);
        if ((_745_valueOrError5).IsFailure()) {
          return (_745_valueOrError5).PropagateFailure();
        } else {
          let _let_tmp_rhs37 = (_745_valueOrError5).Extract();
          let _746_cst = (_let_tmp_rhs37).t;
          let _747_cs_k = (_let_tmp_rhs37).cs;
          return Std_Wrappers.Result.create_Success(Std_JSON_Utils_Cursors.Split.create_SP(Std_JSON_Grammar.Value.create_Null(_746_cst), _747_cs_k));
        }
      } else {
        let _748_valueOrError6 = Std_JSON_ZeroCopy_Deserializer_Numbers.__default.Number(cs);
        if ((_748_valueOrError6).IsFailure()) {
          return (_748_valueOrError6).PropagateFailure();
        } else {
          let _let_tmp_rhs38 = (_748_valueOrError6).Extract();
          let _749_num = (_let_tmp_rhs38).t;
          let _750_cs_k = (_let_tmp_rhs38).cs;
          let _751_v = Std_JSON_Grammar.Value.create_Number(_749_num);
          let _752_sp = Std_JSON_Utils_Cursors.Split.create_SP(_751_v, _750_cs_k);
          return Std_Wrappers.Result.create_Success(_752_sp);
        }
      }
    };
    static ValueParser(cs) {
      let _753_pre = ((_754_cs) => function (_755_ps_k) {
        return ((_755_ps_k).Length()) < ((_754_cs).Length());
      })(cs);
      let _756_fn = ((_757_pre) => function (_758_ps_k) {
        return Std_JSON_ZeroCopy_Deserializer_Values.__default.Value(_758_ps_k);
      })(_753_pre);
      return _756_fn;
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
        let _759___mcc_h0 = (_source24).expected;
        let _760___mcc_h1 = (_source24).b;
        let _761_b = _760___mcc_h1;
        let _762_expected = _759___mcc_h0;
        return Std_JSON_Errors.DeserializationError.create_ExpectingByte(_762_expected, _761_b);
      } else if (_source24.is_ExpectingAnyByte) {
        let _763___mcc_h2 = (_source24).expected__sq;
        let _764___mcc_h3 = (_source24).b;
        let _765_b = _764___mcc_h3;
        let _766_expected__sq = _763___mcc_h2;
        return Std_JSON_Errors.DeserializationError.create_ExpectingAnyByte(_766_expected__sq, _765_b);
      } else {
        let _767___mcc_h4 = (_source24).err;
        let _768_err = _767___mcc_h4;
        return _768_err;
      }
    };
    static JSON(cs) {
      return (Std_JSON_ZeroCopy_Deserializer_Core.__default.Structural(cs, Std_JSON_ZeroCopy_Deserializer_Values.__default.Value)).MapFailure(Std_JSON_ZeroCopy_Deserializer_API.__default.LiftCursorError);
    };
    static Text(v) {
      let _769_valueOrError0 = Std_JSON_ZeroCopy_Deserializer_API.__default.JSON(Std_JSON_Utils_Cursors.Cursor__.OfView(v));
      if ((_769_valueOrError0).IsFailure()) {
        return (_769_valueOrError0).PropagateFailure();
      } else {
        let _let_tmp_rhs39 = (_769_valueOrError0).Extract();
        let _770_text = (_let_tmp_rhs39).t;
        let _771_cs = (_let_tmp_rhs39).cs;
        let _772_valueOrError1 = Std_Wrappers.__default.Need((_771_cs).EOF_q, Std_JSON_Errors.DeserializationError.create_ExpectingEOF());
        if ((_772_valueOrError1).IsFailure()) {
          return (_772_valueOrError1).PropagateFailure();
        } else {
          return Std_Wrappers.Result.create_Success(_770_text);
        }
      }
    };
    static OfBytes(bs) {
      let _773_valueOrError0 = Std_Wrappers.__default.Need((new BigNumber((bs).length)).isLessThan(Std_BoundedInts.__default.TWO__TO__THE__32), Std_JSON_Errors.DeserializationError.create_IntOverflow());
      if ((_773_valueOrError0).IsFailure()) {
        return (_773_valueOrError0).PropagateFailure();
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
      let _774_valueOrError0 = Std_JSON_Serializer.__default.JSON(js);
      if ((_774_valueOrError0).IsFailure()) {
        return (_774_valueOrError0).PropagateFailure();
      } else {
        let _775_js = (_774_valueOrError0).Extract();
        return Std_JSON_ZeroCopy_API.__default.Serialize(_775_js);
      }
    };
    static SerializeAlloc(js) {
      let bs = Std_Wrappers.Result.Default([]);
      let _776_js;
      let _777_valueOrError0 = Std_Wrappers.Result.Default(Std_JSON_Grammar.Structural.Default(Std_JSON_Grammar.Value.Default()));
      _777_valueOrError0 = Std_JSON_Serializer.__default.JSON(js);
      if ((_777_valueOrError0).IsFailure()) {
        bs = (_777_valueOrError0).PropagateFailure();
        return bs;
      }
      _776_js = (_777_valueOrError0).Extract();
      let _out11;
      _out11 = Std_JSON_ZeroCopy_API.__default.SerializeAlloc(_776_js);
      bs = _out11;
      return bs;
    }
    static SerializeInto(js, bs) {
      let len = Std_Wrappers.Result.Default(0);
      let _778_js;
      let _779_valueOrError0 = Std_Wrappers.Result.Default(Std_JSON_Grammar.Structural.Default(Std_JSON_Grammar.Value.Default()));
      _779_valueOrError0 = Std_JSON_Serializer.__default.JSON(js);
      if ((_779_valueOrError0).IsFailure()) {
        len = (_779_valueOrError0).PropagateFailure();
        return len;
      }
      _778_js = (_779_valueOrError0).Extract();
      let _out12;
      _out12 = Std_JSON_ZeroCopy_API.__default.SerializeInto(_778_js, bs);
      len = _out12;
      return len;
    }
    static Deserialize(bs) {
      let _780_valueOrError0 = Std_JSON_ZeroCopy_API.__default.Deserialize(bs);
      if ((_780_valueOrError0).IsFailure()) {
        return (_780_valueOrError0).PropagateFailure();
      } else {
        let _781_js = (_780_valueOrError0).Extract();
        return Std_JSON_Deserializer.__default.JSON(_781_js);
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
let _module = (function() {
  let $module = {};

  return $module;
})(); // end of module _module
