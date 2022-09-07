// Dafny program dafnyRuntime.dfy compiled into JavaScript
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
(function() {
  let $module = Helpers_Compile;

  return $module;
})(); // end of module Helpers_Compile
(function() {
  let $module = Dafny;

  $module.Validatable = class Validatable {
  };

  $module.Array = class Array {
  };

  $module.ArrayCell = class ArrayCell {
    constructor(tag) { this.$tag = tag; }
    static create_Set(value) {
      let $dt = new ArrayCell(0);
      $dt.value = value;
      return $dt;
    }
    static create_Unset() {
      let $dt = new ArrayCell(1);
      return $dt;
    }
    get is_Set() { return this.$tag === 0; }
    get is_Unset() { return this.$tag === 1; }
    get dtor_value() { return this.value; }
    toString() {
      if (this.$tag === 0) {
        return "Dafny_Compile.ArrayCell.Set" + "(" + _dafny.toString(this.value) + ")";
      } else if (this.$tag === 1) {
        return "Dafny_Compile.ArrayCell.Unset";
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
        return other.$tag === 1;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Dafny.ArrayCell.create_Unset();
    }
    static Rtd() {
      return class {
        static get Default() {
          return ArrayCell.Default();
        }
      };
    }
  }

  $module.ImmutableArray = class ImmutableArray {
  };

  $module.Vector = class Vector {
    constructor () {
      this._tname = "Dafny_Compile.Vector";
      this.storage = undefined;
      this.size = _dafny.ZERO;
    }
    _parentTraits() {
      return [Dafny.Validatable];
    }
    __ctor(length) {
      let _this = this;
      let _0_storage;
      let _out0;
      _out0 = Dafny.NewArray(length);
      _0_storage = _out0;
      (_this).storage = _0_storage;
      (_this).size = _dafny.ZERO;
      return;
    }
    Select(index) {
      let _this = this;
      return (_this.storage).Select(index);
    };
    Last() {
      let _this = this;
      return (_this.storage).Select((_this.size).minus((_dafny.ONE)));
    };
    AddLast(t) {
      let _this = this;
      if ((_this.size).isEqualTo(((_this.storage).Length()))) {
        (_this).Reallocate((_this).Max((_this).MIN__SIZE, ((_this.storage).Length()).multipliedBy((new BigNumber(2)))));
      }
      (_this.storage).Update(_this.size, t);
      (_this).size = (_this.size).plus((_dafny.ONE));
      return;
    }
    Max(a, b) {
      let _this = this;
      if ((a).isLessThan((b))) {
        return b;
      } else {
        return a;
      }
    };
    Reallocate(newCapacity) {
      let _this = this;
      let _1_newStorage;
      let _out1;
      _out1 = Dafny.NewArray(newCapacity);
      _1_newStorage = _out1;
      let _2_values;
      let _out2;
      _out2 = (_this.storage).Freeze(_this.size);
      _2_values = _out2;
      (_1_newStorage).UpdateSubarray(_dafny.ZERO, _2_values);
      (_this).storage = _1_newStorage;
      return;
    }
    RemoveLast() {
      let _this = this;
      let t = undefined;
      t = (_this.storage).Select((_this.size).minus((_dafny.ONE)));
      (_this).size = (_this.size).minus((_dafny.ONE));
      return t;
    }
    Append(other) {
      let _this = this;
      let _3_newSize;
      _3_newSize = (_this.size).plus(((other).Length()));
      if (((_this.storage).Length()).isLessThan((_3_newSize))) {
        (_this).Reallocate((_this).Max(_3_newSize, ((_this.storage).Length()).multipliedBy((new BigNumber(2)))));
      }
      (_this.storage).UpdateSubarray(_this.size, other);
      (_this).size = (_this.size).plus(((other).Length()));
      return;
    }
    Freeze() {
      let _this = this;
      let ret = undefined;
      let _out3;
      _out3 = (_this.storage).Freeze(_this.size);
      ret = _out3;
      return ret;
    }
    get MIN__SIZE() {
      let _this = this;
      return new BigNumber(10);
    };
  };


  $module.Sequence = class Sequence {
    static HashCode(_this) {
      let ret = _dafny.ZERO;
      ret = _dafny.ZERO;
      let _hi0 = (_this).Length();
      for (let _4_i = _dafny.ZERO; _4_i.isLessThan(_hi0); _4_i = _4_i.plus(_dafny.ONE)) {
        let _5_element;
        let _out4;
        _out4 = (_this).Select(_4_i);
        _5_element = _out4;
        ret = _dafny.BitwiseXor(_dafny.BitwiseOr((_dafny.ShiftLeft(ret, new BigNumber(3))).mod(new BigNumber(2).exponentiatedBy(32)), (_dafny.ShiftRight(ret, new BigNumber(29))).mod(new BigNumber(2).exponentiatedBy(32))), Helpers_Compile.HashCode(_5_element));
      }
      return ret;
    }
    static ToString(_this) {
      let ret = '';
      ret = "[";
      let _hi1 = (_this).Length();
      for (let _6_i = _dafny.ZERO; _6_i.isLessThan(_hi1); _6_i = _6_i.plus(_dafny.ONE)) {
        if (!(_6_i).isEqualTo((_dafny.ZERO))) {
          ret = _dafny.Seq.Concat(ret, ",");
        }
        let _7_element;
        let _out5;
        _out5 = (_this).Select(_6_i);
        _7_element = _out5;
        ret = _dafny.Seq.Concat(ret, Helpers_Compile.ToString(_7_element));
      }
      ret = _dafny.Seq.Concat(ret, "]");
      return ret;
    }
    static Select(_this, index) {
      let ret = undefined;
      let _8_a;
      let _out6;
      _out6 = (_this).ToArray();
      _8_a = _out6;
      ret = (_8_a).Select(index);
      return ret;
      return ret;
    }
    static Drop(_this, lo) {
      let ret = undefined;
      let _out7;
      _out7 = (_this).Subsequence(lo, (_this).Length());
      ret = _out7;
      return ret;
    }
    static Take(_this, hi) {
      let ret = undefined;
      let _out8;
      _out8 = (_this).Subsequence(_dafny.ZERO, hi);
      ret = _out8;
      return ret;
    }
    static Subsequence(_this, lo, hi) {
      let ret = undefined;
      let _9_a;
      let _out9;
      _out9 = (_this).ToArray();
      _9_a = _out9;
      let _10_subarray;
      let _out10;
      _out10 = (_9_a).Subarray(lo, hi);
      _10_subarray = _out10;
      let _nw0 = new Dafny.ArraySequence();
      _nw0.__ctor(_10_subarray);
      ret = _nw0;
      return ret;
    }
  };

  $module.ArraySequence = class ArraySequence {
    constructor () {
      this._tname = "Dafny_Compile.ArraySequence";
      this._value = undefined;
    }
    _parentTraits() {
      return [Dafny.Sequence];
    }
    HashCode() {
      let _this = this;
      let _out11;
      _out11 = Dafny.Sequence.HashCode(_this);
      return _out11;
    }
    ToString() {
      let _this = this;
      let _out12;
      _out12 = Dafny.Sequence.ToString(_this);
      return _out12;
    }
    Select(index) {
      let _this = this;
      let _out13;
      _out13 = Dafny.Sequence.Select(_this, index);
      return _out13;
    }
    Drop(lo) {
      let _this = this;
      let _out14;
      _out14 = Dafny.Sequence.Drop(_this, lo);
      return _out14;
    }
    Take(hi) {
      let _this = this;
      let _out15;
      _out15 = Dafny.Sequence.Take(_this, hi);
      return _out15;
    }
    Subsequence(lo, hi) {
      let _this = this;
      let _out16;
      _out16 = Dafny.Sequence.Subsequence(_this, lo, hi);
      return _out16;
    }
    __ctor(value) {
      let _this = this;
      (_this)._value = value;
      return;
    }
    Length() {
      let _this = this;
      return ((_this).value).Length();
    };
    ToArray() {
      let _this = this;
      let ret = undefined;
      ret = (_this).value;
      return ret;
      return ret;
    }
    get value() {
      let _this = this;
      return _this._value;
    };
  };

  $module.ConcatSequence = class ConcatSequence {
    constructor () {
      this._tname = "Dafny_Compile.ConcatSequence";
      this._left = undefined;
      this._right = undefined;
      this._length = _dafny.ZERO;
    }
    _parentTraits() {
      return [Dafny.Sequence];
    }
    HashCode() {
      let _this = this;
      let _out17;
      _out17 = Dafny.Sequence.HashCode(_this);
      return _out17;
    }
    ToString() {
      let _this = this;
      let _out18;
      _out18 = Dafny.Sequence.ToString(_this);
      return _out18;
    }
    Select(index) {
      let _this = this;
      let _out19;
      _out19 = Dafny.Sequence.Select(_this, index);
      return _out19;
    }
    Drop(lo) {
      let _this = this;
      let _out20;
      _out20 = Dafny.Sequence.Drop(_this, lo);
      return _out20;
    }
    Take(hi) {
      let _this = this;
      let _out21;
      _out21 = Dafny.Sequence.Take(_this, hi);
      return _out21;
    }
    Subsequence(lo, hi) {
      let _this = this;
      let _out22;
      _out22 = Dafny.Sequence.Subsequence(_this, lo, hi);
      return _out22;
    }
    __ctor(left, right) {
      let _this = this;
      (_this)._left = left;
      (_this)._right = right;
      (_this)._length = ((left).Length()).plus(((right).Length()));
      return;
    }
    Length() {
      let _this = this;
      return (_this).length;
    };
    ToArray() {
      let _this = this;
      let ret = undefined;
      let _11_builder;
      let _nw1 = new Dafny.Vector();
      _nw1.__ctor((_this).length);
      _11_builder = _nw1;
      let _12_stack;
      let _nw2 = new Dafny.Vector();
      _nw2.__ctor(new BigNumber(10));
      _12_stack = _nw2;
      Dafny.__default.AppendOptimized(_11_builder, _this, _12_stack);
      let _out23;
      _out23 = (_11_builder).Freeze();
      ret = _out23;
      return ret;
    }
    get left() {
      let _this = this;
      return _this._left;
    };
    get right() {
      let _this = this;
      return _this._right;
    };
    get length() {
      let _this = this;
      return _this._length;
    };
  };

  $module.LazySequence = class LazySequence {
    constructor () {
      this._tname = "Dafny_Compile.LazySequence";
      this._length = _dafny.ZERO;
      this._box = undefined;
    }
    _parentTraits() {
      return [Dafny.Sequence];
    }
    HashCode() {
      let _this = this;
      let _out24;
      _out24 = Dafny.Sequence.HashCode(_this);
      return _out24;
    }
    ToString() {
      let _this = this;
      let _out25;
      _out25 = Dafny.Sequence.ToString(_this);
      return _out25;
    }
    Select(index) {
      let _this = this;
      let _out26;
      _out26 = Dafny.Sequence.Select(_this, index);
      return _out26;
    }
    Drop(lo) {
      let _this = this;
      let _out27;
      _out27 = Dafny.Sequence.Drop(_this, lo);
      return _out27;
    }
    Take(hi) {
      let _this = this;
      let _out28;
      _out28 = Dafny.Sequence.Take(_this, hi);
      return _out28;
    }
    Subsequence(lo, hi) {
      let _this = this;
      let _out29;
      _out29 = Dafny.Sequence.Subsequence(_this, lo, hi);
      return _out29;
    }
    __ctor(wrapped) {
      let _this = this;
      let _13_box;
      let _out30;
      _out30 = Dafny.AtomicBox.Make(wrapped);
      _13_box = _out30;
      (_this)._box = _13_box;
      (_this)._length = (wrapped).Length();
      return;
    }
    Length() {
      let _this = this;
      return (_this).length;
    };
    ToArray() {
      let _this = this;
      let ret = undefined;
      let _14_expr;
      let _out31;
      _out31 = ((_this).box).Get();
      _14_expr = _out31;
      let _out32;
      _out32 = (_14_expr).ToArray();
      ret = _out32;
      let _15_arraySeq;
      let _nw3 = new Dafny.ArraySequence();
      _nw3.__ctor(ret);
      _15_arraySeq = _nw3;
      ((_this).box).Put(_15_arraySeq);
      return ret;
    }
    get length() {
      let _this = this;
      return _this._length;
    };
    get box() {
      let _this = this;
      return _this._box;
    };
  };

  $module.__default = class __default extends $module.__default {
    constructor () {
      super();
      this._tname = "Dafny_Compile._default";
    }
    _parentTraits() {
      return [];
    }
    static AppendRecursive(builder, e) {
      if (function (_is_0) {
        return _is_0 instanceof Dafny.ConcatSequence;
      }(e)) {
        let _16_concat;
        _16_concat = e;
        Dafny.__default.AppendRecursive(builder, (_16_concat).left);
        Dafny.__default.AppendRecursive(builder, (_16_concat).right);
      } else if (function (_is_1) {
        return _is_1 instanceof Dafny.LazySequence;
      }(e)) {
        let _17_lazy;
        _17_lazy = e;
        let _18_boxed;
        let _out33;
        _out33 = ((_17_lazy).box).Get();
        _18_boxed = _out33;
        Dafny.__default.AppendRecursive(builder, _18_boxed);
      } else {
        let _19_a;
        let _out34;
        _out34 = (e).ToArray();
        _19_a = _out34;
        (builder).Append(_19_a);
      }
      return;
    }
    static AppendOptimized(builder, e, stack) {
      TAIL_CALL_START: while (true) {
        if (function (_is_2) {
          return _is_2 instanceof Dafny.ConcatSequence;
        }(e)) {
          let _20_concat;
          _20_concat = e;
          (stack).AddLast((_20_concat).right);
          let _in0 = builder;
          let _in1 = (_20_concat).left;
          let _in2 = stack;
          builder = _in0;
          e = _in1;
          stack = _in2;
          continue TAIL_CALL_START;
        } else if (function (_is_3) {
          return _is_3 instanceof Dafny.LazySequence;
        }(e)) {
          let _21_lazy;
          _21_lazy = e;
          let _22_boxed;
          let _out35;
          _out35 = ((_21_lazy).box).Get();
          _22_boxed = _out35;
          let _in3 = builder;
          let _in4 = _22_boxed;
          let _in5 = stack;
          builder = _in3;
          e = _in4;
          stack = _in5;
          continue TAIL_CALL_START;
        } else if (function (_is_4) {
          return _is_4 instanceof Dafny.ArraySequence;
        }(e)) {
          let _23_a;
          _23_a = e;
          (builder).Append((_23_a).value);
          if ((_dafny.ZERO).isLessThan((stack.size))) {
            let _24_next;
            let _out36;
            _out36 = (stack).RemoveLast();
            _24_next = _out36;
            let _in6 = builder;
            let _in7 = _24_next;
            let _in8 = stack;
            builder = _in6;
            e = _in7;
            stack = _in8;
            continue TAIL_CALL_START;
          }
        } else {
        }
        return;
        return;
      }
    }
    static EqualUpTo(left, right, index) {
      let ret = false;
      let _hi2 = index;
      for (let _25_i = _dafny.ZERO; _25_i.isLessThan(_hi2); _25_i = _25_i.plus(_dafny.ONE)) {
        let _26_leftElement;
        let _out37;
        _out37 = (left).Select(_25_i);
        _26_leftElement = _out37;
        let _27_rightElement;
        let _out38;
        _out38 = (right).Select(_25_i);
        _27_rightElement = _out38;
        if (!_dafny.areEqual(_26_leftElement, _27_rightElement)) {
          ret = false;
          return ret;
        }
      }
      ret = true;
      return ret;
      return ret;
    }
    static EqualSequences(left, right) {
      let ret = false;
      if (!((left).Length()).isEqualTo(((right).Length()))) {
        ret = false;
        return ret;
      }
      let _out39;
      _out39 = Dafny.__default.EqualUpTo(left, right, (left).Length());
      ret = _out39;
      return ret;
    }
    static IsPrefixOf(left, right) {
      let ret = false;
      if (((right).Length()).isLessThan(((left).Length()))) {
        ret = false;
        return ret;
      }
      let _out40;
      _out40 = Dafny.__default.EqualUpTo(left, right, (left).Length());
      ret = _out40;
      return ret;
    }
    static IsProperPrefixOf(left, right) {
      let ret = false;
      if (((right).Length()).isLessThanOrEqualTo(((left).Length()))) {
        ret = false;
        return ret;
      }
      let _out41;
      _out41 = Dafny.__default.EqualUpTo(left, right, (left).Length());
      ret = _out41;
      return ret;
    }
    static Contains(s, t) {
      let _hresult = false;
      let _hi3 = (s).Length();
      for (let _28_i = _dafny.ZERO; _28_i.isLessThan(_hi3); _28_i = _28_i.plus(_dafny.ONE)) {
        let _29_element;
        let _out42;
        _out42 = (s).Select(_28_i);
        _29_element = _out42;
        if (_dafny.areEqual(_29_element, t)) {
          _hresult = true;
          return _hresult;
        }
      }
      _hresult = false;
      return _hresult;
      return _hresult;
    }
    static Concatenate(left, right) {
      let ret = undefined;
      let _30_c;
      let _nw4 = new Dafny.ConcatSequence();
      _nw4.__ctor(left, right);
      _30_c = _nw4;
      let _nw5 = new Dafny.LazySequence();
      _nw5.__ctor(_30_c);
      ret = _nw5;
      return ret;
    }
    static Update(s, i, t) {
      let ret = undefined;
      let _31_a;
      let _out43;
      _out43 = (s).ToArray();
      _31_a = _out43;
      let _32_newValue;
      let _out44;
      _out44 = Dafny.CopyArray(_31_a);
      _32_newValue = _out44;
      (_32_newValue).Update(i, t);
      let _33_newValueFrozen;
      let _out45;
      _out45 = (_32_newValue).Freeze((_32_newValue).Length());
      _33_newValueFrozen = _out45;
      let _nw6 = new Dafny.ArraySequence();
      _nw6.__ctor(_33_newValueFrozen);
      ret = _nw6;
      return ret;
    }
    static MultiDimentionalArrays() {
      let _34_a;
      let _nw7 = _dafny.newArray(undefined, (new BigNumber(3)).toNumber(), (new BigNumber(4)).toNumber(), (new BigNumber(5)).toNumber());
      let _arrayinit0 = function (_35_i, _36_j, _37_k) {
        return _dafny.ZERO;
      };
      for (let _arrayinit_00 = 0; _arrayinit_00 < new BigNumber(_nw7.dims[0]); _arrayinit_00++) {
        for (let _arrayinit_10 = 0; _arrayinit_10 < new BigNumber(_nw7.dims[1]); _arrayinit_10++) {
          for (let _arrayinit_20 = 0; _arrayinit_20 < new BigNumber(_nw7.dims[2]); _arrayinit_20++) {
            _nw7.elmts[_arrayinit_00][_arrayinit_10][_arrayinit_20] = _arrayinit0(new BigNumber(_arrayinit_00), new BigNumber(_arrayinit_10), new BigNumber(_arrayinit_20));
          }
        }
      }
      _34_a = _nw7;
      (_34_a).elmts[(_dafny.ONE)][(_dafny.ONE)][(_dafny.ONE)] = new BigNumber(42);
      return;
    }
  };
  return $module;
})(); // end of module Dafny
let _module = (function() {
  let $module = {};

  return $module;
})(); // end of module _module
