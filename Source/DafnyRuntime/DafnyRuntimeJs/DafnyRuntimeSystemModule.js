// Dafny program systemModulePopulator.dfy compiled into JavaScript
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
let _module = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "_module._default";
    }
    _parentTraits() {
      return [];
    }
    static HasTuples() {
      let _0_has0;
      _0_has0 = _dafny.Tuple.of();
      let _1_has1;
      _1_has1 = _dafny.ONE;
      let _2_has2;
      _2_has2 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2));
      let _3_has3;
      _3_has3 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3));
      let _4_has4;
      _4_has4 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4));
      let _5_has5;
      _5_has5 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5));
      let _6_has6;
      _6_has6 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6));
      let _7_has7;
      _7_has7 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7));
      let _8_has8;
      _8_has8 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8));
      let _9_has9;
      _9_has9 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9));
      let _10_has10;
      _10_has10 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10));
      let _11_has11;
      _11_has11 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11));
      let _12_has12;
      _12_has12 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12));
      let _13_has13;
      _13_has13 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13));
      let _14_has14;
      _14_has14 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14));
      let _15_has15;
      _15_has15 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15));
      let _16_has16;
      _16_has16 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15), new BigNumber(16));
      let _17_has17;
      _17_has17 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15), new BigNumber(16), new BigNumber(17));
      let _18_has18;
      _18_has18 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15), new BigNumber(16), new BigNumber(17), new BigNumber(18));
      let _19_has19;
      _19_has19 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15), new BigNumber(16), new BigNumber(17), new BigNumber(18), new BigNumber(19));
      let _20_has20;
      _20_has20 = _dafny.Tuple.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15), new BigNumber(16), new BigNumber(17), new BigNumber(18), new BigNumber(19), new BigNumber(20));
      return;
    }
    static HasArrows() {
      let _21_has0;
      _21_has0 = function () {
        return new BigNumber(42);
      };
      let _22_has1;
      _22_has1 = function (_23_x1) {
        return new BigNumber(42);
      };
      let _24_has2;
      _24_has2 = function (_25_x1, _26_x2) {
        return new BigNumber(42);
      };
      let _27_has3;
      _27_has3 = function (_28_x1, _29_x2, _30_x3) {
        return new BigNumber(42);
      };
      let _31_has4;
      _31_has4 = function (_32_x1, _33_x2, _34_x3, _35_x4) {
        return new BigNumber(42);
      };
      let _36_has5;
      _36_has5 = function (_37_x1, _38_x2, _39_x3, _40_x4, _41_x5) {
        return new BigNumber(42);
      };
      let _42_has6;
      _42_has6 = function (_43_x1, _44_x2, _45_x3, _46_x4, _47_x5, _48_x6) {
        return new BigNumber(42);
      };
      let _49_has7;
      _49_has7 = function (_50_x1, _51_x2, _52_x3, _53_x4, _54_x5, _55_x6, _56_x7) {
        return new BigNumber(42);
      };
      let _57_has8;
      _57_has8 = function (_58_x1, _59_x2, _60_x3, _61_x4, _62_x5, _63_x6, _64_x7, _65_x8) {
        return new BigNumber(42);
      };
      let _66_has9;
      _66_has9 = function (_67_x1, _68_x2, _69_x3, _70_x4, _71_x5, _72_x6, _73_x7, _74_x8, _75_x9) {
        return new BigNumber(42);
      };
      let _76_has10;
      _76_has10 = function (_77_x1, _78_x2, _79_x3, _80_x4, _81_x5, _82_x6, _83_x7, _84_x8, _85_x9, _86_x10) {
        return new BigNumber(42);
      };
      let _87_has11;
      _87_has11 = function (_88_x1, _89_x2, _90_x3, _91_x4, _92_x5, _93_x6, _94_x7, _95_x8, _96_x9, _97_x10, _98_x11) {
        return new BigNumber(42);
      };
      let _99_has12;
      _99_has12 = function (_100_x1, _101_x2, _102_x3, _103_x4, _104_x5, _105_x6, _106_x7, _107_x8, _108_x9, _109_x10, _110_x11, _111_x12) {
        return new BigNumber(42);
      };
      let _112_has13;
      _112_has13 = function (_113_x1, _114_x2, _115_x3, _116_x4, _117_x5, _118_x6, _119_x7, _120_x8, _121_x9, _122_x10, _123_x11, _124_x12, _125_x13) {
        return new BigNumber(42);
      };
      let _126_has14;
      _126_has14 = function (_127_x1, _128_x2, _129_x3, _130_x4, _131_x5, _132_x6, _133_x7, _134_x8, _135_x9, _136_x10, _137_x11, _138_x12, _139_x13, _140_x14) {
        return new BigNumber(42);
      };
      let _141_has15;
      _141_has15 = function (_142_x1, _143_x2, _144_x3, _145_x4, _146_x5, _147_x6, _148_x7, _149_x8, _150_x9, _151_x10, _152_x11, _153_x12, _154_x13, _155_x14, _156_x15) {
        return new BigNumber(42);
      };
      let _157_has16;
      _157_has16 = function (_158_x1, _159_x2, _160_x3, _161_x4, _162_x5, _163_x6, _164_x7, _165_x8, _166_x9, _167_x10, _168_x11, _169_x12, _170_x13, _171_x14, _172_x15, _173_x16) {
        return new BigNumber(42);
      };
      return;
    }
    static HasArrays() {
      let _174_has1;
      let _nw0 = Array((_dafny.ONE).toNumber()).fill(_dafny.ZERO);
      _174_has1 = _nw0;
      let _175_has2;
      let _nw1 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2));
      _175_has2 = _nw1;
      let _176_has3;
      let _nw2 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3));
      _176_has3 = _nw2;
      let _177_has4;
      let _nw3 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4));
      _177_has4 = _nw3;
      let _178_has5;
      let _nw4 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5));
      _178_has5 = _nw4;
      let _179_has6;
      let _nw5 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6));
      _179_has6 = _nw5;
      let _180_has7;
      let _nw6 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7));
      _180_has7 = _nw6;
      let _181_has8;
      let _nw7 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8));
      _181_has8 = _nw7;
      let _182_has9;
      let _nw8 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9));
      _182_has9 = _nw8;
      let _183_has10;
      let _nw9 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10));
      _183_has10 = _nw9;
      let _184_has11;
      let _nw10 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11));
      _184_has11 = _nw10;
      let _185_has12;
      let _nw11 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12));
      _185_has12 = _nw11;
      let _186_has13;
      let _nw12 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13));
      _186_has13 = _nw12;
      let _187_has14;
      let _nw13 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14));
      _187_has14 = _nw13;
      let _188_has15;
      let _nw14 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15));
      _188_has15 = _nw14;
      let _189_has16;
      let _nw15 = _dafny.newArray(_dafny.ZERO, _dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4), new BigNumber(5), new BigNumber(6), new BigNumber(7), new BigNumber(8), new BigNumber(9), new BigNumber(10), new BigNumber(11), new BigNumber(12), new BigNumber(13), new BigNumber(14), new BigNumber(15), new BigNumber(16));
      _189_has16 = _nw15;
      return;
    }
  };
  return $module;
})(); // end of module _module
