// Class __default
// Dafny class __default compiled into Java
package Std.Base64;

import Std.Wrappers.*;
import Std.BoundedInts.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean IsBase64Char(int c) {
    return (((((c) == ('+')) || ((c) == ('/'))) || ((('0') <= (c)) && ((c) <= ('9')))) || ((('A') <= (c)) && ((c) <= ('Z')))) || ((('a') <= (c)) && ((c) <= ('z')));
  }
  public static boolean IsUnpaddedBase64String(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return ((dafny.DafnyEuclidean.EuclideanModulus(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))).signum() == 0) && (((java.util.function.Function<dafny.DafnySequence<? extends dafny.CodePoint>, Boolean>)(_28_s) -> dafny.Helpers.Quantifier((_28_s).UniqueElements(), true, ((_forall_var_0_boxed0) -> {
      int _forall_var_0 = ((dafny.CodePoint)(_forall_var_0_boxed0)).value();
      if (true) {
        int _29_k = (int)_forall_var_0;
        return !((_28_s).contains(dafny.CodePoint.valueOf(_29_k))) || (__default.IsBase64Char(_29_k));
      } else {
        return true;
      }
    }))).apply(s));
  }
  public static int IndexToChar(byte i) {
    if ((i) == ((byte) 63)) {
      return '/';
    } else if ((i) == ((byte) 62)) {
      return '+';
    } else if ((java.lang.Integer.compareUnsigned((byte) 52, i) <= 0) && (java.lang.Integer.compareUnsigned(i, (byte) 61) <= 0)) {
      return (int)java.lang.Byte.toUnsignedInt((byte) (byte) (((byte) (byte)  ((byte)((i) - ((byte) 4)))) & (byte) 0x3F));
    } else if ((java.lang.Integer.compareUnsigned((byte) 26, i) <= 0) && (java.lang.Integer.compareUnsigned(i, (byte) 51) <= 0)) {
      return (int) (((int)java.lang.Byte.toUnsignedInt(i)) + ((int)dafny.Helpers.toInt((java.math.BigInteger.valueOf(71L)))));
    } else {
      return (int) (((int)java.lang.Byte.toUnsignedInt(i)) + ((int)dafny.Helpers.toInt((java.math.BigInteger.valueOf(65L)))));
    }
  }
  public static byte CharToIndex(int c) {
    if ((c) == ('/')) {
      return (byte) 63;
    } else if ((c) == ('+')) {
      return (byte) 62;
    } else if ((('0') <= (c)) && ((c) <= ('9'))) {
      return ((byte) ((int) ((c) + ((int)dafny.Helpers.toInt((java.math.BigInteger.valueOf(4L)))))));
    } else if ((('a') <= (c)) && ((c) <= ('z'))) {
      return ((byte) ((int) ((c) - ((int)dafny.Helpers.toInt((java.math.BigInteger.valueOf(71L)))))));
    } else {
      return ((byte) ((int) ((c) - ((int)dafny.Helpers.toInt((java.math.BigInteger.valueOf(65L)))))));
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> BV24ToSeq(int x) {
    byte _30_b0 = ((byte) ((int)  (((int)  ((x) >>> ((byte) 16))) & (255))));
    byte _31_b1 = ((byte) ((int)  (((int)  ((x) >>> ((byte) 8))) & (255))));
    byte _32_b2 = ((byte) ((int)  ((x) & (255))));
    return dafny.DafnySequence.<java.lang.Byte> of(_30_b0, _31_b1, _32_b2);
  }
  public static int SeqToBV24(dafny.DafnySequence<? extends java.lang.Byte> x) {
    return (int)  (((int)  (((int) (((int)  ((java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((x).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))) << ((byte) 16))) & 0xFFFFFF)) | ((int) (((int)  ((java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((x).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))))) << ((byte) 8))) & 0xFFFFFF)))) | (java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((x).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L)))))))));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> BV24ToIndexSeq(int x) {
    byte _33_b0 = ((byte) ((int)  (((int)  ((x) >>> ((byte) 18))) & (63))));
    byte _34_b1 = ((byte) ((int)  (((int)  ((x) >>> ((byte) 12))) & (63))));
    byte _35_b2 = ((byte) ((int)  (((int)  ((x) >>> ((byte) 6))) & (63))));
    byte _36_b3 = ((byte) ((int)  ((x) & (63))));
    return dafny.DafnySequence.<java.lang.Byte> of(_33_b0, _34_b1, _35_b2, _36_b3);
  }
  public static int IndexSeqToBV24(dafny.DafnySequence<? extends java.lang.Byte> x) {
    return (int)  (((int)  (((int)  (((int) (((int)  ((java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((x).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))) << ((byte) 18))) & 0xFFFFFF)) | ((int) (((int)  ((java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((x).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))))) << ((byte) 12))) & 0xFFFFFF)))) | ((int) (((int)  ((java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((x).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L)))))))) << ((byte) 6))) & 0xFFFFFF)))) | (java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((x).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L)))))))));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> DecodeBlock(dafny.DafnySequence<? extends java.lang.Byte> s) {
    return __default.BV24ToSeq(__default.IndexSeqToBV24(s));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeBlock(dafny.DafnySequence<? extends java.lang.Byte> s) {
    return __default.BV24ToIndexSeq(__default.SeqToBV24(s));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> DecodeRecursively(dafny.DafnySequence<? extends java.lang.Byte> s)
  {
    dafny.DafnySequence<? extends java.lang.Byte> b = dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE);
    if(true) {
      java.math.BigInteger _37_resultLength = java.math.BigInteger.ZERO;
      _37_resultLength = (dafny.DafnyEuclidean.EuclideanDivision(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))).multiply(java.math.BigInteger.valueOf(3L));
      byte[] _38_result;
      java.util.function.Function<java.math.BigInteger, java.lang.Byte> _init0 = ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_39_i_boxed0) -> {
        java.math.BigInteger _39_i = ((java.math.BigInteger)(java.lang.Object)(_39_i_boxed0));
        return (byte) 0;
      });
      byte[] _nw0 = (byte[]) dafny.TypeDescriptor.BYTE.newArray(dafny.Helpers.toIntChecked((_37_resultLength), "Java arrays may be no larger than the maximum 32-bit signed int"));
      for (java.math.BigInteger _i0_0 = java.math.BigInteger.ZERO; _i0_0.compareTo(java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength(_nw0))) < 0; _i0_0 = _i0_0.add(java.math.BigInteger.ONE)) {
        _nw0[dafny.Helpers.toInt(_i0_0)] = ((byte)(java.lang.Object)(_init0.apply(_i0_0)));
      }
      _38_result = _nw0;
      java.math.BigInteger _40_i = java.math.BigInteger.ZERO;
      _40_i = java.math.BigInteger.valueOf((s).length());
      java.math.BigInteger _41_j = java.math.BigInteger.ZERO;
      _41_j = _37_resultLength;
      while ((_40_i).signum() == 1) {
        _40_i = (_40_i).subtract(java.math.BigInteger.valueOf(4L));
        _41_j = (_41_j).subtract(java.math.BigInteger.valueOf(3L));
        dafny.DafnySequence<? extends java.lang.Byte> _42_block;
        _42_block = __default.DecodeBlock((s).subsequence(dafny.Helpers.toInt((_40_i)), dafny.Helpers.toInt(((_40_i).add(java.math.BigInteger.valueOf(4L))))));
        (_38_result)[dafny.Helpers.toInt(((_41_j)).intValue())] = ((byte)(java.lang.Object)((_42_block).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
        java.math.BigInteger _index0 = (_41_j).add(java.math.BigInteger.ONE);
        (_38_result)[dafny.Helpers.toInt((_index0).intValue())] = ((byte)(java.lang.Object)((_42_block).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
        java.math.BigInteger _index1 = (_41_j).add(java.math.BigInteger.valueOf(2L));
        (_38_result)[dafny.Helpers.toInt((_index1).intValue())] = ((byte)(java.lang.Object)((_42_block).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
      }
      b = dafny.DafnySequence.fromRawArrayRange(dafny.TypeDescriptor.BYTE, (_38_result), 0, java.lang.reflect.Array.getLength(_38_result));
    }
    return b;
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeRecursively(dafny.DafnySequence<? extends java.lang.Byte> b)
  {
    dafny.DafnySequence<? extends java.lang.Byte> s = dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE);
    if(true) {
      java.math.BigInteger _43_resultLength = java.math.BigInteger.ZERO;
      _43_resultLength = (dafny.DafnyEuclidean.EuclideanDivision(java.math.BigInteger.valueOf((b).length()), java.math.BigInteger.valueOf(3L))).multiply(java.math.BigInteger.valueOf(4L));
      byte[] _44_result;
      java.util.function.Function<java.math.BigInteger, java.lang.Byte> _init1 = ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_45_i_boxed0) -> {
        java.math.BigInteger _45_i = ((java.math.BigInteger)(java.lang.Object)(_45_i_boxed0));
        return (byte) 0;
      });
      byte[] _nw1 = (byte[]) dafny.TypeDescriptor.BYTE.newArray(dafny.Helpers.toIntChecked((_43_resultLength), "Java arrays may be no larger than the maximum 32-bit signed int"));
      for (java.math.BigInteger _i0_1 = java.math.BigInteger.ZERO; _i0_1.compareTo(java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength(_nw1))) < 0; _i0_1 = _i0_1.add(java.math.BigInteger.ONE)) {
        _nw1[dafny.Helpers.toInt(_i0_1)] = ((byte)(java.lang.Object)(_init1.apply(_i0_1)));
      }
      _44_result = _nw1;
      java.math.BigInteger _46_i = java.math.BigInteger.ZERO;
      _46_i = java.math.BigInteger.valueOf((b).length());
      java.math.BigInteger _47_j = java.math.BigInteger.ZERO;
      _47_j = _43_resultLength;
      while ((_46_i).signum() == 1) {
        _46_i = (_46_i).subtract(java.math.BigInteger.valueOf(3L));
        _47_j = (_47_j).subtract(java.math.BigInteger.valueOf(4L));
        dafny.DafnySequence<? extends java.lang.Byte> _48_block;
        _48_block = __default.EncodeBlock((b).subsequence(dafny.Helpers.toInt((_46_i)), dafny.Helpers.toInt(((_46_i).add(java.math.BigInteger.valueOf(3L))))));
        (_44_result)[dafny.Helpers.toInt(((_47_j)).intValue())] = ((byte)(java.lang.Object)((_48_block).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
        java.math.BigInteger _index2 = (_47_j).add(java.math.BigInteger.ONE);
        (_44_result)[dafny.Helpers.toInt((_index2).intValue())] = ((byte)(java.lang.Object)((_48_block).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
        java.math.BigInteger _index3 = (_47_j).add(java.math.BigInteger.valueOf(2L));
        (_44_result)[dafny.Helpers.toInt((_index3).intValue())] = ((byte)(java.lang.Object)((_48_block).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
        java.math.BigInteger _index4 = (_47_j).add(java.math.BigInteger.valueOf(3L));
        (_44_result)[dafny.Helpers.toInt((_index4).intValue())] = ((byte)(java.lang.Object)((_48_block).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L))))));
      }
      s = dafny.DafnySequence.fromRawArrayRange(dafny.TypeDescriptor.BYTE, (_44_result), 0, java.lang.reflect.Array.getLength(_44_result));
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> FromCharsToIndices(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return dafny.DafnySequence.Create(dafny.TypeDescriptor.BYTE, java.math.BigInteger.valueOf((s).length()), ((java.util.function.Function<dafny.DafnySequence<? extends dafny.CodePoint>, java.util.function.Function<java.math.BigInteger, java.lang.Byte>>)(_49_s) -> ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_50_i_boxed0) -> {
      java.math.BigInteger _50_i = ((java.math.BigInteger)(java.lang.Object)(_50_i_boxed0));
      return __default.CharToIndex(((dafny.CodePoint)((_49_s).select(dafny.Helpers.toInt((_50_i))))).value());
    })).apply(s));
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> FromIndicesToChars(dafny.DafnySequence<? extends java.lang.Byte> b) {
    return dafny.DafnySequence.Create(dafny.TypeDescriptor.UNICODE_CHAR, java.math.BigInteger.valueOf((b).length()), ((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Byte>, java.util.function.Function<java.math.BigInteger, dafny.CodePoint>>)(_51_b) -> ((java.util.function.Function<java.math.BigInteger, dafny.CodePoint>)(_52_i_boxed0) -> {
      java.math.BigInteger _52_i = ((java.math.BigInteger)(java.lang.Object)(_52_i_boxed0));
      return dafny.CodePoint.valueOf(__default.IndexToChar(((byte)(java.lang.Object)((_51_b).select(dafny.Helpers.toInt((_52_i)))))));
    })).apply(b));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> DecodeUnpadded(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return __default.DecodeRecursively(__default.FromCharsToIndices(s));
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> EncodeUnpadded(dafny.DafnySequence<? extends java.lang.Byte> b) {
    return __default.FromIndicesToChars(__default.EncodeRecursively(b));
  }
  public static boolean Is1Padding(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return (((((java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))) && (__default.IsBase64Char(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()))) && (__default.IsBase64Char(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))).value()))) && (__default.IsBase64Char(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L)))))).value()))) && ((((byte) (byte)  ((byte)((__default.CharToIndex(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L)))))).value())) & ((byte) 3)))) == 0 ? 0 : 1) == 0)) && ((((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L)))))).value()) == ('='));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Decode1Padding(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    dafny.DafnySequence<? extends java.lang.Byte> _53_d = __default.DecodeBlock(dafny.DafnySequence.<java.lang.Byte> of(__default.CharToIndex(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()), __default.CharToIndex(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))).value()), __default.CharToIndex(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L)))))).value()), (byte) 0));
    return dafny.DafnySequence.<java.lang.Byte> of(((byte)(java.lang.Object)((_53_d).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), ((byte)(java.lang.Object)((_53_d).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))));
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> Encode1Padding(dafny.DafnySequence<? extends java.lang.Byte> b) {
    dafny.DafnySequence<? extends java.lang.Byte> _54_e = __default.EncodeBlock(dafny.DafnySequence.<java.lang.Byte> of(((byte)(java.lang.Object)((b).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), ((byte)(java.lang.Object)((b).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))), (byte) 0));
    return dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(__default.IndexToChar(((byte)(java.lang.Object)((_54_e).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))), dafny.CodePoint.valueOf(__default.IndexToChar(((byte)(java.lang.Object)((_54_e).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))))), dafny.CodePoint.valueOf(__default.IndexToChar(((byte)(java.lang.Object)((_54_e).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L)))))))), dafny.CodePoint.valueOf('='));
  }
  public static boolean Is2Padding(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return (((((java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))) && (__default.IsBase64Char(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()))) && (__default.IsBase64Char(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))).value()))) && (((dafny.Helpers.remainderUnsignedByte(__default.CharToIndex(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))).value()), (byte) 16)) == 0 ? 0 : 1) == 0)) && ((((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L)))))).value()) == ('='))) && ((((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L)))))).value()) == ('='));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Decode2Padding(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    dafny.DafnySequence<? extends java.lang.Byte> _55_d = __default.DecodeBlock(dafny.DafnySequence.<java.lang.Byte> of(__default.CharToIndex(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()), __default.CharToIndex(((dafny.CodePoint)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))).value()), (byte) 0, (byte) 0));
    return dafny.DafnySequence.<java.lang.Byte> of(((byte)(java.lang.Object)((_55_d).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))));
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> Encode2Padding(dafny.DafnySequence<? extends java.lang.Byte> b) {
    dafny.DafnySequence<? extends java.lang.Byte> _56_e = __default.EncodeBlock(dafny.DafnySequence.<java.lang.Byte> of(((byte)(java.lang.Object)((b).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), (byte) 0, (byte) 0));
    return dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(__default.IndexToChar(((byte)(java.lang.Object)((_56_e).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))), dafny.CodePoint.valueOf(__default.IndexToChar(((byte)(java.lang.Object)((_56_e).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))))), dafny.CodePoint.valueOf('='), dafny.CodePoint.valueOf('='));
  }
  public static boolean IsBase64String(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    java.math.BigInteger _57_finalBlockStart = (java.math.BigInteger.valueOf((s).length())).subtract(java.math.BigInteger.valueOf(4L));
    return ((dafny.DafnyEuclidean.EuclideanModulus(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))).signum() == 0) && ((__default.IsUnpaddedBase64String(s)) || ((__default.IsUnpaddedBase64String((s).take(_57_finalBlockStart))) && ((__default.Is1Padding((s).drop(_57_finalBlockStart))) || (__default.Is2Padding((s).drop(_57_finalBlockStart))))));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> DecodeValid(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    if ((s).equals(dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR))) {
      return dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE);
    } else {
      java.math.BigInteger _58_finalBlockStart = (java.math.BigInteger.valueOf((s).length())).subtract(java.math.BigInteger.valueOf(4L));
      dafny.DafnySequence<? extends dafny.CodePoint> _59_prefix = (s).take(_58_finalBlockStart);
      dafny.DafnySequence<? extends dafny.CodePoint> _60_suffix = (s).drop(_58_finalBlockStart);
      if (__default.Is1Padding(_60_suffix)) {
        return dafny.DafnySequence.<java.lang.Byte>concatenate(__default.DecodeUnpadded(_59_prefix), __default.Decode1Padding(_60_suffix));
      } else if (__default.Is2Padding(_60_suffix)) {
        return dafny.DafnySequence.<java.lang.Byte>concatenate(__default.DecodeUnpadded(_59_prefix), __default.Decode2Padding(_60_suffix));
      } else {
        return __default.DecodeUnpadded(s);
      }
    }
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> DecodeBV(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    if (__default.IsBase64String(s)) {
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), __default.DecodeValid(s));
    } else {
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.asUnicodeString("The encoding is malformed"));
    }
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> EncodeBV(dafny.DafnySequence<? extends java.lang.Byte> b) {
    if ((dafny.DafnyEuclidean.EuclideanModulus(java.math.BigInteger.valueOf((b).length()), java.math.BigInteger.valueOf(3L))).signum() == 0) {
      return __default.EncodeUnpadded(b);
    } else if (java.util.Objects.equals(dafny.DafnyEuclidean.EuclideanModulus(java.math.BigInteger.valueOf((b).length()), java.math.BigInteger.valueOf(3L)), java.math.BigInteger.ONE)) {
      dafny.DafnySequence<? extends dafny.CodePoint> _61_s1 = __default.EncodeUnpadded((b).take((java.math.BigInteger.valueOf((b).length())).subtract(java.math.BigInteger.ONE)));
      dafny.DafnySequence<? extends dafny.CodePoint> _62_s2 = __default.Encode2Padding((b).drop((java.math.BigInteger.valueOf((b).length())).subtract(java.math.BigInteger.ONE)));
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(_61_s1, _62_s2);
    } else {
      dafny.DafnySequence<? extends dafny.CodePoint> _63_s1 = __default.EncodeUnpadded((b).take((java.math.BigInteger.valueOf((b).length())).subtract(java.math.BigInteger.valueOf(2L))));
      dafny.DafnySequence<? extends dafny.CodePoint> _64_s2 = __default.Encode1Padding((b).drop((java.math.BigInteger.valueOf((b).length())).subtract(java.math.BigInteger.valueOf(2L))));
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(_63_s1, _64_s2);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> UInt8sToBVs(dafny.DafnySequence<? extends java.lang.Byte> u) {
    return dafny.DafnySequence.Create(dafny.TypeDescriptor.BYTE, java.math.BigInteger.valueOf((u).length()), ((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Byte>, java.util.function.Function<java.math.BigInteger, java.lang.Byte>>)(_65_u) -> ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_66_i_boxed0) -> {
      java.math.BigInteger _66_i = ((java.math.BigInteger)(java.lang.Object)(_66_i_boxed0));
      return (((byte)(java.lang.Object)((_65_u).select(dafny.Helpers.toInt((_66_i))))));
    })).apply(u));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> BVsToUInt8s(dafny.DafnySequence<? extends java.lang.Byte> b) {
    return dafny.DafnySequence.Create(Std.BoundedInts.uint8._typeDescriptor(), java.math.BigInteger.valueOf((b).length()), ((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Byte>, java.util.function.Function<java.math.BigInteger, java.lang.Byte>>)(_67_b) -> ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_68_i_boxed0) -> {
      java.math.BigInteger _68_i = ((java.math.BigInteger)(java.lang.Object)(_68_i_boxed0));
      return (((byte)(java.lang.Object)((_67_b).select(dafny.Helpers.toInt((_68_i))))));
    })).apply(b));
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> Encode(dafny.DafnySequence<? extends java.lang.Byte> u) {
    return __default.EncodeBV(__default.UInt8sToBVs(u));
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> Decode(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    if (__default.IsBase64String(s)) {
      dafny.DafnySequence<? extends java.lang.Byte> _69_b = __default.DecodeValid(s);
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), __default.BVsToUInt8s(_69_b));
    } else {
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.asUnicodeString("The encoding is malformed"));
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Base64._default";
  }
}
