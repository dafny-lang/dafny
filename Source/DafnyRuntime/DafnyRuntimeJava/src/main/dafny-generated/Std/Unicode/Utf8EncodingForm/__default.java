// Class __default
// Dafny class __default compiled into Java
package Std.Unicode.Utf8EncodingForm;

import Std.Wrappers.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;
import Std.Collections.Array.*;
import Std.Collections.Imap.*;
import Std.Collections.Map.*;
import Std.Collections.Set.*;
import Std.DynamicArray.*;
import Std.FileIO.*;
import Std.Arithmetic.MulInternals.*;
import Std.Arithmetic.ModInternals.*;
import Std.Arithmetic.DivInternals.*;
import Std.Arithmetic.DivMod.*;
import Std.Arithmetic.Power.*;
import Std.Arithmetic.Logarithm.*;
import Std.Arithmetic.Power2.*;
import Std.Strings.HexConversion.*;
import Std.Strings.DecimalConversion.*;
import Std.Strings.CharStrEscaping.*;
import Std.Strings.*;
import Std.Unicode.Base.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean IsMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.ONE)) {
      boolean _185_b = __default.IsWellFormedSingleCodeUnitSequence(s);
      return _185_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(2L))) {
      boolean _186_b = __default.IsWellFormedDoubleCodeUnitSequence(s);
      return _186_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(3L))) {
      boolean _187_b = __default.IsWellFormedTripleCodeUnitSequence(s);
      return _187_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))) {
      boolean _188_b = __default.IsWellFormedQuadrupleCodeUnitSequence(s);
      return _188_b;
    } else {
      return false;
    }
  }
  public static boolean IsWellFormedSingleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _189_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    return (true) && ((((_189_firstByte) == 0 ? 0 : 1) != -1) && (java.lang.Integer.compareUnsigned(_189_firstByte, (byte) 127) <= 0));
  }
  public static boolean IsWellFormedDoubleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _190_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _191_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    return ((java.lang.Integer.compareUnsigned((byte) 194, _190_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_190_firstByte, (byte) 223) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _191_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_191_secondByte, (byte) 191) <= 0));
  }
  public static boolean IsWellFormedTripleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _192_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _193_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _194_thirdByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    return ((((((_192_firstByte) == ((byte) 224)) && ((java.lang.Integer.compareUnsigned((byte) 160, _193_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_193_secondByte, (byte) 191) <= 0))) || (((java.lang.Integer.compareUnsigned((byte) 225, _192_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_192_firstByte, (byte) 236) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _193_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_193_secondByte, (byte) 191) <= 0)))) || (((_192_firstByte) == ((byte) 237)) && ((java.lang.Integer.compareUnsigned((byte) 128, _193_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_193_secondByte, (byte) 159) <= 0)))) || (((java.lang.Integer.compareUnsigned((byte) 238, _192_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_192_firstByte, (byte) 239) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _193_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_193_secondByte, (byte) 191) <= 0)))) && ((java.lang.Integer.compareUnsigned((byte) 128, _194_thirdByte) <= 0) && (java.lang.Integer.compareUnsigned(_194_thirdByte, (byte) 191) <= 0));
  }
  public static boolean IsWellFormedQuadrupleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _195_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _196_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _197_thirdByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    byte _198_fourthByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L))))));
    return ((((((_195_firstByte) == ((byte) 240)) && ((java.lang.Integer.compareUnsigned((byte) 144, _196_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_196_secondByte, (byte) 191) <= 0))) || (((java.lang.Integer.compareUnsigned((byte) 241, _195_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_195_firstByte, (byte) 243) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _196_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_196_secondByte, (byte) 191) <= 0)))) || (((_195_firstByte) == ((byte) 244)) && ((java.lang.Integer.compareUnsigned((byte) 128, _196_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_196_secondByte, (byte) 143) <= 0)))) && ((java.lang.Integer.compareUnsigned((byte) 128, _197_thirdByte) <= 0) && (java.lang.Integer.compareUnsigned(_197_thirdByte, (byte) 191) <= 0))) && ((java.lang.Integer.compareUnsigned((byte) 128, _198_fourthByte) <= 0) && (java.lang.Integer.compareUnsigned(_198_fourthByte, (byte) 191) <= 0));
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Byte>> SplitPrefixMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    if (((java.math.BigInteger.valueOf((s).length())).compareTo(java.math.BigInteger.ONE) >= 0) && (__default.IsWellFormedSingleCodeUnitSequence((s).take(java.math.BigInteger.ONE)))) {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), (s).take(java.math.BigInteger.ONE));
    } else if (((java.math.BigInteger.valueOf((s).length())).compareTo(java.math.BigInteger.valueOf(2L)) >= 0) && (__default.IsWellFormedDoubleCodeUnitSequence((s).take(java.math.BigInteger.valueOf(2L))))) {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), (s).take(java.math.BigInteger.valueOf(2L)));
    } else if (((java.math.BigInteger.valueOf((s).length())).compareTo(java.math.BigInteger.valueOf(3L)) >= 0) && (__default.IsWellFormedTripleCodeUnitSequence((s).take(java.math.BigInteger.valueOf(3L))))) {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), (s).take(java.math.BigInteger.valueOf(3L)));
    } else if (((java.math.BigInteger.valueOf((s).length())).compareTo(java.math.BigInteger.valueOf(4L)) >= 0) && (__default.IsWellFormedQuadrupleCodeUnitSequence((s).take(java.math.BigInteger.valueOf(4L))))) {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), (s).take(java.math.BigInteger.valueOf(4L)));
    } else {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_None(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE));
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValue(int v) {
    if (java.lang.Integer.compareUnsigned(v, 127) <= 0) {
      return __default.EncodeScalarValueSingleByte(v);
    } else if (java.lang.Integer.compareUnsigned(v, 2047) <= 0) {
      return __default.EncodeScalarValueDoubleByte(v);
    } else if (java.lang.Integer.compareUnsigned(v, 65535) <= 0) {
      return __default.EncodeScalarValueTripleByte(v);
    } else {
      return __default.EncodeScalarValueQuadrupleByte(v);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueSingleByte(int v) {
    byte _199_x = ((byte) ((int)  ((v) & (127))));
    byte _200_firstByte = (_199_x);
    return dafny.DafnySequence.<java.lang.Byte> of(_200_firstByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueDoubleByte(int v) {
    byte _201_x = ((byte) ((int)  ((v) & (63))));
    byte _202_y = ((byte) ((int)  (((int)  ((v) & (1984))) >>> ((byte) 6))));
    byte _203_firstByte = (byte) (byte)  ((byte)(((byte) 192) | ((_202_y))));
    byte _204_secondByte = (byte) (byte)  ((byte)(((byte) 128) | ((_201_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_203_firstByte, _204_secondByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueTripleByte(int v) {
    byte _205_x = ((byte) ((int)  ((v) & (63))));
    byte _206_y = ((byte) ((int)  (((int)  ((v) & (4032))) >>> ((byte) 6))));
    byte _207_z = ((byte) ((int)  (((int)  ((v) & (61440))) >>> ((byte) 12))));
    byte _208_firstByte = (byte) (byte)  ((byte)(((byte) 224) | ((_207_z))));
    byte _209_secondByte = (byte) (byte)  ((byte)(((byte) 128) | ((_206_y))));
    byte _210_thirdByte = (byte) (byte)  ((byte)(((byte) 128) | ((_205_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_208_firstByte, _209_secondByte, _210_thirdByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueQuadrupleByte(int v) {
    byte _211_x = ((byte) ((int)  ((v) & (63))));
    byte _212_y = ((byte) ((int)  (((int)  ((v) & (4032))) >>> ((byte) 6))));
    byte _213_z = ((byte) ((int)  (((int)  ((v) & (61440))) >>> ((byte) 12))));
    byte _214_u2 = ((byte) ((int)  (((int)  ((v) & (196608))) >>> ((byte) 16))));
    byte _215_u1 = ((byte) ((int)  (((int)  ((v) & (1835008))) >>> ((byte) 18))));
    byte _216_firstByte = (byte) (byte)  ((byte)(((byte) 240) | ((_215_u1))));
    byte _217_secondByte = (byte) (byte)  ((byte)(((byte) (byte)  ((byte)(((byte) 128) | ((byte) (byte) (((byte) (byte)  ((byte)(((_214_u2)) << ((byte) 4))))))))) | ((_213_z))));
    byte _218_thirdByte = (byte) (byte)  ((byte)(((byte) 128) | ((_212_y))));
    byte _219_fourthByte = (byte) (byte)  ((byte)(((byte) 128) | ((_211_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_216_firstByte, _217_secondByte, _218_thirdByte, _219_fourthByte);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Byte> m) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((m).length()), java.math.BigInteger.ONE)) {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m);
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((m).length()), java.math.BigInteger.valueOf(2L))) {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m);
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((m).length()), java.math.BigInteger.valueOf(3L))) {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m);
    } else {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m);
    }
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _220_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _221_x = (_220_firstByte);
    return java.lang.Byte.toUnsignedInt(_221_x);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _222_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _223_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    int _224_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_222_firstByte) & ((byte) 31))));
    int _225_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_223_secondByte) & ((byte) 63))));
    return (int)  (((int) (((int)  ((_224_y) << ((byte) 6))) & 0xFFFFFF)) | ((_225_x)));
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _226_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _227_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _228_thirdByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    int _229_z = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_226_firstByte) & ((byte) 15))));
    int _230_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_227_secondByte) & ((byte) 63))));
    int _231_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_228_thirdByte) & ((byte) 63))));
    return (int)  (((int)  (((int) (((int)  ((_229_z) << ((byte) 12))) & 0xFFFFFF)) | ((int) (((int)  ((_230_y) << ((byte) 6))) & 0xFFFFFF)))) | ((_231_x)));
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _232_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _233_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _234_thirdByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    byte _235_fourthByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L))))));
    int _236_u1 = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_232_firstByte) & ((byte) 7))));
    int _237_u2 = java.lang.Byte.toUnsignedInt((byte) dafny.Helpers.bv8ShiftRight((byte) (byte)  ((byte)((_233_secondByte) & ((byte) 48))), (byte) 4));
    int _238_z = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_233_secondByte) & ((byte) 15))));
    int _239_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_234_thirdByte) & ((byte) 63))));
    int _240_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_235_fourthByte) & ((byte) 63))));
    return (int)  (((int)  (((int)  (((int)  (((int) (((int)  ((_236_u1) << ((byte) 18))) & 0xFFFFFF)) | ((int) (((int)  ((_237_u2) << ((byte) 16))) & 0xFFFFFF)))) | ((int) (((int)  ((_238_z) << ((byte) 12))) & 0xFFFFFF)))) | ((int) (((int)  ((_239_y) << ((byte) 6))) & 0xFFFFFF)))) | ((_240_x)));
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> PartitionCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Byte> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>Default(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
    if ((s).equals(dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE))) {
      maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
      return maybeParts;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _241_result;
    _241_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Byte> _242_rest;
    _242_rest = s;
    while ((java.math.BigInteger.valueOf((_242_rest).length())).signum() == 1) {
      dafny.DafnySequence<? extends java.lang.Byte> _243_prefix;
      Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Byte>> _244_valueOrError0 = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>Default(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _244_valueOrError0 = __default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_242_rest);
      if ((_244_valueOrError0).IsFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor())) {
        maybeParts = (_244_valueOrError0).<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>PropagateFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor(), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
        return maybeParts;
      }
      _243_prefix = (_244_valueOrError0).Extract(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _241_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>concatenate(_241_result, dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(MinimalWellFormedCodeUnitSeq._typeDescriptor(), _243_prefix));
      _242_rest = (_242_rest).drop(java.math.BigInteger.valueOf((_243_prefix).length()));
    }
    maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), _241_result);
    return maybeParts;
  }
  public static dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> PartitionCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    return (__default.PartitionCodeUnitSequenceChecked(s)).Extract(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
  }
  public static boolean IsWellFormedCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    return (__default.PartitionCodeUnitSequenceChecked(s)).is_Some();
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarSequence(dafny.DafnySequence<? extends java.lang.Integer> vs)
  {
    dafny.DafnySequence<? extends java.lang.Byte> s = WellFormedCodeUnitSeq.defaultValue();
    if(true) {
      s = dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE);
      java.math.BigInteger _lo0 = java.math.BigInteger.ZERO;
      for (java.math.BigInteger _245_i = java.math.BigInteger.valueOf((vs).length()); _lo0.compareTo(_245_i) < 0; ) {
        _245_i = _245_i.subtract(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Byte> _246_next;
        _246_next = __default.EncodeScalarValue(((int)(java.lang.Object)((vs).select(dafny.Helpers.toInt((_245_i))))));
        s = dafny.DafnySequence.<java.lang.Byte>concatenate(_246_next, s);
      }
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Integer> DecodeCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _247_parts = __default.PartitionCodeUnitSequence(s);
    dafny.DafnySequence<? extends java.lang.Integer> _248_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Byte>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _247_parts);
    return _248_vs;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> DecodeCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Byte> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>Default(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _249_maybeParts;
    _249_maybeParts = __default.PartitionCodeUnitSequenceChecked(s);
    if ((_249_maybeParts).is_None()) {
      maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_None(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      return maybeVs;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _250_parts;
    _250_parts = (_249_maybeParts).dtor_value();
    dafny.DafnySequence<? extends java.lang.Integer> _251_vs;
    _251_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Byte>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _250_parts);
    maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_Some(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), _251_vs);
    return maybeVs;
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Utf8EncodingForm._default";
  }
}
