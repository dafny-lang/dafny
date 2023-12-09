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
      boolean _179_b = __default.IsWellFormedSingleCodeUnitSequence(s);
      return _179_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(2L))) {
      boolean _180_b = __default.IsWellFormedDoubleCodeUnitSequence(s);
      return _180_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(3L))) {
      boolean _181_b = __default.IsWellFormedTripleCodeUnitSequence(s);
      return _181_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))) {
      boolean _182_b = __default.IsWellFormedQuadrupleCodeUnitSequence(s);
      return _182_b;
    } else {
      return false;
    }
  }
  public static boolean IsWellFormedSingleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _183_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    return (true) && ((((_183_firstByte) == 0 ? 0 : 1) != -1) && (java.lang.Integer.compareUnsigned(_183_firstByte, (byte) 127) <= 0));
  }
  public static boolean IsWellFormedDoubleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _184_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _185_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    return ((java.lang.Integer.compareUnsigned((byte) 194, _184_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_184_firstByte, (byte) 223) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _185_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_185_secondByte, (byte) 191) <= 0));
  }
  public static boolean IsWellFormedTripleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _186_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _187_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _188_thirdByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    return ((((((_186_firstByte) == ((byte) 224)) && ((java.lang.Integer.compareUnsigned((byte) 160, _187_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_187_secondByte, (byte) 191) <= 0))) || (((java.lang.Integer.compareUnsigned((byte) 225, _186_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_186_firstByte, (byte) 236) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _187_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_187_secondByte, (byte) 191) <= 0)))) || (((_186_firstByte) == ((byte) 237)) && ((java.lang.Integer.compareUnsigned((byte) 128, _187_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_187_secondByte, (byte) 159) <= 0)))) || (((java.lang.Integer.compareUnsigned((byte) 238, _186_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_186_firstByte, (byte) 239) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _187_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_187_secondByte, (byte) 191) <= 0)))) && ((java.lang.Integer.compareUnsigned((byte) 128, _188_thirdByte) <= 0) && (java.lang.Integer.compareUnsigned(_188_thirdByte, (byte) 191) <= 0));
  }
  public static boolean IsWellFormedQuadrupleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _189_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _190_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _191_thirdByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    byte _192_fourthByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L))))));
    return ((((((_189_firstByte) == ((byte) 240)) && ((java.lang.Integer.compareUnsigned((byte) 144, _190_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_190_secondByte, (byte) 191) <= 0))) || (((java.lang.Integer.compareUnsigned((byte) 241, _189_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_189_firstByte, (byte) 243) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _190_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_190_secondByte, (byte) 191) <= 0)))) || (((_189_firstByte) == ((byte) 244)) && ((java.lang.Integer.compareUnsigned((byte) 128, _190_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_190_secondByte, (byte) 143) <= 0)))) && ((java.lang.Integer.compareUnsigned((byte) 128, _191_thirdByte) <= 0) && (java.lang.Integer.compareUnsigned(_191_thirdByte, (byte) 191) <= 0))) && ((java.lang.Integer.compareUnsigned((byte) 128, _192_fourthByte) <= 0) && (java.lang.Integer.compareUnsigned(_192_fourthByte, (byte) 191) <= 0));
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
    byte _193_x = ((byte) ((int)  ((v) & (127))));
    byte _194_firstByte = (_193_x);
    return dafny.DafnySequence.<java.lang.Byte> of(_194_firstByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueDoubleByte(int v) {
    byte _195_x = ((byte) ((int)  ((v) & (63))));
    byte _196_y = ((byte) ((int)  (((int)  ((v) & (1984))) >>> ((byte) 6))));
    byte _197_firstByte = (byte) (byte)  ((byte)(((byte) 192) | ((_196_y))));
    byte _198_secondByte = (byte) (byte)  ((byte)(((byte) 128) | ((_195_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_197_firstByte, _198_secondByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueTripleByte(int v) {
    byte _199_x = ((byte) ((int)  ((v) & (63))));
    byte _200_y = ((byte) ((int)  (((int)  ((v) & (4032))) >>> ((byte) 6))));
    byte _201_z = ((byte) ((int)  (((int)  ((v) & (61440))) >>> ((byte) 12))));
    byte _202_firstByte = (byte) (byte)  ((byte)(((byte) 224) | ((_201_z))));
    byte _203_secondByte = (byte) (byte)  ((byte)(((byte) 128) | ((_200_y))));
    byte _204_thirdByte = (byte) (byte)  ((byte)(((byte) 128) | ((_199_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_202_firstByte, _203_secondByte, _204_thirdByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueQuadrupleByte(int v) {
    byte _205_x = ((byte) ((int)  ((v) & (63))));
    byte _206_y = ((byte) ((int)  (((int)  ((v) & (4032))) >>> ((byte) 6))));
    byte _207_z = ((byte) ((int)  (((int)  ((v) & (61440))) >>> ((byte) 12))));
    byte _208_u2 = ((byte) ((int)  (((int)  ((v) & (196608))) >>> ((byte) 16))));
    byte _209_u1 = ((byte) ((int)  (((int)  ((v) & (1835008))) >>> ((byte) 18))));
    byte _210_firstByte = (byte) (byte)  ((byte)(((byte) 240) | ((_209_u1))));
    byte _211_secondByte = (byte) (byte)  ((byte)(((byte) (byte)  ((byte)(((byte) 128) | ((byte) (byte) (((byte) (byte)  ((byte)(((_208_u2)) << ((byte) 4))))))))) | ((_207_z))));
    byte _212_thirdByte = (byte) (byte)  ((byte)(((byte) 128) | ((_206_y))));
    byte _213_fourthByte = (byte) (byte)  ((byte)(((byte) 128) | ((_205_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_210_firstByte, _211_secondByte, _212_thirdByte, _213_fourthByte);
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
    byte _214_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _215_x = (_214_firstByte);
    return java.lang.Byte.toUnsignedInt(_215_x);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _216_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _217_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    int _218_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_216_firstByte) & ((byte) 31))));
    int _219_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_217_secondByte) & ((byte) 63))));
    return (int)  (((int) (((int)  ((_218_y) << ((byte) 6))) & 0xFFFFFF)) | ((_219_x)));
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _220_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _221_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _222_thirdByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    int _223_z = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_220_firstByte) & ((byte) 15))));
    int _224_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_221_secondByte) & ((byte) 63))));
    int _225_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_222_thirdByte) & ((byte) 63))));
    return (int)  (((int)  (((int) (((int)  ((_223_z) << ((byte) 12))) & 0xFFFFFF)) | ((int) (((int)  ((_224_y) << ((byte) 6))) & 0xFFFFFF)))) | ((_225_x)));
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _226_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _227_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _228_thirdByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    byte _229_fourthByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L))))));
    int _230_u1 = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_226_firstByte) & ((byte) 7))));
    int _231_u2 = java.lang.Byte.toUnsignedInt((byte) dafny.Helpers.bv8ShiftRight((byte) (byte)  ((byte)((_227_secondByte) & ((byte) 48))), (byte) 4));
    int _232_z = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_227_secondByte) & ((byte) 15))));
    int _233_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_228_thirdByte) & ((byte) 63))));
    int _234_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_229_fourthByte) & ((byte) 63))));
    return (int)  (((int)  (((int)  (((int)  (((int) (((int)  ((_230_u1) << ((byte) 18))) & 0xFFFFFF)) | ((int) (((int)  ((_231_u2) << ((byte) 16))) & 0xFFFFFF)))) | ((int) (((int)  ((_232_z) << ((byte) 12))) & 0xFFFFFF)))) | ((int) (((int)  ((_233_y) << ((byte) 6))) & 0xFFFFFF)))) | ((_234_x)));
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> PartitionCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Byte> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>Default(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
    if ((s).equals(dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE))) {
      maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
      return maybeParts;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _235_result;
    _235_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Byte> _236_rest;
    _236_rest = s;
    while ((java.math.BigInteger.valueOf((_236_rest).length())).signum() == 1) {
      dafny.DafnySequence<? extends java.lang.Byte> _237_prefix;
      Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Byte>> _238_valueOrError0 = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>Default(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _238_valueOrError0 = __default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_236_rest);
      if ((_238_valueOrError0).IsFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor())) {
        maybeParts = (_238_valueOrError0).<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>PropagateFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor(), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
        return maybeParts;
      }
      _237_prefix = (_238_valueOrError0).Extract(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _235_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>concatenate(_235_result, dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(MinimalWellFormedCodeUnitSeq._typeDescriptor(), _237_prefix));
      _236_rest = (_236_rest).drop(java.math.BigInteger.valueOf((_237_prefix).length()));
    }
    maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), _235_result);
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
      for (java.math.BigInteger _239_i = java.math.BigInteger.valueOf((vs).length()); _lo0.compareTo(_239_i) < 0; ) {
        _239_i = _239_i.subtract(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Byte> _240_next;
        _240_next = __default.EncodeScalarValue(((int)(java.lang.Object)((vs).select(dafny.Helpers.toInt((_239_i))))));
        s = dafny.DafnySequence.<java.lang.Byte>concatenate(_240_next, s);
      }
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Integer> DecodeCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _241_parts = __default.PartitionCodeUnitSequence(s);
    dafny.DafnySequence<? extends java.lang.Integer> _242_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Byte>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _241_parts);
    return _242_vs;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> DecodeCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Byte> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>Default(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _243_maybeParts;
    _243_maybeParts = __default.PartitionCodeUnitSequenceChecked(s);
    if ((_243_maybeParts).is_None()) {
      maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_None(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      return maybeVs;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _244_parts;
    _244_parts = (_243_maybeParts).dtor_value();
    dafny.DafnySequence<? extends java.lang.Integer> _245_vs;
    _245_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Byte>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _244_parts);
    maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_Some(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), _245_vs);
    return maybeVs;
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Utf8EncodingForm._default";
  }
}
