// Class __default
// Dafny class __default compiled into Java
package Std.Unicode.Utf8EncodingForm;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
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
      boolean _190_b = __default.IsWellFormedSingleCodeUnitSequence(s);
      return _190_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(2L))) {
      boolean _191_b = __default.IsWellFormedDoubleCodeUnitSequence(s);
      return _191_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(3L))) {
      boolean _192_b = __default.IsWellFormedTripleCodeUnitSequence(s);
      return _192_b;
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(4L))) {
      boolean _193_b = __default.IsWellFormedQuadrupleCodeUnitSequence(s);
      return _193_b;
    } else {
      return false;
    }
  }
  public static boolean IsWellFormedSingleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _194_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    return (true) && ((((_194_firstByte) == 0 ? 0 : 1) != -1) && (java.lang.Integer.compareUnsigned(_194_firstByte, (byte) 127) <= 0));
  }
  public static boolean IsWellFormedDoubleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _195_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _196_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    return ((java.lang.Integer.compareUnsigned((byte) 194, _195_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_195_firstByte, (byte) 223) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _196_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_196_secondByte, (byte) 191) <= 0));
  }
  public static boolean IsWellFormedTripleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _197_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _198_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _199_thirdByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    return ((((((_197_firstByte) == ((byte) 224)) && ((java.lang.Integer.compareUnsigned((byte) 160, _198_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_198_secondByte, (byte) 191) <= 0))) || (((java.lang.Integer.compareUnsigned((byte) 225, _197_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_197_firstByte, (byte) 236) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _198_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_198_secondByte, (byte) 191) <= 0)))) || (((_197_firstByte) == ((byte) 237)) && ((java.lang.Integer.compareUnsigned((byte) 128, _198_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_198_secondByte, (byte) 159) <= 0)))) || (((java.lang.Integer.compareUnsigned((byte) 238, _197_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_197_firstByte, (byte) 239) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _198_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_198_secondByte, (byte) 191) <= 0)))) && ((java.lang.Integer.compareUnsigned((byte) 128, _199_thirdByte) <= 0) && (java.lang.Integer.compareUnsigned(_199_thirdByte, (byte) 191) <= 0));
  }
  public static boolean IsWellFormedQuadrupleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    byte _200_firstByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _201_secondByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _202_thirdByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    byte _203_fourthByte = ((byte)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L))))));
    return ((((((_200_firstByte) == ((byte) 240)) && ((java.lang.Integer.compareUnsigned((byte) 144, _201_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_201_secondByte, (byte) 191) <= 0))) || (((java.lang.Integer.compareUnsigned((byte) 241, _200_firstByte) <= 0) && (java.lang.Integer.compareUnsigned(_200_firstByte, (byte) 243) <= 0)) && ((java.lang.Integer.compareUnsigned((byte) 128, _201_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_201_secondByte, (byte) 191) <= 0)))) || (((_200_firstByte) == ((byte) 244)) && ((java.lang.Integer.compareUnsigned((byte) 128, _201_secondByte) <= 0) && (java.lang.Integer.compareUnsigned(_201_secondByte, (byte) 143) <= 0)))) && ((java.lang.Integer.compareUnsigned((byte) 128, _202_thirdByte) <= 0) && (java.lang.Integer.compareUnsigned(_202_thirdByte, (byte) 191) <= 0))) && ((java.lang.Integer.compareUnsigned((byte) 128, _203_fourthByte) <= 0) && (java.lang.Integer.compareUnsigned(_203_fourthByte, (byte) 191) <= 0));
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
    byte _204_x = ((byte) ((int)  ((v) & (127))));
    byte _205_firstByte = (_204_x);
    return dafny.DafnySequence.<java.lang.Byte> of(_205_firstByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueDoubleByte(int v) {
    byte _206_x = ((byte) ((int)  ((v) & (63))));
    byte _207_y = ((byte) ((int)  (((int)  ((v) & (1984))) >>> ((byte) 6))));
    byte _208_firstByte = (byte) (byte)  ((byte)(((byte) 192) | ((_207_y))));
    byte _209_secondByte = (byte) (byte)  ((byte)(((byte) 128) | ((_206_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_208_firstByte, _209_secondByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueTripleByte(int v) {
    byte _210_x = ((byte) ((int)  ((v) & (63))));
    byte _211_y = ((byte) ((int)  (((int)  ((v) & (4032))) >>> ((byte) 6))));
    byte _212_z = ((byte) ((int)  (((int)  ((v) & (61440))) >>> ((byte) 12))));
    byte _213_firstByte = (byte) (byte)  ((byte)(((byte) 224) | ((_212_z))));
    byte _214_secondByte = (byte) (byte)  ((byte)(((byte) 128) | ((_211_y))));
    byte _215_thirdByte = (byte) (byte)  ((byte)(((byte) 128) | ((_210_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_213_firstByte, _214_secondByte, _215_thirdByte);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> EncodeScalarValueQuadrupleByte(int v) {
    byte _216_x = ((byte) ((int)  ((v) & (63))));
    byte _217_y = ((byte) ((int)  (((int)  ((v) & (4032))) >>> ((byte) 6))));
    byte _218_z = ((byte) ((int)  (((int)  ((v) & (61440))) >>> ((byte) 12))));
    byte _219_u2 = ((byte) ((int)  (((int)  ((v) & (196608))) >>> ((byte) 16))));
    byte _220_u1 = ((byte) ((int)  (((int)  ((v) & (1835008))) >>> ((byte) 18))));
    byte _221_firstByte = (byte) (byte)  ((byte)(((byte) 240) | ((_220_u1))));
    byte _222_secondByte = (byte) (byte)  ((byte)(((byte) (byte)  ((byte)(((byte) 128) | ((byte) (byte) (((byte) (byte)  ((byte)(((_219_u2)) << ((byte) 4))))))))) | ((_218_z))));
    byte _223_thirdByte = (byte) (byte)  ((byte)(((byte) 128) | ((_217_y))));
    byte _224_fourthByte = (byte) (byte)  ((byte)(((byte) 128) | ((_216_x))));
    return dafny.DafnySequence.<java.lang.Byte> of(_221_firstByte, _222_secondByte, _223_thirdByte, _224_fourthByte);
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
    byte _225_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _226_x = (_225_firstByte);
    return java.lang.Byte.toUnsignedInt(_226_x);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _227_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _228_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    int _229_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_227_firstByte) & ((byte) 31))));
    int _230_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_228_secondByte) & ((byte) 63))));
    return (int)  (((int) (((int)  ((_229_y) << ((byte) 6))) & 0xFFFFFF)) | ((_230_x)));
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _231_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _232_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _233_thirdByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    int _234_z = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_231_firstByte) & ((byte) 15))));
    int _235_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_232_secondByte) & ((byte) 63))));
    int _236_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_233_thirdByte) & ((byte) 63))));
    return (int)  (((int)  (((int) (((int)  ((_234_z) << ((byte) 12))) & 0xFFFFFF)) | ((int) (((int)  ((_235_y) << ((byte) 6))) & 0xFFFFFF)))) | ((_236_x)));
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(dafny.DafnySequence<? extends java.lang.Byte> m) {
    byte _237_firstByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    byte _238_secondByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    byte _239_thirdByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(2L))))));
    byte _240_fourthByte = ((byte)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.valueOf(3L))))));
    int _241_u1 = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_237_firstByte) & ((byte) 7))));
    int _242_u2 = java.lang.Byte.toUnsignedInt((byte) dafny.Helpers.bv8ShiftRight((byte) (byte)  ((byte)((_238_secondByte) & ((byte) 48))), (byte) 4));
    int _243_z = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_238_secondByte) & ((byte) 15))));
    int _244_y = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_239_thirdByte) & ((byte) 63))));
    int _245_x = java.lang.Byte.toUnsignedInt((byte) (byte)  ((byte)((_240_fourthByte) & ((byte) 63))));
    return (int)  (((int)  (((int)  (((int)  (((int) (((int)  ((_241_u1) << ((byte) 18))) & 0xFFFFFF)) | ((int) (((int)  ((_242_u2) << ((byte) 16))) & 0xFFFFFF)))) | ((int) (((int)  ((_243_z) << ((byte) 12))) & 0xFFFFFF)))) | ((int) (((int)  ((_244_y) << ((byte) 6))) & 0xFFFFFF)))) | ((_245_x)));
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> PartitionCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Byte> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>Default(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
    if ((s).equals(dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE))) {
      maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
      return maybeParts;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _246_result;
    _246_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Byte> _247_rest;
    _247_rest = s;
    while ((java.math.BigInteger.valueOf((_247_rest).length())).signum() == 1) {
      dafny.DafnySequence<? extends java.lang.Byte> _248_prefix;
      Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Byte>> _249_valueOrError0 = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>Default(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _249_valueOrError0 = __default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_247_rest);
      if ((_249_valueOrError0).IsFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor())) {
        maybeParts = (_249_valueOrError0).<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>PropagateFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor(), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
        return maybeParts;
      }
      _248_prefix = (_249_valueOrError0).Extract(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _246_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>concatenate(_246_result, dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(MinimalWellFormedCodeUnitSeq._typeDescriptor(), _248_prefix));
      _247_rest = (_247_rest).drop(java.math.BigInteger.valueOf((_248_prefix).length()));
    }
    maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), _246_result);
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
      for (java.math.BigInteger _250_i = java.math.BigInteger.valueOf((vs).length()); _lo0.compareTo(_250_i) < 0; ) {
        _250_i = _250_i.subtract(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Byte> _251_next;
        _251_next = __default.EncodeScalarValue(((int)(java.lang.Object)((vs).select(dafny.Helpers.toInt((_250_i))))));
        s = dafny.DafnySequence.<java.lang.Byte>concatenate(_251_next, s);
      }
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Integer> DecodeCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Byte> s) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _252_parts = __default.PartitionCodeUnitSequence(s);
    dafny.DafnySequence<? extends java.lang.Integer> _253_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Byte>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _252_parts);
    return _253_vs;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> DecodeCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Byte> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>Default(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _254_maybeParts;
    _254_maybeParts = __default.PartitionCodeUnitSequenceChecked(s);
    if ((_254_maybeParts).is_None()) {
      maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_None(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      return maybeVs;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _255_parts;
    _255_parts = (_254_maybeParts).dtor_value();
    dafny.DafnySequence<? extends java.lang.Integer> _256_vs;
    _256_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Byte>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _255_parts);
    maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_Some(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), _256_vs);
    return maybeVs;
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Utf8EncodingForm._default";
  }
}
