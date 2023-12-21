// Class __default
// Dafny class __default compiled into Java
package Std.Unicode.Utf16EncodingForm;

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
import Std.Unicode.Utf8EncodingForm.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean IsMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.ONE)) {
      return __default.IsWellFormedSingleCodeUnitSequence(s);
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(2L))) {
      boolean _252_b = __default.IsWellFormedDoubleCodeUnitSequence(s);
      return _252_b;
    } else {
      return false;
    }
  }
  public static boolean IsWellFormedSingleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    short _253_firstWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    return ((((_253_firstWord) == 0 ? 0 : 1) != -1) && (java.lang.Integer.compareUnsigned(_253_firstWord, (short) 55295) <= 0)) || ((java.lang.Integer.compareUnsigned((short) 57344, _253_firstWord) <= 0) && (java.lang.Integer.compareUnsigned(_253_firstWord, (short) 65535) <= 0));
  }
  public static boolean IsWellFormedDoubleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    short _254_firstWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _255_secondWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    return ((java.lang.Integer.compareUnsigned((short) 55296, _254_firstWord) <= 0) && (java.lang.Integer.compareUnsigned(_254_firstWord, (short) 56319) <= 0)) && ((java.lang.Integer.compareUnsigned((short) 56320, _255_secondWord) <= 0) && (java.lang.Integer.compareUnsigned(_255_secondWord, (short) 57343) <= 0));
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Short>> SplitPrefixMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    if (((java.math.BigInteger.valueOf((s).length())).compareTo(java.math.BigInteger.ONE) >= 0) && (__default.IsWellFormedSingleCodeUnitSequence((s).take(java.math.BigInteger.ONE)))) {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>create_Some(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(dafny.TypeDescriptor.SHORT), (s).take(java.math.BigInteger.ONE));
    } else if (((java.math.BigInteger.valueOf((s).length())).compareTo(java.math.BigInteger.valueOf(2L)) >= 0) && (__default.IsWellFormedDoubleCodeUnitSequence((s).take(java.math.BigInteger.valueOf(2L))))) {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>create_Some(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(dafny.TypeDescriptor.SHORT), (s).take(java.math.BigInteger.valueOf(2L)));
    } else {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>create_None(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(dafny.TypeDescriptor.SHORT));
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Short> EncodeScalarValue(int v) {
    if (((((v) == 0 ? 0 : 1) != -1) && (java.lang.Integer.compareUnsigned(v, 55295) <= 0)) || ((java.lang.Integer.compareUnsigned(57344, v) <= 0) && (java.lang.Integer.compareUnsigned(v, 65535) <= 0))) {
      return __default.EncodeScalarValueSingleWord(v);
    } else {
      return __default.EncodeScalarValueDoubleWord(v);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Short> EncodeScalarValueSingleWord(int v) {
    short _256_firstWord = ((short) (v));
    return dafny.DafnySequence.<java.lang.Short> of(_256_firstWord);
  }
  public static dafny.DafnySequence<? extends java.lang.Short> EncodeScalarValueDoubleWord(int v) {
    short _257_x2 = ((short) ((int)  ((v) & (1023))));
    byte _258_x1 = ((byte) ((int)  (((int)  ((v) & (64512))) >>> ((byte) 10))));
    byte _259_u = ((byte) ((int)  (((int)  ((v) & (2031616))) >>> ((byte) 16))));
    byte _260_w = ((byte) (byte) (((byte) (byte)  ((byte)((_259_u) - ((byte) 1)))) & (byte) 0x1F));
    short _261_firstWord = (short) (short)  ((short)(((short) (short)  ((short)(((short) 55296) | ((short) (short) (((short) (short)  ((short)(((short) java.lang.Byte.toUnsignedInt(_260_w)) << ((byte) 6))))))))) | ((short) java.lang.Byte.toUnsignedInt(_258_x1))));
    short _262_secondWord = (short) (short)  ((short)(((short) 56320) | ((_257_x2))));
    return dafny.DafnySequence.<java.lang.Short> of(_261_firstWord, _262_secondWord);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Short> m) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((m).length()), java.math.BigInteger.ONE)) {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m);
    } else {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m);
    }
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(dafny.DafnySequence<? extends java.lang.Short> m) {
    short _263_firstWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _264_x = (_263_firstWord);
    return java.lang.Short.toUnsignedInt(_264_x);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(dafny.DafnySequence<? extends java.lang.Short> m) {
    short _265_firstWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _266_secondWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    int _267_x2 = java.lang.Short.toUnsignedInt((short) (short)  ((short)((_266_secondWord) & ((short) 1023))));
    int _268_x1 = java.lang.Short.toUnsignedInt((short) (short)  ((short)((_265_firstWord) & ((short) 63))));
    int _269_w = java.lang.Short.toUnsignedInt((short) dafny.Helpers.bv16ShiftRight((short) (short)  ((short)((_265_firstWord) & ((short) 960))), (byte) 6));
    int _270_u = ((int) (((int)  ((_269_w) + (1))) & 0xFFFFFF));
    int _271_v = (int)  (((int)  (((int) (((int)  ((_270_u) << ((byte) 16))) & 0xFFFFFF)) | ((int) (((int)  ((_268_x1) << ((byte) 10))) & 0xFFFFFF)))) | ((_267_x2)));
    return _271_v;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> PartitionCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Short> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>Default(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
    if ((s).equals(dafny.DafnySequence.<java.lang.Short> empty(dafny.TypeDescriptor.SHORT))) {
      maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
      return maybeParts;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _272_result;
    _272_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Short> _273_rest;
    _273_rest = s;
    while ((java.math.BigInteger.valueOf((_273_rest).length())).signum() == 1) {
      dafny.DafnySequence<? extends java.lang.Short> _274_prefix;
      Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Short>> _275_valueOrError0 = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>Default(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _275_valueOrError0 = __default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_273_rest);
      if ((_275_valueOrError0).IsFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor())) {
        maybeParts = (_275_valueOrError0).<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>PropagateFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor(), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
        return maybeParts;
      }
      _274_prefix = (_275_valueOrError0).Extract(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _272_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>concatenate(_272_result, dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> of(MinimalWellFormedCodeUnitSeq._typeDescriptor(), _274_prefix));
      _273_rest = (_273_rest).drop(java.math.BigInteger.valueOf((_274_prefix).length()));
    }
    maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), _272_result);
    return maybeParts;
  }
  public static dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> PartitionCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    return (__default.PartitionCodeUnitSequenceChecked(s)).Extract(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
  }
  public static boolean IsWellFormedCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    return (__default.PartitionCodeUnitSequenceChecked(s)).is_Some();
  }
  public static dafny.DafnySequence<? extends java.lang.Short> EncodeScalarSequence(dafny.DafnySequence<? extends java.lang.Integer> vs)
  {
    dafny.DafnySequence<? extends java.lang.Short> s = WellFormedCodeUnitSeq.defaultValue();
    if(true) {
      s = dafny.DafnySequence.<java.lang.Short> empty(dafny.TypeDescriptor.SHORT);
      java.math.BigInteger _lo1 = java.math.BigInteger.ZERO;
      for (java.math.BigInteger _276_i = java.math.BigInteger.valueOf((vs).length()); _lo1.compareTo(_276_i) < 0; ) {
        _276_i = _276_i.subtract(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Short> _277_next;
        _277_next = __default.EncodeScalarValue(((int)(java.lang.Object)((vs).select(dafny.Helpers.toInt((_276_i))))));
        s = dafny.DafnySequence.<java.lang.Short>concatenate(_277_next, s);
      }
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Integer> DecodeCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _278_parts = __default.PartitionCodeUnitSequence(s);
    dafny.DafnySequence<? extends java.lang.Integer> _279_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Short>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _278_parts);
    return _279_vs;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> DecodeCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Short> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>Default(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> _280_maybeParts;
    _280_maybeParts = __default.PartitionCodeUnitSequenceChecked(s);
    if ((_280_maybeParts).is_None()) {
      maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_None(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      return maybeVs;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _281_parts;
    _281_parts = (_280_maybeParts).dtor_value();
    dafny.DafnySequence<? extends java.lang.Integer> _282_vs;
    _282_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Short>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _281_parts);
    maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_Some(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), _282_vs);
    return maybeVs;
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Utf16EncodingForm._default";
  }
}
