// Class __default
// Dafny class __default compiled into Java
package Std.Unicode.Utf16EncodingForm;

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
import Std.Unicode.Utf8EncodingForm.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean IsMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.ONE)) {
      return __default.IsWellFormedSingleCodeUnitSequence(s);
    } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((s).length()), java.math.BigInteger.valueOf(2L))) {
      boolean _257_b = __default.IsWellFormedDoubleCodeUnitSequence(s);
      return _257_b;
    } else {
      return false;
    }
  }
  public static boolean IsWellFormedSingleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    short _258_firstWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    return ((((_258_firstWord) == 0 ? 0 : 1) != -1) && (java.lang.Integer.compareUnsigned(_258_firstWord, (short) 55295) <= 0)) || ((java.lang.Integer.compareUnsigned((short) 57344, _258_firstWord) <= 0) && (java.lang.Integer.compareUnsigned(_258_firstWord, (short) 65535) <= 0));
  }
  public static boolean IsWellFormedDoubleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    short _259_firstWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _260_secondWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    return ((java.lang.Integer.compareUnsigned((short) 55296, _259_firstWord) <= 0) && (java.lang.Integer.compareUnsigned(_259_firstWord, (short) 56319) <= 0)) && ((java.lang.Integer.compareUnsigned((short) 56320, _260_secondWord) <= 0) && (java.lang.Integer.compareUnsigned(_260_secondWord, (short) 57343) <= 0));
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
    short _261_firstWord = ((short) (v));
    return dafny.DafnySequence.<java.lang.Short> of(_261_firstWord);
  }
  public static dafny.DafnySequence<? extends java.lang.Short> EncodeScalarValueDoubleWord(int v) {
    short _262_x2 = ((short) ((int)  ((v) & (1023))));
    byte _263_x1 = ((byte) ((int)  (((int)  ((v) & (64512))) >>> ((byte) 10))));
    byte _264_u = ((byte) ((int)  (((int)  ((v) & (2031616))) >>> ((byte) 16))));
    byte _265_w = ((byte) (byte) (((byte) (byte)  ((byte)((_264_u) - ((byte) 1)))) & (byte) 0x1F));
    short _266_firstWord = (short) (short)  ((short)(((short) (short)  ((short)(((short) 55296) | ((short) (short) (((short) (short)  ((short)(((short) java.lang.Byte.toUnsignedInt(_265_w)) << ((byte) 6))))))))) | ((short) java.lang.Byte.toUnsignedInt(_263_x1))));
    short _267_secondWord = (short) (short)  ((short)(((short) 56320) | ((_262_x2))));
    return dafny.DafnySequence.<java.lang.Short> of(_266_firstWord, _267_secondWord);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Short> m) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((m).length()), java.math.BigInteger.ONE)) {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m);
    } else {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m);
    }
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(dafny.DafnySequence<? extends java.lang.Short> m) {
    short _268_firstWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _269_x = (_268_firstWord);
    return java.lang.Short.toUnsignedInt(_269_x);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(dafny.DafnySequence<? extends java.lang.Short> m) {
    short _270_firstWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _271_secondWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    int _272_x2 = java.lang.Short.toUnsignedInt((short) (short)  ((short)((_271_secondWord) & ((short) 1023))));
    int _273_x1 = java.lang.Short.toUnsignedInt((short) (short)  ((short)((_270_firstWord) & ((short) 63))));
    int _274_w = java.lang.Short.toUnsignedInt((short) dafny.Helpers.bv16ShiftRight((short) (short)  ((short)((_270_firstWord) & ((short) 960))), (byte) 6));
    int _275_u = ((int) (((int)  ((_274_w) + (1))) & 0xFFFFFF));
    int _276_v = (int)  (((int)  (((int) (((int)  ((_275_u) << ((byte) 16))) & 0xFFFFFF)) | ((int) (((int)  ((_273_x1) << ((byte) 10))) & 0xFFFFFF)))) | ((_272_x2)));
    return _276_v;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> PartitionCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Short> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>Default(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
    if ((s).equals(dafny.DafnySequence.<java.lang.Short> empty(dafny.TypeDescriptor.SHORT))) {
      maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
      return maybeParts;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _277_result;
    _277_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Short> _278_rest;
    _278_rest = s;
    while ((java.math.BigInteger.valueOf((_278_rest).length())).signum() == 1) {
      dafny.DafnySequence<? extends java.lang.Short> _279_prefix;
      Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Short>> _280_valueOrError0 = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>Default(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _280_valueOrError0 = __default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_278_rest);
      if ((_280_valueOrError0).IsFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor())) {
        maybeParts = (_280_valueOrError0).<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>PropagateFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor(), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
        return maybeParts;
      }
      _279_prefix = (_280_valueOrError0).Extract(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _277_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>concatenate(_277_result, dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> of(MinimalWellFormedCodeUnitSeq._typeDescriptor(), _279_prefix));
      _278_rest = (_278_rest).drop(java.math.BigInteger.valueOf((_279_prefix).length()));
    }
    maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), _277_result);
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
      for (java.math.BigInteger _281_i = java.math.BigInteger.valueOf((vs).length()); _lo1.compareTo(_281_i) < 0; ) {
        _281_i = _281_i.subtract(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Short> _282_next;
        _282_next = __default.EncodeScalarValue(((int)(java.lang.Object)((vs).select(dafny.Helpers.toInt((_281_i))))));
        s = dafny.DafnySequence.<java.lang.Short>concatenate(_282_next, s);
      }
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Integer> DecodeCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _283_parts = __default.PartitionCodeUnitSequence(s);
    dafny.DafnySequence<? extends java.lang.Integer> _284_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Short>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _283_parts);
    return _284_vs;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> DecodeCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Short> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>Default(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> _285_maybeParts;
    _285_maybeParts = __default.PartitionCodeUnitSequenceChecked(s);
    if ((_285_maybeParts).is_None()) {
      maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_None(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      return maybeVs;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _286_parts;
    _286_parts = (_285_maybeParts).dtor_value();
    dafny.DafnySequence<? extends java.lang.Integer> _287_vs;
    _287_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Short>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _286_parts);
    maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_Some(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), _287_vs);
    return maybeVs;
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Utf16EncodingForm._default";
  }
}
