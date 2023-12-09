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
      boolean _246_b = __default.IsWellFormedDoubleCodeUnitSequence(s);
      return _246_b;
    } else {
      return false;
    }
  }
  public static boolean IsWellFormedSingleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    short _247_firstWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    return ((((_247_firstWord) == 0 ? 0 : 1) != -1) && (java.lang.Integer.compareUnsigned(_247_firstWord, (short) 55295) <= 0)) || ((java.lang.Integer.compareUnsigned((short) 57344, _247_firstWord) <= 0) && (java.lang.Integer.compareUnsigned(_247_firstWord, (short) 65535) <= 0));
  }
  public static boolean IsWellFormedDoubleCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    short _248_firstWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _249_secondWord = ((short)(java.lang.Object)((s).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    return ((java.lang.Integer.compareUnsigned((short) 55296, _248_firstWord) <= 0) && (java.lang.Integer.compareUnsigned(_248_firstWord, (short) 56319) <= 0)) && ((java.lang.Integer.compareUnsigned((short) 56320, _249_secondWord) <= 0) && (java.lang.Integer.compareUnsigned(_249_secondWord, (short) 57343) <= 0));
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
    short _250_firstWord = ((short) (v));
    return dafny.DafnySequence.<java.lang.Short> of(_250_firstWord);
  }
  public static dafny.DafnySequence<? extends java.lang.Short> EncodeScalarValueDoubleWord(int v) {
    short _251_x2 = ((short) ((int)  ((v) & (1023))));
    byte _252_x1 = ((byte) ((int)  (((int)  ((v) & (64512))) >>> ((byte) 10))));
    byte _253_u = ((byte) ((int)  (((int)  ((v) & (2031616))) >>> ((byte) 16))));
    byte _254_w = ((byte) (byte) (((byte) (byte)  ((byte)((_253_u) - ((byte) 1)))) & (byte) 0x1F));
    short _255_firstWord = (short) (short)  ((short)(((short) (short)  ((short)(((short) 55296) | ((short) (short) (((short) (short)  ((short)(((short) java.lang.Byte.toUnsignedInt(_254_w)) << ((byte) 6))))))))) | ((short) java.lang.Byte.toUnsignedInt(_252_x1))));
    short _256_secondWord = (short) (short)  ((short)(((short) 56320) | ((_251_x2))));
    return dafny.DafnySequence.<java.lang.Short> of(_255_firstWord, _256_secondWord);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequence(dafny.DafnySequence<? extends java.lang.Short> m) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((m).length()), java.math.BigInteger.ONE)) {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m);
    } else {
      return __default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m);
    }
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(dafny.DafnySequence<? extends java.lang.Short> m) {
    short _257_firstWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _258_x = (_257_firstWord);
    return java.lang.Short.toUnsignedInt(_258_x);
  }
  public static int DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(dafny.DafnySequence<? extends java.lang.Short> m) {
    short _259_firstWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    short _260_secondWord = ((short)(java.lang.Object)((m).select(dafny.Helpers.toInt((java.math.BigInteger.ONE)))));
    int _261_x2 = java.lang.Short.toUnsignedInt((short) (short)  ((short)((_260_secondWord) & ((short) 1023))));
    int _262_x1 = java.lang.Short.toUnsignedInt((short) (short)  ((short)((_259_firstWord) & ((short) 63))));
    int _263_w = java.lang.Short.toUnsignedInt((short) dafny.Helpers.bv16ShiftRight((short) (short)  ((short)((_259_firstWord) & ((short) 960))), (byte) 6));
    int _264_u = ((int) (((int)  ((_263_w) + (1))) & 0xFFFFFF));
    int _265_v = (int)  (((int)  (((int) (((int)  ((_264_u) << ((byte) 16))) & 0xFFFFFF)) | ((int) (((int)  ((_262_x1) << ((byte) 10))) & 0xFFFFFF)))) | ((_261_x2)));
    return _265_v;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> PartitionCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Short> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>Default(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
    if ((s).equals(dafny.DafnySequence.<java.lang.Short> empty(dafny.TypeDescriptor.SHORT))) {
      maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
      return maybeParts;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _266_result;
    _266_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> empty(MinimalWellFormedCodeUnitSeq._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Short> _267_rest;
    _267_rest = s;
    while ((java.math.BigInteger.valueOf((_267_rest).length())).signum() == 1) {
      dafny.DafnySequence<? extends java.lang.Short> _268_prefix;
      Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Short>> _269_valueOrError0 = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>Default(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _269_valueOrError0 = __default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_267_rest);
      if ((_269_valueOrError0).IsFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor())) {
        maybeParts = (_269_valueOrError0).<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>PropagateFailure(MinimalWellFormedCodeUnitSeq._typeDescriptor(), dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()));
        return maybeParts;
      }
      _268_prefix = (_269_valueOrError0).Extract(MinimalWellFormedCodeUnitSeq._typeDescriptor());
      _266_result = dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>concatenate(_266_result, dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>> of(MinimalWellFormedCodeUnitSeq._typeDescriptor(), _268_prefix));
      _267_rest = (_267_rest).drop(java.math.BigInteger.valueOf((_268_prefix).length()));
    }
    maybeParts = Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>>create_Some(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Short>>_typeDescriptor(MinimalWellFormedCodeUnitSeq._typeDescriptor()), _266_result);
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
      for (java.math.BigInteger _270_i = java.math.BigInteger.valueOf((vs).length()); _lo1.compareTo(_270_i) < 0; ) {
        _270_i = _270_i.subtract(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends java.lang.Short> _271_next;
        _271_next = __default.EncodeScalarValue(((int)(java.lang.Object)((vs).select(dafny.Helpers.toInt((_270_i))))));
        s = dafny.DafnySequence.<java.lang.Short>concatenate(_271_next, s);
      }
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Integer> DecodeCodeUnitSequence(dafny.DafnySequence<? extends java.lang.Short> s) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _272_parts = __default.PartitionCodeUnitSequence(s);
    dafny.DafnySequence<? extends java.lang.Integer> _273_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Short>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _272_parts);
    return _273_vs;
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> DecodeCodeUnitSequenceChecked(dafny.DafnySequence<? extends java.lang.Short> s)
  {
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>Default(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
    Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>>> _274_maybeParts;
    _274_maybeParts = __default.PartitionCodeUnitSequenceChecked(s);
    if ((_274_maybeParts).is_None()) {
      maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_None(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      return maybeVs;
    }
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Short>> _275_parts;
    _275_parts = (_274_maybeParts).dtor_value();
    dafny.DafnySequence<? extends java.lang.Integer> _276_vs;
    _276_vs = Std.Collections.Seq.__default.<dafny.DafnySequence<? extends java.lang.Short>, java.lang.Integer>Map(MinimalWellFormedCodeUnitSeq._typeDescriptor(), Std.Unicode.Base.ScalarValue._typeDescriptor(), __default::DecodeMinimalWellFormedCodeUnitSubsequence, _275_parts);
    maybeVs = Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Integer>>create_Some(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), _276_vs);
    return maybeVs;
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Utf16EncodingForm._default";
  }
}
