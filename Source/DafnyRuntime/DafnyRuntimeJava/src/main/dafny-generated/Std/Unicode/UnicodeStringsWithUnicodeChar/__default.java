// Class __default
// Dafny class __default compiled into Java
package Std.Unicode.UnicodeStringsWithUnicodeChar;

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
import Std.Unicode.Utf16EncodingForm.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static int CharAsUnicodeScalarValue(int c) {
    return ((int) (c));
  }
  public static int CharFromUnicodeScalarValue(int sv) {
    return (int)dafny.Helpers.toInt((dafny.Helpers.unsignedToBigInteger(sv)));
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Byte>> ToUTF8Checked(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    dafny.DafnySequence<? extends java.lang.Integer> _283_asCodeUnits = Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Integer>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.Unicode.Base.ScalarValue._typeDescriptor(), (dafny.CodePoint _eta0) -> __default.CharAsUnicodeScalarValue(((dafny.CodePoint)(_eta0)).value()), s);
    dafny.DafnySequence<? extends java.lang.Byte> _284_asUtf8CodeUnits = Std.Unicode.Utf8EncodingForm.__default.EncodeScalarSequence(_283_asCodeUnits);
    dafny.DafnySequence<? extends java.lang.Byte> _285_asBytes = Std.Collections.Seq.__default.<java.lang.Byte, java.lang.Byte>Map(dafny.TypeDescriptor.BYTE, Std.BoundedInts.uint8._typeDescriptor(), ((java.util.function.Function<java.lang.Byte, java.lang.Byte>)(_286_cu_boxed0) -> {
      byte _286_cu = ((byte)(java.lang.Object)(_286_cu_boxed0));
      return (_286_cu);
    }), _284_asUtf8CodeUnits);
    return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), _285_asBytes);
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> FromUTF8Checked(dafny.DafnySequence<? extends java.lang.Byte> bs) {
    dafny.DafnySequence<? extends java.lang.Byte> _287_asCodeUnits = Std.Collections.Seq.__default.<java.lang.Byte, java.lang.Byte>Map(Std.BoundedInts.uint8._typeDescriptor(), dafny.TypeDescriptor.BYTE, ((java.util.function.Function<java.lang.Byte, java.lang.Byte>)(_288_c_boxed0) -> {
      byte _288_c = ((byte)(java.lang.Object)(_288_c_boxed0));
      return (_288_c);
    }), bs);
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> _289_valueOrError0 = Std.Unicode.Utf8EncodingForm.__default.DecodeCodeUnitSequenceChecked(_287_asCodeUnits);
    if ((_289_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()))) {
      return (_289_valueOrError0).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
    } else {
      dafny.DafnySequence<? extends java.lang.Integer> _290_utf32 = (_289_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      dafny.DafnySequence<? extends dafny.CodePoint> _291_asChars = Std.Collections.Seq.__default.<java.lang.Integer, dafny.CodePoint>Map(Std.Unicode.Base.ScalarValue._typeDescriptor(), dafny.TypeDescriptor.UNICODE_CHAR, (java.lang.Integer _eta1) -> dafny.CodePoint.valueOf(__default.CharFromUnicodeScalarValue(((int)(java.lang.Object)(_eta1)))), _290_utf32);
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _291_asChars);
    }
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Short>> ToUTF16Checked(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    dafny.DafnySequence<? extends java.lang.Integer> _292_asCodeUnits = Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Integer>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.Unicode.Base.ScalarValue._typeDescriptor(), (dafny.CodePoint _eta2) -> __default.CharAsUnicodeScalarValue(((dafny.CodePoint)(_eta2)).value()), s);
    dafny.DafnySequence<? extends java.lang.Short> _293_asUtf16CodeUnits = Std.Unicode.Utf16EncodingForm.__default.EncodeScalarSequence(_292_asCodeUnits);
    dafny.DafnySequence<? extends java.lang.Short> _294_asBytes = Std.Collections.Seq.__default.<java.lang.Short, java.lang.Short>Map(dafny.TypeDescriptor.SHORT, Std.BoundedInts.uint16._typeDescriptor(), ((java.util.function.Function<java.lang.Short, java.lang.Short>)(_295_cu_boxed0) -> {
      short _295_cu = ((short)(java.lang.Object)(_295_cu_boxed0));
      return (_295_cu);
    }), _293_asUtf16CodeUnits);
    return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>create_Some(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), _294_asBytes);
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> FromUTF16Checked(dafny.DafnySequence<? extends java.lang.Short> bs) {
    dafny.DafnySequence<? extends java.lang.Short> _296_asCodeUnits = Std.Collections.Seq.__default.<java.lang.Short, java.lang.Short>Map(Std.BoundedInts.uint16._typeDescriptor(), dafny.TypeDescriptor.SHORT, ((java.util.function.Function<java.lang.Short, java.lang.Short>)(_297_c_boxed0) -> {
      short _297_c = ((short)(java.lang.Object)(_297_c_boxed0));
      return (_297_c);
    }), bs);
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> _298_valueOrError0 = Std.Unicode.Utf16EncodingForm.__default.DecodeCodeUnitSequenceChecked(_296_asCodeUnits);
    if ((_298_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()))) {
      return (_298_valueOrError0).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
    } else {
      dafny.DafnySequence<? extends java.lang.Integer> _299_utf32 = (_298_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      dafny.DafnySequence<? extends dafny.CodePoint> _300_asChars = Std.Collections.Seq.__default.<java.lang.Integer, dafny.CodePoint>Map(Std.Unicode.Base.ScalarValue._typeDescriptor(), dafny.TypeDescriptor.UNICODE_CHAR, (java.lang.Integer _eta3) -> dafny.CodePoint.valueOf(__default.CharFromUnicodeScalarValue(((int)(java.lang.Object)(_eta3)))), _299_utf32);
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _300_asChars);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> ASCIIToUTF8(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Byte>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.BoundedInts.uint8._typeDescriptor(), ((java.util.function.Function<dafny.CodePoint, java.lang.Byte>)(_301_c_boxed0) -> {
      int _301_c = ((dafny.CodePoint)(_301_c_boxed0)).value();
      return ((byte) (_301_c));
    }), s);
  }
  public static dafny.DafnySequence<? extends java.lang.Short> ASCIIToUTF16(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Short>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.BoundedInts.uint16._typeDescriptor(), ((java.util.function.Function<dafny.CodePoint, java.lang.Short>)(_302_c_boxed0) -> {
      int _302_c = ((dafny.CodePoint)(_302_c_boxed0)).value();
      return ((short) (_302_c));
    }), s);
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.UnicodeStringsWithUnicodeChar._default";
  }
}
