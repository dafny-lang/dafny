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
    dafny.DafnySequence<? extends java.lang.Integer> _277_asCodeUnits = Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Integer>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.Unicode.Base.ScalarValue._typeDescriptor(), (dafny.CodePoint _eta0) -> __default.CharAsUnicodeScalarValue(((dafny.CodePoint)(_eta0)).value()), s);
    dafny.DafnySequence<? extends java.lang.Byte> _278_asUtf8CodeUnits = Std.Unicode.Utf8EncodingForm.__default.EncodeScalarSequence(_277_asCodeUnits);
    dafny.DafnySequence<? extends java.lang.Byte> _279_asBytes = Std.Collections.Seq.__default.<java.lang.Byte, java.lang.Byte>Map(dafny.TypeDescriptor.BYTE, Std.BoundedInts.uint8._typeDescriptor(), ((java.util.function.Function<java.lang.Byte, java.lang.Byte>)(_280_cu_boxed0) -> {
      byte _280_cu = ((byte)(java.lang.Object)(_280_cu_boxed0));
      return (_280_cu);
    }), _278_asUtf8CodeUnits);
    return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), _279_asBytes);
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> FromUTF8Checked(dafny.DafnySequence<? extends java.lang.Byte> bs) {
    dafny.DafnySequence<? extends java.lang.Byte> _281_asCodeUnits = Std.Collections.Seq.__default.<java.lang.Byte, java.lang.Byte>Map(Std.BoundedInts.uint8._typeDescriptor(), dafny.TypeDescriptor.BYTE, ((java.util.function.Function<java.lang.Byte, java.lang.Byte>)(_282_c_boxed0) -> {
      byte _282_c = ((byte)(java.lang.Object)(_282_c_boxed0));
      return (_282_c);
    }), bs);
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> _283_valueOrError0 = Std.Unicode.Utf8EncodingForm.__default.DecodeCodeUnitSequenceChecked(_281_asCodeUnits);
    if ((_283_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()))) {
      return (_283_valueOrError0).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
    } else {
      dafny.DafnySequence<? extends java.lang.Integer> _284_utf32 = (_283_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      dafny.DafnySequence<? extends dafny.CodePoint> _285_asChars = Std.Collections.Seq.__default.<java.lang.Integer, dafny.CodePoint>Map(Std.Unicode.Base.ScalarValue._typeDescriptor(), dafny.TypeDescriptor.UNICODE_CHAR, (java.lang.Integer _eta1) -> dafny.CodePoint.valueOf(__default.CharFromUnicodeScalarValue(((int)(java.lang.Object)(_eta1)))), _284_utf32);
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _285_asChars);
    }
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Short>> ToUTF16Checked(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    dafny.DafnySequence<? extends java.lang.Integer> _286_asCodeUnits = Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Integer>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.Unicode.Base.ScalarValue._typeDescriptor(), (dafny.CodePoint _eta2) -> __default.CharAsUnicodeScalarValue(((dafny.CodePoint)(_eta2)).value()), s);
    dafny.DafnySequence<? extends java.lang.Short> _287_asUtf16CodeUnits = Std.Unicode.Utf16EncodingForm.__default.EncodeScalarSequence(_286_asCodeUnits);
    dafny.DafnySequence<? extends java.lang.Short> _288_asBytes = Std.Collections.Seq.__default.<java.lang.Short, java.lang.Short>Map(dafny.TypeDescriptor.SHORT, Std.BoundedInts.uint16._typeDescriptor(), ((java.util.function.Function<java.lang.Short, java.lang.Short>)(_289_cu_boxed0) -> {
      short _289_cu = ((short)(java.lang.Object)(_289_cu_boxed0));
      return (_289_cu);
    }), _287_asUtf16CodeUnits);
    return Std.Wrappers.Option.<dafny.DafnySequence<? extends java.lang.Short>>create_Some(dafny.DafnySequence.<java.lang.Short>_typeDescriptor(Std.BoundedInts.uint16._typeDescriptor()), _288_asBytes);
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> FromUTF16Checked(dafny.DafnySequence<? extends java.lang.Short> bs) {
    dafny.DafnySequence<? extends java.lang.Short> _290_asCodeUnits = Std.Collections.Seq.__default.<java.lang.Short, java.lang.Short>Map(Std.BoundedInts.uint16._typeDescriptor(), dafny.TypeDescriptor.SHORT, ((java.util.function.Function<java.lang.Short, java.lang.Short>)(_291_c_boxed0) -> {
      short _291_c = ((short)(java.lang.Object)(_291_c_boxed0));
      return (_291_c);
    }), bs);
    Std.Wrappers.Option<dafny.DafnySequence<? extends java.lang.Integer>> _292_valueOrError0 = Std.Unicode.Utf16EncodingForm.__default.DecodeCodeUnitSequenceChecked(_290_asCodeUnits);
    if ((_292_valueOrError0).IsFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()))) {
      return (_292_valueOrError0).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
    } else {
      dafny.DafnySequence<? extends java.lang.Integer> _293_utf32 = (_292_valueOrError0).Extract(dafny.DafnySequence.<java.lang.Integer>_typeDescriptor(Std.Unicode.Base.ScalarValue._typeDescriptor()));
      dafny.DafnySequence<? extends dafny.CodePoint> _294_asChars = Std.Collections.Seq.__default.<java.lang.Integer, dafny.CodePoint>Map(Std.Unicode.Base.ScalarValue._typeDescriptor(), dafny.TypeDescriptor.UNICODE_CHAR, (java.lang.Integer _eta3) -> dafny.CodePoint.valueOf(__default.CharFromUnicodeScalarValue(((int)(java.lang.Object)(_eta3)))), _293_utf32);
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _294_asChars);
    }
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> ASCIIToUTF8(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Byte>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.BoundedInts.uint8._typeDescriptor(), ((java.util.function.Function<dafny.CodePoint, java.lang.Byte>)(_295_c_boxed0) -> {
      int _295_c = ((dafny.CodePoint)(_295_c_boxed0)).value();
      return ((byte) (_295_c));
    }), s);
  }
  public static dafny.DafnySequence<? extends java.lang.Short> ASCIIToUTF16(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return Std.Collections.Seq.__default.<dafny.CodePoint, java.lang.Short>Map(dafny.TypeDescriptor.UNICODE_CHAR, Std.BoundedInts.uint16._typeDescriptor(), ((java.util.function.Function<dafny.CodePoint, java.lang.Short>)(_296_c_boxed0) -> {
      int _296_c = ((dafny.CodePoint)(_296_c_boxed0)).value();
      return ((short) (_296_c));
    }), s);
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.UnicodeStringsWithUnicodeChar._default";
  }
}
