// Class DeserializationError
// Dafny class DeserializationError compiled into Java
package Std.JSON.Errors;

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
import Std.Unicode.UnicodeStringsWithUnicodeChar.*;
import Std.Unicode.Utf8EncodingScheme.*;
import Std.JSON.Values.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class DeserializationError {
  public DeserializationError() {
  }

  private static final DeserializationError theDefault = Std.JSON.Errors.DeserializationError.create_UnterminatedSequence();
  public static DeserializationError Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<DeserializationError> _TYPE = dafny.TypeDescriptor.<DeserializationError>referenceWithInitializer(DeserializationError.class, () -> DeserializationError.Default());
  public static dafny.TypeDescriptor<DeserializationError> _typeDescriptor() {
    return (dafny.TypeDescriptor<DeserializationError>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static DeserializationError create_UnterminatedSequence() {
    return new DeserializationError_UnterminatedSequence();
  }
  public static DeserializationError create_UnsupportedEscape(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    return new DeserializationError_UnsupportedEscape(str);
  }
  public static DeserializationError create_EscapeAtEOS() {
    return new DeserializationError_EscapeAtEOS();
  }
  public static DeserializationError create_EmptyNumber() {
    return new DeserializationError_EmptyNumber();
  }
  public static DeserializationError create_ExpectingEOF() {
    return new DeserializationError_ExpectingEOF();
  }
  public static DeserializationError create_IntOverflow() {
    return new DeserializationError_IntOverflow();
  }
  public static DeserializationError create_ReachedEOF() {
    return new DeserializationError_ReachedEOF();
  }
  public static DeserializationError create_ExpectingByte(byte expected, short b) {
    return new DeserializationError_ExpectingByte(expected, b);
  }
  public static DeserializationError create_ExpectingAnyByte(dafny.DafnySequence<? extends java.lang.Byte> expected__sq, short b) {
    return new DeserializationError_ExpectingAnyByte(expected__sq, b);
  }
  public static DeserializationError create_InvalidUnicode() {
    return new DeserializationError_InvalidUnicode();
  }
  public boolean is_UnterminatedSequence() { return this instanceof DeserializationError_UnterminatedSequence; }
  public boolean is_UnsupportedEscape() { return this instanceof DeserializationError_UnsupportedEscape; }
  public boolean is_EscapeAtEOS() { return this instanceof DeserializationError_EscapeAtEOS; }
  public boolean is_EmptyNumber() { return this instanceof DeserializationError_EmptyNumber; }
  public boolean is_ExpectingEOF() { return this instanceof DeserializationError_ExpectingEOF; }
  public boolean is_IntOverflow() { return this instanceof DeserializationError_IntOverflow; }
  public boolean is_ReachedEOF() { return this instanceof DeserializationError_ReachedEOF; }
  public boolean is_ExpectingByte() { return this instanceof DeserializationError_ExpectingByte; }
  public boolean is_ExpectingAnyByte() { return this instanceof DeserializationError_ExpectingAnyByte; }
  public boolean is_InvalidUnicode() { return this instanceof DeserializationError_InvalidUnicode; }
  public dafny.DafnySequence<? extends dafny.CodePoint> dtor_str() {
    DeserializationError d = this;
    return ((DeserializationError_UnsupportedEscape)d)._str;
  }
  public byte dtor_expected() {
    DeserializationError d = this;
    return ((DeserializationError_ExpectingByte)d)._expected;
  }
  public short dtor_b() {
    DeserializationError d = this;
    if (d instanceof DeserializationError_ExpectingByte) { return ((DeserializationError_ExpectingByte)d)._b; }
    return ((DeserializationError_ExpectingAnyByte)d)._b;
  }
  public dafny.DafnySequence<? extends java.lang.Byte> dtor_expected__sq() {
    DeserializationError d = this;
    return ((DeserializationError_ExpectingAnyByte)d)._expected__sq;
  }
  public dafny.DafnySequence<? extends dafny.CodePoint> ToString() {
    DeserializationError _source10 = this;
    if (_source10.is_UnterminatedSequence()) {
      return dafny.DafnySequence.asUnicodeString("Unterminated sequence");
    } else if (_source10.is_UnsupportedEscape()) {
      dafny.DafnySequence<? extends dafny.CodePoint> _299___mcc_h0 = ((Std.JSON.Errors.DeserializationError_UnsupportedEscape)_source10)._str;
      dafny.DafnySequence<? extends dafny.CodePoint> _300_str = _299___mcc_h0;
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("Unsupported escape sequence: "), _300_str);
    } else if (_source10.is_EscapeAtEOS()) {
      return dafny.DafnySequence.asUnicodeString("Escape character at end of string");
    } else if (_source10.is_EmptyNumber()) {
      return dafny.DafnySequence.asUnicodeString("Number must contain at least one digit");
    } else if (_source10.is_ExpectingEOF()) {
      return dafny.DafnySequence.asUnicodeString("Expecting EOF");
    } else if (_source10.is_IntOverflow()) {
      return dafny.DafnySequence.asUnicodeString("Input length does not fit in a 32-bit counter");
    } else if (_source10.is_ReachedEOF()) {
      return dafny.DafnySequence.asUnicodeString("Reached EOF");
    } else if (_source10.is_ExpectingByte()) {
      byte _301___mcc_h1 = ((Std.JSON.Errors.DeserializationError_ExpectingByte)_source10)._expected;
      short _302___mcc_h2 = ((Std.JSON.Errors.DeserializationError_ExpectingByte)_source10)._b;
      short _303_b = _302___mcc_h2;
      byte _304_b0 = _301___mcc_h1;
      dafny.DafnySequence<? extends dafny.CodePoint> _305_c = ((java.lang.Integer.signum((_303_b)) == 1) ? (dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("'"), dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf((int)dafny.Helpers.toInt(_303_b)))), dafny.DafnySequence.asUnicodeString("'"))) : (dafny.DafnySequence.asUnicodeString("EOF")));
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("Expecting '"), dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf((int)java.lang.Byte.toUnsignedInt(_304_b0)))), dafny.DafnySequence.asUnicodeString("', read ")), _305_c);
    } else if (_source10.is_ExpectingAnyByte()) {
      dafny.DafnySequence<? extends java.lang.Byte> _306___mcc_h3 = ((Std.JSON.Errors.DeserializationError_ExpectingAnyByte)_source10)._expected__sq;
      short _307___mcc_h4 = ((Std.JSON.Errors.DeserializationError_ExpectingAnyByte)_source10)._b;
      short _308_b = _307___mcc_h4;
      dafny.DafnySequence<? extends java.lang.Byte> _309_bs0 = _306___mcc_h3;
      dafny.DafnySequence<? extends dafny.CodePoint> _310_c = ((java.lang.Integer.signum((_308_b)) == 1) ? (dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("'"), dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf((int)dafny.Helpers.toInt(_308_b)))), dafny.DafnySequence.asUnicodeString("'"))) : (dafny.DafnySequence.asUnicodeString("EOF")));
      dafny.DafnySequence<? extends dafny.CodePoint> _311_c0s = dafny.DafnySequence.Create(dafny.TypeDescriptor.UNICODE_CHAR, java.math.BigInteger.valueOf((_309_bs0).length()), ((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Byte>, java.util.function.Function<java.math.BigInteger, dafny.CodePoint>>)(_312_bs0) -> ((java.util.function.Function<java.math.BigInteger, dafny.CodePoint>)(_313_idx_boxed0) -> {
        java.math.BigInteger _313_idx = ((java.math.BigInteger)(java.lang.Object)(_313_idx_boxed0));
        return dafny.CodePoint.valueOf((int)java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((_312_bs0).select(dafny.Helpers.toInt((_313_idx)))))));
      })).apply(_309_bs0));
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("Expecting one of '"), _311_c0s), dafny.DafnySequence.asUnicodeString("', read ")), _310_c);
    } else {
      return dafny.DafnySequence.asUnicodeString("Invalid Unicode sequence");
    }
  }
}
