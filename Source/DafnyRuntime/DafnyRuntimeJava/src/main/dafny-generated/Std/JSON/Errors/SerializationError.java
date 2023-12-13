// Class SerializationError
// Dafny class SerializationError compiled into Java
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
public abstract class SerializationError {
  public SerializationError() {
  }

  private static final SerializationError theDefault = Std.JSON.Errors.SerializationError.create_OutOfMemory();
  public static SerializationError Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<SerializationError> _TYPE = dafny.TypeDescriptor.<SerializationError>referenceWithInitializer(SerializationError.class, () -> SerializationError.Default());
  public static dafny.TypeDescriptor<SerializationError> _typeDescriptor() {
    return (dafny.TypeDescriptor<SerializationError>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static SerializationError create_OutOfMemory() {
    return new SerializationError_OutOfMemory();
  }
  public static SerializationError create_IntTooLarge(java.math.BigInteger i) {
    return new SerializationError_IntTooLarge(i);
  }
  public static SerializationError create_StringTooLong(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return new SerializationError_StringTooLong(s);
  }
  public static SerializationError create_InvalidUnicode() {
    return new SerializationError_InvalidUnicode();
  }
  public boolean is_OutOfMemory() { return this instanceof SerializationError_OutOfMemory; }
  public boolean is_IntTooLarge() { return this instanceof SerializationError_IntTooLarge; }
  public boolean is_StringTooLong() { return this instanceof SerializationError_StringTooLong; }
  public boolean is_InvalidUnicode() { return this instanceof SerializationError_InvalidUnicode; }
  public java.math.BigInteger dtor_i() {
    SerializationError d = this;
    return ((SerializationError_IntTooLarge)d)._i;
  }
  public dafny.DafnySequence<? extends dafny.CodePoint> dtor_s() {
    SerializationError d = this;
    return ((SerializationError_StringTooLong)d)._s;
  }
  public dafny.DafnySequence<? extends dafny.CodePoint> ToString() {
    SerializationError _source11 = this;
    if (_source11.is_OutOfMemory()) {
      return dafny.DafnySequence.asUnicodeString("Out of memory");
    } else if (_source11.is_IntTooLarge()) {
      java.math.BigInteger _320___mcc_h0 = ((Std.JSON.Errors.SerializationError_IntTooLarge)_source11)._i;
      java.math.BigInteger _321_i = _320___mcc_h0;
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("Integer too large: "), Std.Strings.__default.OfInt(_321_i));
    } else if (_source11.is_StringTooLong()) {
      dafny.DafnySequence<? extends dafny.CodePoint> _322___mcc_h1 = ((Std.JSON.Errors.SerializationError_StringTooLong)_source11)._s;
      dafny.DafnySequence<? extends dafny.CodePoint> _323_s = _322___mcc_h1;
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("String too long: "), _323_s);
    } else {
      return dafny.DafnySequence.asUnicodeString("Invalid Unicode sequence");
    }
  }
}
