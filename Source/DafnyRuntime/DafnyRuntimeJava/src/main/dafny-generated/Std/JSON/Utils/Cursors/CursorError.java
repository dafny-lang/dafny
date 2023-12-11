// Class CursorError<R>
// Dafny class CursorError<R> compiled into Java
package Std.JSON.Utils.Cursors;

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
import Std.JavaFileIOInternalExterns.*;
import Std.JSON.Values.*;
import Std.JSON.Errors.*;
import Std.JSON.Spec.*;
import Std.JSON.Utils.Views.Core.*;
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;
import Std.JSON.Utils.Lexers.Strings.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class CursorError<R> {
  protected dafny.TypeDescriptor<R> _td_R;
  public CursorError(dafny.TypeDescriptor<R> _td_R) {
    this._td_R = _td_R;
  }

  public static <R> CursorError<R> Default(dafny.TypeDescriptor<R> _td_R) {
    return Std.JSON.Utils.Cursors.CursorError.<R>create_EOF(_td_R);
  }
  public static <R> dafny.TypeDescriptor<CursorError<R>> _typeDescriptor(dafny.TypeDescriptor<R> _td_R) {
    return (dafny.TypeDescriptor<CursorError<R>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<CursorError<R>>referenceWithInitializer(CursorError.class, () -> CursorError.<R>Default(_td_R));
  }
  public static <R> CursorError<R> create_EOF(dafny.TypeDescriptor<R> _td_R) {
    return new CursorError_EOF<R>(_td_R);
  }
  public static <R> CursorError<R> create_ExpectingByte(dafny.TypeDescriptor<R> _td_R, byte expected, short b) {
    return new CursorError_ExpectingByte<R>(_td_R, expected, b);
  }
  public static <R> CursorError<R> create_ExpectingAnyByte(dafny.TypeDescriptor<R> _td_R, dafny.DafnySequence<? extends java.lang.Byte> expected__sq, short b) {
    return new CursorError_ExpectingAnyByte<R>(_td_R, expected__sq, b);
  }
  public static <R> CursorError<R> create_OtherError(dafny.TypeDescriptor<R> _td_R, R err) {
    return new CursorError_OtherError<R>(_td_R, err);
  }
  public boolean is_EOF() { return this instanceof CursorError_EOF; }
  public boolean is_ExpectingByte() { return this instanceof CursorError_ExpectingByte; }
  public boolean is_ExpectingAnyByte() { return this instanceof CursorError_ExpectingAnyByte; }
  public boolean is_OtherError() { return this instanceof CursorError_OtherError; }
  public byte dtor_expected() {
    CursorError<R> d = this;
    return ((CursorError_ExpectingByte<R>)d)._expected;
  }
  public short dtor_b() {
    CursorError<R> d = this;
    if (d instanceof CursorError_ExpectingByte) { return ((CursorError_ExpectingByte<R>)d)._b; }
    return ((CursorError_ExpectingAnyByte<R>)d)._b;
  }
  public dafny.DafnySequence<? extends java.lang.Byte> dtor_expected__sq() {
    CursorError<R> d = this;
    return ((CursorError_ExpectingAnyByte<R>)d)._expected__sq;
  }
  public R dtor_err() {
    CursorError<R> d = this;
    return ((CursorError_OtherError<R>)d)._err;
  }
  public dafny.DafnySequence<? extends dafny.CodePoint> ToString(dafny.TypeDescriptor<R> _td_R, java.util.function.Function<R, dafny.DafnySequence<? extends dafny.CodePoint>> pr)
  {
    CursorError<R> _source14 = this;
    if (_source14.is_EOF()) {
      return dafny.DafnySequence.asUnicodeString("Reached EOF");
    } else if (_source14.is_ExpectingByte()) {
      byte _374___mcc_h0 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingByte<R>)_source14)._expected;
      short _375___mcc_h1 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingByte<R>)_source14)._b;
      short _376_b = _375___mcc_h1;
      byte _377_b0 = _374___mcc_h0;
      dafny.DafnySequence<? extends dafny.CodePoint> _378_c = ((java.lang.Integer.signum((_376_b)) == 1) ? (dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("'"), dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf((int)dafny.Helpers.toInt(_376_b)))), dafny.DafnySequence.asUnicodeString("'"))) : (dafny.DafnySequence.asUnicodeString("EOF")));
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("Expecting '"), dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf((int)java.lang.Byte.toUnsignedInt(_377_b0)))), dafny.DafnySequence.asUnicodeString("', read ")), _378_c);
    } else if (_source14.is_ExpectingAnyByte()) {
      dafny.DafnySequence<? extends java.lang.Byte> _379___mcc_h2 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingAnyByte<R>)_source14)._expected__sq;
      short _380___mcc_h3 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingAnyByte<R>)_source14)._b;
      short _381_b = _380___mcc_h3;
      dafny.DafnySequence<? extends java.lang.Byte> _382_bs0 = _379___mcc_h2;
      dafny.DafnySequence<? extends dafny.CodePoint> _383_c = ((java.lang.Integer.signum((_381_b)) == 1) ? (dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("'"), dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf((int)dafny.Helpers.toInt(_381_b)))), dafny.DafnySequence.asUnicodeString("'"))) : (dafny.DafnySequence.asUnicodeString("EOF")));
      dafny.DafnySequence<? extends dafny.CodePoint> _384_c0s = dafny.DafnySequence.Create(dafny.TypeDescriptor.UNICODE_CHAR, java.math.BigInteger.valueOf((_382_bs0).length()), ((java.util.function.Function<dafny.DafnySequence<? extends java.lang.Byte>, java.util.function.Function<java.math.BigInteger, dafny.CodePoint>>)(_385_bs0) -> ((java.util.function.Function<java.math.BigInteger, dafny.CodePoint>)(_386_idx_boxed0) -> {
        java.math.BigInteger _386_idx = ((java.math.BigInteger)(java.lang.Object)(_386_idx_boxed0));
        return dafny.CodePoint.valueOf((int)java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)((_385_bs0).select(dafny.Helpers.toInt((_386_idx)))))));
      })).apply(_382_bs0));
      return dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.asUnicodeString("Expecting one of '"), _384_c0s), dafny.DafnySequence.asUnicodeString("', read ")), _383_c);
    } else {
      R _387___mcc_h4 = ((Std.JSON.Utils.Cursors.CursorError_OtherError<R>)_source14)._err;
      R _388_err = _387___mcc_h4;
      return ((dafny.DafnySequence<? extends dafny.CodePoint>)(java.lang.Object)((pr).apply(_388_err)));
    }
  }
}
