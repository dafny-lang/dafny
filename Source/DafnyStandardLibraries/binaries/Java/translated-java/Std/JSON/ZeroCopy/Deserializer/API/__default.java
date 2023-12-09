// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.API;

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
import Std.JSON.Errors.*;
import Std.JSON.Spec.*;
import Std.JSON.Utils.Views.Core.*;
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;
import Std.JSON.Utils.Lexers.Strings.*;
import Std.JSON.Utils.Cursors.*;
import Std.JSON.Utils.Parsers.*;
import Std.JSON.Grammar.*;
import Std.JSON.ByteStrConversion.*;
import Std.JSON.Serializer.*;
import Std.JSON.Deserializer.Uint16StrConversion.*;
import Std.JSON.Deserializer.*;
import Std.JSON.ConcreteSyntax.Spec.*;
import Std.JSON.ZeroCopy.Serializer.*;
import Std.JSON.ZeroCopy.Deserializer.Core.*;
import Std.JSON.ZeroCopy.Deserializer.Strings.*;
import Std.JSON.ZeroCopy.Deserializer.Numbers.*;
import Std.JSON.ZeroCopy.Deserializer.ObjectParams.*;
import Std.JSON.ZeroCopy.Deserializer.Objects.*;
import Std.JSON.ZeroCopy.Deserializer.ArrayParams.*;
import Std.JSON.ZeroCopy.Deserializer.Arrays.*;
import Std.JSON.ZeroCopy.Deserializer.Constants.*;
import Std.JSON.ZeroCopy.Deserializer.Values.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.JSON.Errors.DeserializationError LiftCursorError(Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError> err) {
    Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError> _source24 = err;
    if (_source24.is_EOF()) {
      return Std.JSON.Errors.DeserializationError.create_ReachedEOF();
    } else if (_source24.is_ExpectingByte()) {
      byte _779___mcc_h0 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingByte<Std.JSON.Errors.DeserializationError>)_source24)._expected;
      short _780___mcc_h1 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingByte<Std.JSON.Errors.DeserializationError>)_source24)._b;
      short _781_b = _780___mcc_h1;
      byte _782_expected = _779___mcc_h0;
      return Std.JSON.Errors.DeserializationError.create_ExpectingByte(_782_expected, _781_b);
    } else if (_source24.is_ExpectingAnyByte()) {
      dafny.DafnySequence<? extends java.lang.Byte> _783___mcc_h2 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingAnyByte<Std.JSON.Errors.DeserializationError>)_source24)._expected__sq;
      short _784___mcc_h3 = ((Std.JSON.Utils.Cursors.CursorError_ExpectingAnyByte<Std.JSON.Errors.DeserializationError>)_source24)._b;
      short _785_b = _784___mcc_h3;
      dafny.DafnySequence<? extends java.lang.Byte> _786_expected__sq = _783___mcc_h2;
      return Std.JSON.Errors.DeserializationError.create_ExpectingAnyByte(_786_expected__sq, _785_b);
    } else {
      Std.JSON.Errors.DeserializationError _787___mcc_h4 = ((Std.JSON.Utils.Cursors.CursorError_OtherError<Std.JSON.Errors.DeserializationError>)_source24)._err;
      Std.JSON.Errors.DeserializationError _788_err = _787___mcc_h4;
      return _788_err;
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>, Std.JSON.Errors.DeserializationError> JSON(Std.JSON.Utils.Cursors.Cursor__ cs) {
    return (Std.JSON.ZeroCopy.Deserializer.Core.__default.<Std.JSON.Grammar.Value>Structural(Std.JSON.Grammar.Value._typeDescriptor(), cs, Std.JSON.ZeroCopy.Deserializer.Values.__default::Value)).<Std.JSON.Errors.DeserializationError>MapFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), __default::LiftCursorError);
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.DeserializationError> Text(Std.JSON.Utils.Views.Core.View__ v) {
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>, Std.JSON.Errors.DeserializationError> _789_valueOrError0 = __default.JSON(Std.JSON.Utils.Cursors.Cursor__.OfView(v));
    if ((_789_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_789_valueOrError0).<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>> _let_tmp_rhs39 = (_789_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>_typeDescriptor(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor())), Std.JSON.Errors.DeserializationError._typeDescriptor());
      Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> _790_text = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>)_let_tmp_rhs39)._t;
      Std.JSON.Utils.Cursors.Cursor__ _791_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>)_let_tmp_rhs39)._cs;
      Std.Wrappers.OutcomeResult<Std.JSON.Errors.DeserializationError> _792_valueOrError1 = Std.Wrappers.__default.<Std.JSON.Errors.DeserializationError>Need(Std.JSON.Errors.DeserializationError._typeDescriptor(), (_791_cs).EOF_q(), Std.JSON.Errors.DeserializationError.create_ExpectingEOF());
      if ((_792_valueOrError1).IsFailure(Std.JSON.Errors.DeserializationError._typeDescriptor())) {
        return (_792_valueOrError1).<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
      } else {
        return Std.Wrappers.Result.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.DeserializationError>create_Success(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), _790_text);
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.DeserializationError> OfBytes(dafny.DafnySequence<? extends java.lang.Byte> bs) {
    Std.Wrappers.OutcomeResult<Std.JSON.Errors.DeserializationError> _793_valueOrError0 = Std.Wrappers.__default.<Std.JSON.Errors.DeserializationError>Need(Std.JSON.Errors.DeserializationError._typeDescriptor(), (java.math.BigInteger.valueOf((bs).length())).compareTo(Std.BoundedInts.__default.TWO__TO__THE__32()) < 0, Std.JSON.Errors.DeserializationError.create_IntOverflow());
    if ((_793_valueOrError0).IsFailure(Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_793_valueOrError0).<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>>PropagateFailure(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()));
    } else {
      return __default.Text(Std.JSON.Utils.Views.Core.View__.OfBytes(bs));
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Deserializer.API._default";
  }
}
