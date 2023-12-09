// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Numbers;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> Digits(Std.JSON.Utils.Cursors.Cursor__ cs) {
    return ((cs).SkipWhile(Std.JSON.Grammar.__default::Digit_q)).Split();
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> NonEmptyDigits(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _649_sp = __default.Digits(cs);
    if (((_649_sp).dtor_t()).Empty_q()) {
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Failure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jdigits._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>create_OtherError(Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Errors.DeserializationError.create_EmptyNumber()));
    } else {
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jdigits._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _649_sp);
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> NonZeroInt(Std.JSON.Utils.Cursors.Cursor__ cs) {
    return __default.NonEmptyDigits(cs);
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> OptionalMinus(Std.JSON.Utils.Cursors.Cursor__ cs) {
    return ((cs).SkipIf(((java.util.function.Function<java.lang.Byte, Boolean>)(_650_c_boxed0) -> {
      byte _650_c = ((byte)(java.lang.Object)(_650_c_boxed0));
      return (_650_c) == (((byte) ('-')));
    }))).Split();
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> OptionalSign(Std.JSON.Utils.Cursors.Cursor__ cs) {
    return ((cs).SkipIf(((java.util.function.Function<java.lang.Byte, Boolean>)(_651_c_boxed0) -> {
      byte _651_c = ((byte)(java.lang.Object)(_651_c_boxed0));
      return ((_651_c) == (((byte) ('-')))) || ((_651_c) == (((byte) ('+'))));
    }))).Split();
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> TrimmedInt(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _652_sp = ((cs).SkipIf(((java.util.function.Function<java.lang.Byte, Boolean>)(_653_c_boxed0) -> {
      byte _653_c = ((byte)(java.lang.Object)(_653_c_boxed0));
      return (_653_c) == (((byte) ('0')));
    }))).Split();
    if (((_652_sp).dtor_t()).Empty_q()) {
      return __default.NonZeroInt((_652_sp).dtor_cs());
    } else {
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Utils.Views.Core.View._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), _652_sp);
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Exp(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs27 = ((cs).SkipIf(((java.util.function.Function<java.lang.Byte, Boolean>)(_654_c_boxed0) -> {
      byte _654_c = ((byte)(java.lang.Object)(_654_c_boxed0));
      return ((_654_c) == (((byte) ('e')))) || ((_654_c) == (((byte) ('E'))));
    }))).Split();
    Std.JSON.Utils.Views.Core.View__ _655_e = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs27)._t;
    Std.JSON.Utils.Cursors.Cursor__ _656_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs27)._cs;
    if ((_655_e).Empty_q()) {
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>create(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>create_Empty(Std.JSON.Grammar.jexp._typeDescriptor()), _656_cs));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs28 = __default.OptionalSign(_656_cs);
      Std.JSON.Utils.Views.Core.View__ _657_sign = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs28)._t;
      Std.JSON.Utils.Cursors.Cursor__ _658_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs28)._cs;
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _659_valueOrError0 = __default.NonEmptyDigits(_658_cs);
      if ((_659_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jnum._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_659_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jnum._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor())));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs29 = (_659_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jnum._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Utils.Views.Core.View__ _660_num = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs29)._t;
        Std.JSON.Utils.Cursors.Cursor__ _661_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs29)._cs;
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>create(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor()), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>create_NonEmpty(Std.JSON.Grammar.jexp._typeDescriptor(), Std.JSON.Grammar.jexp.create(_655_e, _657_sign, _660_num)), _661_cs));
      }
    }
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Frac(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs30 = ((cs).SkipIf(((java.util.function.Function<java.lang.Byte, Boolean>)(_662_c_boxed0) -> {
      byte _662_c = ((byte)(java.lang.Object)(_662_c_boxed0));
      return (_662_c) == (((byte) ('.')));
    }))).Split();
    Std.JSON.Utils.Views.Core.View__ _663_period = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs30)._t;
    Std.JSON.Utils.Cursors.Cursor__ _664_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs30)._cs;
    if ((_663_period).Empty_q()) {
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>create(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor()), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>create_Empty(Std.JSON.Grammar.jfrac._typeDescriptor()), _664_cs));
    } else {
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _665_valueOrError0 = __default.NonEmptyDigits(_664_cs);
      if ((_665_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jnum._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_665_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jnum._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor())));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _let_tmp_rhs31 = (_665_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jnum._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.JSON.Utils.Views.Core.View__ _666_num = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs31)._t;
        Std.JSON.Utils.Cursors.Cursor__ _667_cs = ((Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>)_let_tmp_rhs31)._cs;
        return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>create(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor()), Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>create_NonEmpty(Std.JSON.Grammar.jfrac._typeDescriptor(), Std.JSON.Grammar.jfrac.create(_663_period, _666_num)), _667_cs));
      }
    }
  }
  public static Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber> NumberFromParts(Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> minus, Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> num, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>> frac, Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>> exp)
  {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber> _668_sp = Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>create(Std.JSON.Grammar.jnumber._typeDescriptor(), Std.JSON.Grammar.jnumber.create((minus).dtor_t(), (num).dtor_t(), (frac).dtor_t(), (exp).dtor_t()), (exp).dtor_cs());
    return _668_sp;
  }
  public static Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> Number(Std.JSON.Utils.Cursors.Cursor__ cs) {
    Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _669_minus = __default.OptionalMinus(cs);
    Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _670_valueOrError0 = __default.TrimmedInt((_669_minus).dtor_cs());
    if ((_670_valueOrError0).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jint._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
      return (_670_valueOrError0).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jint._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>_typeDescriptor(Std.JSON.Grammar.jnumber._typeDescriptor()));
    } else {
      Std.JSON.Utils.Cursors.Split<Std.JSON.Utils.Views.Core.View__> _671_num = (_670_valueOrError0).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>_typeDescriptor(Std.JSON.Grammar.jint._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
      Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _672_valueOrError1 = __default.Frac((_671_num).dtor_cs());
      if ((_672_valueOrError1).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
        return (_672_valueOrError1).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>_typeDescriptor(Std.JSON.Grammar.jnumber._typeDescriptor()));
      } else {
        Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>> _673_frac = (_672_valueOrError1).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jfrac>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jfrac>_typeDescriptor(Std.JSON.Grammar.jfrac._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
        Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>> _674_valueOrError2 = __default.Exp((_673_frac).dtor_cs());
        if ((_674_valueOrError2).IsFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()))) {
          return (_674_valueOrError2).<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>>PropagateFailure(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>_typeDescriptor(Std.JSON.Grammar.jnumber._typeDescriptor()));
        } else {
          Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>> _675_exp = (_674_valueOrError2).Extract(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.Maybe<Std.JSON.Grammar.jexp>>_typeDescriptor(Std.JSON.Grammar.Maybe.<Std.JSON.Grammar.jexp>_typeDescriptor(Std.JSON.Grammar.jexp._typeDescriptor())), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()));
          return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<Std.JSON.Grammar.jnumber>, Std.JSON.Utils.Cursors.CursorError<Std.JSON.Errors.DeserializationError>>create_Success(Std.JSON.Utils.Cursors.Split.<Std.JSON.Grammar.jnumber>_typeDescriptor(Std.JSON.Grammar.jnumber._typeDescriptor()), Std.JSON.Utils.Cursors.CursorError.<Std.JSON.Errors.DeserializationError>_typeDescriptor(Std.JSON.Errors.DeserializationError._typeDescriptor()), __default.NumberFromParts(_669_minus, _671_num, _673_frac, _675_exp));
        }
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Deserializer.Numbers._default";
  }
}
