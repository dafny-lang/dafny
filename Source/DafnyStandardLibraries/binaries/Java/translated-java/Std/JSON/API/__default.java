// Class __default
// Dafny class __default compiled into Java
package Std.JSON.API;

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
import Std.JSON.ZeroCopy.Deserializer.API.*;
import Std.JSON.ZeroCopy.API.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> Serialize(Std.JSON.Values.JSON js) {
    Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError> _794_valueOrError0 = Std.JSON.Serializer.__default.JSON(js);
    if ((_794_valueOrError0).IsFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
      return (_794_valueOrError0).<dafny.DafnySequence<? extends java.lang.Byte>>PropagateFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()));
    } else {
      Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> _795_js = (_794_valueOrError0).Extract(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      return Std.JSON.ZeroCopy.API.__default.Serialize(_795_js);
    }
  }
  public static Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> SerializeAlloc(Std.JSON.Values.JSON js)
  {
    Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> bs = Std.Wrappers.Result.<byte[], Std.JSON.Errors.SerializationError>Default(dafny.TypeDescriptor.BYTE_ARRAY, Std.JSON.Errors.SerializationError._typeDescriptor(), new byte[0]);
    if(true) {
      Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> _796_js;
      Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError> _797_valueOrError0 = Std.Wrappers.Result.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError>Default(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>Default(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.Value.Default()));
      _797_valueOrError0 = Std.JSON.Serializer.__default.JSON(js);
      if ((_797_valueOrError0).IsFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        bs = (_797_valueOrError0).<byte[]>PropagateFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.TypeDescriptor.BYTE_ARRAY);
        return bs;
      }
      _796_js = (_797_valueOrError0).Extract(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> _out11;
      _out11 = Std.JSON.ZeroCopy.API.__default.SerializeAlloc(_796_js);
      bs = _out11;
    }
    return bs;
  }
  public static Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> SerializeInto(Std.JSON.Values.JSON js, byte[] bs)
  {
    Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> len = Std.Wrappers.Result.<java.lang.Integer, Std.JSON.Errors.SerializationError>Default(Std.BoundedInts.uint32._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), 0);
    if(true) {
      Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> _798_js;
      Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError> _799_valueOrError0 = Std.Wrappers.Result.<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.SerializationError>Default(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>Default(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Grammar.Value.Default()));
      _799_valueOrError0 = Std.JSON.Serializer.__default.JSON(js);
      if ((_799_valueOrError0).IsFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor())) {
        len = (_799_valueOrError0).<java.lang.Integer>PropagateFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), Std.BoundedInts.uint32._typeDescriptor());
        return len;
      }
      _798_js = (_799_valueOrError0).Extract(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor());
      Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> _out12;
      _out12 = Std.JSON.ZeroCopy.API.__default.SerializeInto(_798_js, bs);
      len = _out12;
    }
    return len;
  }
  public static Std.Wrappers.Result<Std.JSON.Values.JSON, Std.JSON.Errors.DeserializationError> Deserialize(dafny.DafnySequence<? extends java.lang.Byte> bs) {
    Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.DeserializationError> _800_valueOrError0 = Std.JSON.ZeroCopy.API.__default.Deserialize(bs);
    if ((_800_valueOrError0).IsFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor())) {
      return (_800_valueOrError0).<Std.JSON.Values.JSON>PropagateFailure(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor(), Std.JSON.Values.JSON._typeDescriptor());
    } else {
      Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> _801_js = (_800_valueOrError0).Extract(Std.JSON.Grammar.Structural.<Std.JSON.Grammar.Value>_typeDescriptor(Std.JSON.Grammar.Value._typeDescriptor()), Std.JSON.Errors.DeserializationError._typeDescriptor());
      return Std.JSON.Deserializer.__default.JSON(_801_js);
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.API._default";
  }
}
