// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.API;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError> Serialize(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js) {
    return Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, Std.JSON.Errors.SerializationError>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(Std.BoundedInts.uint8._typeDescriptor()), Std.JSON.Errors.SerializationError._typeDescriptor(), (Std.JSON.ZeroCopy.Serializer.__default.Text(js)).Bytes());
  }
  public static Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> SerializeAlloc(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js)
  {
    Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> bs = Std.Wrappers.Result.<byte[], Std.JSON.Errors.SerializationError>Default(dafny.TypeDescriptor.BYTE_ARRAY, Std.JSON.Errors.SerializationError._typeDescriptor(), new byte[0]);
    if(true) {
      Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> _out14;
      _out14 = Std.JSON.ZeroCopy.Serializer.__default.Serialize(js);
      bs = _out14;
    }
    return bs;
  }
  public static Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> SerializeInto(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js, byte[] bs)
  {
    Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> len = Std.Wrappers.Result.<java.lang.Integer, Std.JSON.Errors.SerializationError>Default(Std.BoundedInts.uint32._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), 0);
    if(true) {
      Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> _out15;
      _out15 = Std.JSON.ZeroCopy.Serializer.__default.SerializeTo(js, bs);
      len = _out15;
    }
    return len;
  }
  public static Std.Wrappers.Result<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, Std.JSON.Errors.DeserializationError> Deserialize(dafny.DafnySequence<? extends java.lang.Byte> bs) {
    return Std.JSON.ZeroCopy.Deserializer.API.__default.OfBytes(bs);
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.API._default";
  }
}
