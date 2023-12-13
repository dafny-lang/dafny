// Class ValueParser
// Dafny class ValueParser compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Core;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class ValueParser {
  public ValueParser() {
  }
  private static final dafny.TypeDescriptor<Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError>> _TYPE = dafny.TypeDescriptor.<Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError>>referenceWithInitializer(Std.JSON.Utils.Parsers.SubParser__.class, () -> Std.JSON.Utils.Parsers.SubParser.defaultValue(Std.JSON.Grammar.Value._typeDescriptor(), Std.JSON.Errors.DeserializationError._typeDescriptor()));
  public static dafny.TypeDescriptor<Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError>> _typeDescriptor() {
    return (dafny.TypeDescriptor<Std.JSON.Utils.Parsers.SubParser__<Std.JSON.Grammar.Value, Std.JSON.Errors.DeserializationError>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
