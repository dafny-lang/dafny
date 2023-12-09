// Class jclose
// Dafny class jclose compiled into Java
package Std.JSON.ZeroCopy.Deserializer.Arrays;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class jclose {
  public jclose() {
  }
  public static Std.JSON.Utils.Views.Core.View__ Witness = Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(Std.JSON.ZeroCopy.Deserializer.ArrayParams.__default.CLOSE()));
  public static Std.JSON.Utils.Views.Core.View__ defaultValue() {
    return Witness;
  }
  private static final dafny.TypeDescriptor<Std.JSON.Utils.Views.Core.View__> _TYPE = dafny.TypeDescriptor.<Std.JSON.Utils.Views.Core.View__>referenceWithInitializer(Std.JSON.Utils.Views.Core.View__.class, () -> jclose.defaultValue());
  public static dafny.TypeDescriptor<Std.JSON.Utils.Views.Core.View__> _typeDescriptor() {
    return (dafny.TypeDescriptor<Std.JSON.Utils.Views.Core.View__>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
