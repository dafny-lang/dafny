// Class Writer
// Dafny class Writer compiled into Java
package Std.JSON.Utils.Views.Writers;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class Writer {
  public Writer() {
  }
  public static Writer__ Witness = Std.JSON.Utils.Views.Writers.Writer__.create(0, Std.JSON.Utils.Views.Writers.Chain.create_Empty());
  public static Writer__ defaultValue() {
    return Witness;
  }
  private static final dafny.TypeDescriptor<Writer__> _TYPE = dafny.TypeDescriptor.<Writer__>referenceWithInitializer(Writer__.class, () -> Writer.defaultValue());
  public static dafny.TypeDescriptor<Writer__> _typeDescriptor() {
    return (dafny.TypeDescriptor<Writer__>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
