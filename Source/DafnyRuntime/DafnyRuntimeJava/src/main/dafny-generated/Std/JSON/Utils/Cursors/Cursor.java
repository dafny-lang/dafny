// Class Cursor
// Dafny class Cursor compiled into Java
package Std.JSON.Utils.Cursors;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class Cursor {
  public Cursor() {
  }
  public static Cursor__ Witness = Std.JSON.Utils.Cursors.Cursor__.create(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()), 0, 0, 0);
  public static Cursor__ defaultValue() {
    return Witness;
  }
  private static final dafny.TypeDescriptor<Cursor__> _TYPE = dafny.TypeDescriptor.<Cursor__>referenceWithInitializer(Cursor__.class, () -> Cursor.defaultValue());
  public static dafny.TypeDescriptor<Cursor__> _typeDescriptor() {
    return (dafny.TypeDescriptor<Cursor__>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
