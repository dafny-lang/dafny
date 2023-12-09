// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Utils.Parsers;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__T, __R> java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<__R>>> ParserWitness(dafny.TypeDescriptor<__T> _td___T, dafny.TypeDescriptor<__R> _td___R)
  {
    return ((java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<__R>>>)(_405___v9_boxed0) -> {
      Std.JSON.Utils.Cursors.Cursor__ _405___v9 = ((Std.JSON.Utils.Cursors.Cursor__)(java.lang.Object)(_405___v9_boxed0));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<__R>>create_Failure(Std.JSON.Utils.Cursors.Split.<__T>_typeDescriptor(_td___T), Std.JSON.Utils.Cursors.CursorError.<__R>_typeDescriptor(_td___R), Std.JSON.Utils.Cursors.CursorError.<__R>create_EOF(_td___R));
    });
  }
  public static <__T, __R> java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<__R>>> SubParserWitness(dafny.TypeDescriptor<__T> _td___T, dafny.TypeDescriptor<__R> _td___R)
  {
    return ((java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<__R>>>)(_406_cs_boxed0) -> {
      Std.JSON.Utils.Cursors.Cursor__ _406_cs = ((Std.JSON.Utils.Cursors.Cursor__)(java.lang.Object)(_406_cs_boxed0));
      return Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<__T>, Std.JSON.Utils.Cursors.CursorError<__R>>create_Failure(Std.JSON.Utils.Cursors.Split.<__T>_typeDescriptor(_td___T), Std.JSON.Utils.Cursors.CursorError.<__R>_typeDescriptor(_td___R), Std.JSON.Utils.Cursors.CursorError.<__R>create_EOF(_td___R));
    });
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Utils.Parsers._default";
  }
}
