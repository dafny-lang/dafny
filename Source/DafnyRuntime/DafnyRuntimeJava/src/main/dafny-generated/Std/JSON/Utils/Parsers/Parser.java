// Class Parser
// Dafny class Parser compiled into Java
package Std.JSON.Utils.Parsers;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class Parser<T, R> {
  protected dafny.TypeDescriptor<T> _td_T;
  protected dafny.TypeDescriptor<R> _td_R;
  public Parser(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    this._td_T = _td_T;
    this._td_R = _td_R;
  }
  public static <T, R> Parser__<T, R> defaultValue(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    return __default.<T, R>ParserWitness(_td_T, _td_R);
  }
  public static <T, R> dafny.TypeDescriptor<Parser__<T, R>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    return (dafny.TypeDescriptor<Parser__<T, R>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Parser__<T, R>>referenceWithInitializer(Parser__.class, () -> Parser.defaultValue(_td_T, _td_R));
  }
}
