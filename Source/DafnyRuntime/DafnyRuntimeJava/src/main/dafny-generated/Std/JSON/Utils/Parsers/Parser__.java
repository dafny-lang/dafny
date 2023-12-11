// Class Parser__<T, R>
// Dafny class Parser__<T, R> compiled into Java
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
import Std.JavaFileIOInternalExterns.*;
import Std.JSON.Values.*;
import Std.JSON.Errors.*;
import Std.JSON.Spec.*;
import Std.JSON.Utils.Views.Core.*;
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;
import Std.JSON.Utils.Lexers.Strings.*;
import Std.JSON.Utils.Cursors.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Parser__<T, R> {
  public java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<T>, Std.JSON.Utils.Cursors.CursorError<R>>> _fn;
  protected dafny.TypeDescriptor<T> _td_T;
  protected dafny.TypeDescriptor<R> _td_R;
  public Parser__ (dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<T>, Std.JSON.Utils.Cursors.CursorError<R>>> fn) {
    this._td_T = _td_T;
    this._td_R = _td_R;
    this._fn = fn;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Parser__<T, R> o = (Parser__<T, R>)other;
    return true && java.util.Objects.equals(this._fn, o._fn);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._fn);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Parsers.Parser_.Parser");
    s.append("(");
    s.append(dafny.Helpers.toString(this._fn));
    s.append(")");
    return s.toString();
  }

  public static <T, R> Parser__<T, R> Default(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R, T _default_T) {
    return Std.JSON.Utils.Parsers.Parser__.<T, R>create(_td_T, _td_R, ((Std.JSON.Utils.Cursors.Cursor__ x0) -> Std.Wrappers.Result.<Std.JSON.Utils.Cursors.Split<T>, Std.JSON.Utils.Cursors.CursorError<R>>Default(Std.JSON.Utils.Cursors.Split.<T>_typeDescriptor(_td_T), Std.JSON.Utils.Cursors.CursorError.<R>_typeDescriptor(_td_R), Std.JSON.Utils.Cursors.Split.<T>Default(_td_T, _default_T))));
  }
  public static <T, R> dafny.TypeDescriptor<Parser__<T, R>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    return (dafny.TypeDescriptor<Parser__<T, R>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Parser__<T, R>>referenceWithInitializer(Parser__.class, () -> Parser__.<T, R>Default(_td_T, _td_R, _td_T.defaultValue()));
  }
  public static <T, R> Parser__<T, R> create(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<T>, Std.JSON.Utils.Cursors.CursorError<R>>> fn) {
    return new Parser__<T, R>(_td_T, _td_R, fn);
  }
  public static <T, R> Parser__<T, R> create_Parser(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R, java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<T>, Std.JSON.Utils.Cursors.CursorError<R>>> fn) {
    return create(_td_T, _td_R, fn);
  }
  public boolean is_Parser() { return true; }
  public java.util.function.Function<Std.JSON.Utils.Cursors.Cursor__, Std.Wrappers.Result<Std.JSON.Utils.Cursors.Split<T>, Std.JSON.Utils.Cursors.CursorError<R>>> dtor_fn() {
    return this._fn;
  }
}
