// Class Split<T>
// Dafny class Split<T> compiled into Java
package Std.JSON.Utils.Cursors;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class Split<T> {
  public T _t;
  public Cursor__ _cs;
  protected dafny.TypeDescriptor<T> _td_T;
  public Split (dafny.TypeDescriptor<T> _td_T, T t, Cursor__ cs) {
    this._td_T = _td_T;
    this._t = t;
    this._cs = cs;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Split<T> o = (Split<T>)other;
    return true && java.util.Objects.equals(this._t, o._t) && java.util.Objects.equals(this._cs, o._cs);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._t);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._cs);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Cursors.Split.SP");
    s.append("(");
    s.append(dafny.Helpers.toString(this._t));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._cs));
    s.append(")");
    return s.toString();
  }

  public static <T> Split<T> Default(dafny.TypeDescriptor<T> _td_T, T _default_T) {
    return Std.JSON.Utils.Cursors.Split.<T>create(_td_T, _default_T, FreshCursor.defaultValue());
  }
  public static <T> dafny.TypeDescriptor<Split<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<Split<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Split<T>>referenceWithInitializer(Split.class, () -> Split.<T>Default(_td_T, _td_T.defaultValue()));
  }
  public static <T> Split<T> create(dafny.TypeDescriptor<T> _td_T, T t, Cursor__ cs) {
    return new Split<T>(_td_T, t, cs);
  }
  public static <T> Split<T> create_SP(dafny.TypeDescriptor<T> _td_T, T t, Cursor__ cs) {
    return create(_td_T, t, cs);
  }
  public boolean is_SP() { return true; }
  public T dtor_t() {
    return this._t;
  }
  public Cursor__ dtor_cs() {
    return this._cs;
  }
}
