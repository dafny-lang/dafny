// Class Maybe<T>
// Dafny class Maybe<T> compiled into Java
package Std.JSON.Grammar;

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

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Maybe<T> {
  protected dafny.TypeDescriptor<T> _td_T;
  public Maybe(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
  }

  public static <T> Maybe<T> Default(dafny.TypeDescriptor<T> _td_T) {
    return Std.JSON.Grammar.Maybe.<T>create_Empty(_td_T);
  }
  public static <T> dafny.TypeDescriptor<Maybe<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<Maybe<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Maybe<T>>referenceWithInitializer(Maybe.class, () -> Maybe.<T>Default(_td_T));
  }
  public static <T> Maybe<T> create_Empty(dafny.TypeDescriptor<T> _td_T) {
    return new Maybe_Empty<T>(_td_T);
  }
  public static <T> Maybe<T> create_NonEmpty(dafny.TypeDescriptor<T> _td_T, T t) {
    return new Maybe_NonEmpty<T>(_td_T, t);
  }
  public boolean is_Empty() { return this instanceof Maybe_Empty; }
  public boolean is_NonEmpty() { return this instanceof Maybe_NonEmpty; }
  public T dtor_t() {
    Maybe<T> d = this;
    return ((Maybe_NonEmpty<T>)d)._t;
  }
}
