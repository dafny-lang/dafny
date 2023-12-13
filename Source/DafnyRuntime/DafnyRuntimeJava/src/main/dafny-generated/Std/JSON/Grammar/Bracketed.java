// Class Bracketed<L, D, S, R>
// Dafny class Bracketed<L, D, S, R> compiled into Java
package Std.JSON.Grammar;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class Bracketed<L, D, S, R> {
  public Structural<L> _l;
  public dafny.DafnySequence<? extends Suffixed<D, S>> _data;
  public Structural<R> _r;
  protected dafny.TypeDescriptor<L> _td_L;
  protected dafny.TypeDescriptor<D> _td_D;
  protected dafny.TypeDescriptor<S> _td_S;
  protected dafny.TypeDescriptor<R> _td_R;
  public Bracketed (dafny.TypeDescriptor<L> _td_L, dafny.TypeDescriptor<D> _td_D, dafny.TypeDescriptor<S> _td_S, dafny.TypeDescriptor<R> _td_R, Structural<L> l, dafny.DafnySequence<? extends Suffixed<D, S>> data, Structural<R> r) {
    this._td_L = _td_L;
    this._td_D = _td_D;
    this._td_S = _td_S;
    this._td_R = _td_R;
    this._l = l;
    this._data = data;
    this._r = r;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Bracketed<L, D, S, R> o = (Bracketed<L, D, S, R>)other;
    return true && java.util.Objects.equals(this._l, o._l) && java.util.Objects.equals(this._data, o._data) && java.util.Objects.equals(this._r, o._r);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._l);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._data);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._r);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Grammar.Bracketed.Bracketed");
    s.append("(");
    s.append(dafny.Helpers.toString(this._l));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._data));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._r));
    s.append(")");
    return s.toString();
  }

  public static <L, D, S, R> Bracketed<L, D, S, R> Default(dafny.TypeDescriptor<L> _td_L, dafny.TypeDescriptor<D> _td_D, dafny.TypeDescriptor<S> _td_S, dafny.TypeDescriptor<R> _td_R, L _default_L, R _default_R) {
    return Std.JSON.Grammar.Bracketed.<L, D, S, R>create(_td_L, _td_D, _td_S, _td_R, Structural.<L>Default(_td_L, _default_L), dafny.DafnySequence.<Suffixed<D, S>> empty(Suffixed.<D, S>_typeDescriptor(_td_D, _td_S)), Structural.<R>Default(_td_R, _default_R));
  }
  public static <L, D, S, R> dafny.TypeDescriptor<Bracketed<L, D, S, R>> _typeDescriptor(dafny.TypeDescriptor<L> _td_L, dafny.TypeDescriptor<D> _td_D, dafny.TypeDescriptor<S> _td_S, dafny.TypeDescriptor<R> _td_R) {
    return (dafny.TypeDescriptor<Bracketed<L, D, S, R>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Bracketed<L, D, S, R>>referenceWithInitializer(Bracketed.class, () -> Bracketed.<L, D, S, R>Default(_td_L, _td_D, _td_S, _td_R, _td_L.defaultValue(), _td_R.defaultValue()));
  }
  public static <L, D, S, R> Bracketed<L, D, S, R> create(dafny.TypeDescriptor<L> _td_L, dafny.TypeDescriptor<D> _td_D, dafny.TypeDescriptor<S> _td_S, dafny.TypeDescriptor<R> _td_R, Structural<L> l, dafny.DafnySequence<? extends Suffixed<D, S>> data, Structural<R> r) {
    return new Bracketed<L, D, S, R>(_td_L, _td_D, _td_S, _td_R, l, data, r);
  }
  public static <L, D, S, R> Bracketed<L, D, S, R> create_Bracketed(dafny.TypeDescriptor<L> _td_L, dafny.TypeDescriptor<D> _td_D, dafny.TypeDescriptor<S> _td_S, dafny.TypeDescriptor<R> _td_R, Structural<L> l, dafny.DafnySequence<? extends Suffixed<D, S>> data, Structural<R> r) {
    return create(_td_L, _td_D, _td_S, _td_R, l, data, r);
  }
  public boolean is_Bracketed() { return true; }
  public Structural<L> dtor_l() {
    return this._l;
  }
  public dafny.DafnySequence<? extends Suffixed<D, S>> dtor_data() {
    return this._data;
  }
  public Structural<R> dtor_r() {
    return this._r;
  }
}
