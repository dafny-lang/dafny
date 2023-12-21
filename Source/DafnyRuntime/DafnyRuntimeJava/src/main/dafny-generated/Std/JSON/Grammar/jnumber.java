// Class jnumber
// Dafny class jnumber compiled into Java
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
public class jnumber {
  public Std.JSON.Utils.Views.Core.View__ _minus;
  public Std.JSON.Utils.Views.Core.View__ _num;
  public Maybe<jfrac> _frac;
  public Maybe<jexp> _exp;
  public jnumber (Std.JSON.Utils.Views.Core.View__ minus, Std.JSON.Utils.Views.Core.View__ num, Maybe<jfrac> frac, Maybe<jexp> exp) {
    this._minus = minus;
    this._num = num;
    this._frac = frac;
    this._exp = exp;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    jnumber o = (jnumber)other;
    return true && java.util.Objects.equals(this._minus, o._minus) && java.util.Objects.equals(this._num, o._num) && java.util.Objects.equals(this._frac, o._frac) && java.util.Objects.equals(this._exp, o._exp);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._minus);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._num);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._frac);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._exp);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Grammar.jnumber.JNumber");
    s.append("(");
    s.append(dafny.Helpers.toString(this._minus));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._num));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._frac));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._exp));
    s.append(")");
    return s.toString();
  }

  private static final jnumber theDefault = Std.JSON.Grammar.jnumber.create(jminus.defaultValue(), jnum.defaultValue(), Maybe.<jfrac>Default(jfrac._typeDescriptor()), Maybe.<jexp>Default(jexp._typeDescriptor()));
  public static jnumber Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<jnumber> _TYPE = dafny.TypeDescriptor.<jnumber>referenceWithInitializer(jnumber.class, () -> jnumber.Default());
  public static dafny.TypeDescriptor<jnumber> _typeDescriptor() {
    return (dafny.TypeDescriptor<jnumber>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static jnumber create(Std.JSON.Utils.Views.Core.View__ minus, Std.JSON.Utils.Views.Core.View__ num, Maybe<jfrac> frac, Maybe<jexp> exp) {
    return new jnumber(minus, num, frac, exp);
  }
  public static jnumber create_JNumber(Std.JSON.Utils.Views.Core.View__ minus, Std.JSON.Utils.Views.Core.View__ num, Maybe<jfrac> frac, Maybe<jexp> exp) {
    return create(minus, num, frac, exp);
  }
  public boolean is_JNumber() { return true; }
  public Std.JSON.Utils.Views.Core.View__ dtor_minus() {
    return this._minus;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_num() {
    return this._num;
  }
  public Maybe<jfrac> dtor_frac() {
    return this._frac;
  }
  public Maybe<jexp> dtor_exp() {
    return this._exp;
  }
}
