// Class jexp
// Dafny class jexp compiled into Java
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
public class jexp {
  public Std.JSON.Utils.Views.Core.View__ _e;
  public Std.JSON.Utils.Views.Core.View__ _sign;
  public Std.JSON.Utils.Views.Core.View__ _num;
  public jexp (Std.JSON.Utils.Views.Core.View__ e, Std.JSON.Utils.Views.Core.View__ sign, Std.JSON.Utils.Views.Core.View__ num) {
    this._e = e;
    this._sign = sign;
    this._num = num;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    jexp o = (jexp)other;
    return true && java.util.Objects.equals(this._e, o._e) && java.util.Objects.equals(this._sign, o._sign) && java.util.Objects.equals(this._num, o._num);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._e);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._sign);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._num);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Grammar.jexp.JExp");
    s.append("(");
    s.append(dafny.Helpers.toString(this._e));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._sign));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._num));
    s.append(")");
    return s.toString();
  }

  private static final jexp theDefault = Std.JSON.Grammar.jexp.create(je.defaultValue(), jsign.defaultValue(), jnum.defaultValue());
  public static jexp Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<jexp> _TYPE = dafny.TypeDescriptor.<jexp>referenceWithInitializer(jexp.class, () -> jexp.Default());
  public static dafny.TypeDescriptor<jexp> _typeDescriptor() {
    return (dafny.TypeDescriptor<jexp>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static jexp create(Std.JSON.Utils.Views.Core.View__ e, Std.JSON.Utils.Views.Core.View__ sign, Std.JSON.Utils.Views.Core.View__ num) {
    return new jexp(e, sign, num);
  }
  public static jexp create_JExp(Std.JSON.Utils.Views.Core.View__ e, Std.JSON.Utils.Views.Core.View__ sign, Std.JSON.Utils.Views.Core.View__ num) {
    return create(e, sign, num);
  }
  public boolean is_JExp() { return true; }
  public Std.JSON.Utils.Views.Core.View__ dtor_e() {
    return this._e;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_sign() {
    return this._sign;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_num() {
    return this._num;
  }
}
