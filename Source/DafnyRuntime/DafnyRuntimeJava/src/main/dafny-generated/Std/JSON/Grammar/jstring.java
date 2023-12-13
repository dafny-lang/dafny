// Class jstring
// Dafny class jstring compiled into Java
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
public class jstring {
  public Std.JSON.Utils.Views.Core.View__ _lq;
  public Std.JSON.Utils.Views.Core.View__ _contents;
  public Std.JSON.Utils.Views.Core.View__ _rq;
  public jstring (Std.JSON.Utils.Views.Core.View__ lq, Std.JSON.Utils.Views.Core.View__ contents, Std.JSON.Utils.Views.Core.View__ rq) {
    this._lq = lq;
    this._contents = contents;
    this._rq = rq;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    jstring o = (jstring)other;
    return true && java.util.Objects.equals(this._lq, o._lq) && java.util.Objects.equals(this._contents, o._contents) && java.util.Objects.equals(this._rq, o._rq);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._lq);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._contents);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._rq);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Grammar.jstring.JString");
    s.append("(");
    s.append(dafny.Helpers.toString(this._lq));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._contents));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._rq));
    s.append(")");
    return s.toString();
  }

  private static final jstring theDefault = Std.JSON.Grammar.jstring.create(jquote.defaultValue(), jstr.defaultValue(), jquote.defaultValue());
  public static jstring Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<jstring> _TYPE = dafny.TypeDescriptor.<jstring>referenceWithInitializer(jstring.class, () -> jstring.Default());
  public static dafny.TypeDescriptor<jstring> _typeDescriptor() {
    return (dafny.TypeDescriptor<jstring>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static jstring create(Std.JSON.Utils.Views.Core.View__ lq, Std.JSON.Utils.Views.Core.View__ contents, Std.JSON.Utils.Views.Core.View__ rq) {
    return new jstring(lq, contents, rq);
  }
  public static jstring create_JString(Std.JSON.Utils.Views.Core.View__ lq, Std.JSON.Utils.Views.Core.View__ contents, Std.JSON.Utils.Views.Core.View__ rq) {
    return create(lq, contents, rq);
  }
  public boolean is_JString() { return true; }
  public Std.JSON.Utils.Views.Core.View__ dtor_lq() {
    return this._lq;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_contents() {
    return this._contents;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_rq() {
    return this._rq;
  }
}
