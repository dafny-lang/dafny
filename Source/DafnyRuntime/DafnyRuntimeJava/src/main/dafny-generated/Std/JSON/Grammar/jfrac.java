// Class jfrac
// Dafny class jfrac compiled into Java
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
import Std.JavaFileIOInternalExterns.*;
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
public class jfrac {
  public Std.JSON.Utils.Views.Core.View__ _period;
  public Std.JSON.Utils.Views.Core.View__ _num;
  public jfrac (Std.JSON.Utils.Views.Core.View__ period, Std.JSON.Utils.Views.Core.View__ num) {
    this._period = period;
    this._num = num;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    jfrac o = (jfrac)other;
    return true && java.util.Objects.equals(this._period, o._period) && java.util.Objects.equals(this._num, o._num);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._period);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._num);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Grammar.jfrac.JFrac");
    s.append("(");
    s.append(dafny.Helpers.toString(this._period));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._num));
    s.append(")");
    return s.toString();
  }

  private static final jfrac theDefault = Std.JSON.Grammar.jfrac.create(jperiod.defaultValue(), jnum.defaultValue());
  public static jfrac Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<jfrac> _TYPE = dafny.TypeDescriptor.<jfrac>referenceWithInitializer(jfrac.class, () -> jfrac.Default());
  public static dafny.TypeDescriptor<jfrac> _typeDescriptor() {
    return (dafny.TypeDescriptor<jfrac>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static jfrac create(Std.JSON.Utils.Views.Core.View__ period, Std.JSON.Utils.Views.Core.View__ num) {
    return new jfrac(period, num);
  }
  public static jfrac create_JFrac(Std.JSON.Utils.Views.Core.View__ period, Std.JSON.Utils.Views.Core.View__ num) {
    return create(period, num);
  }
  public boolean is_JFrac() { return true; }
  public Std.JSON.Utils.Views.Core.View__ dtor_period() {
    return this._period;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_num() {
    return this._num;
  }
}
