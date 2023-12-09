// Class Decimal
// Dafny class Decimal compiled into Java
package Std.JSON.Values;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class Decimal {
  public java.math.BigInteger _n;
  public java.math.BigInteger _e10;
  public Decimal (java.math.BigInteger n, java.math.BigInteger e10) {
    this._n = n;
    this._e10 = e10;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Decimal o = (Decimal)other;
    return true && java.util.Objects.equals(this._n, o._n) && java.util.Objects.equals(this._e10, o._e10);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._n);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._e10);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Values.Decimal.Decimal");
    s.append("(");
    s.append(dafny.Helpers.toString(this._n));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._e10));
    s.append(")");
    return s.toString();
  }

  private static final Decimal theDefault = Std.JSON.Values.Decimal.create(java.math.BigInteger.ZERO, java.math.BigInteger.ZERO);
  public static Decimal Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Decimal> _TYPE = dafny.TypeDescriptor.<Decimal>referenceWithInitializer(Decimal.class, () -> Decimal.Default());
  public static dafny.TypeDescriptor<Decimal> _typeDescriptor() {
    return (dafny.TypeDescriptor<Decimal>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Decimal create(java.math.BigInteger n, java.math.BigInteger e10) {
    return new Decimal(n, e10);
  }
  public static Decimal create_Decimal(java.math.BigInteger n, java.math.BigInteger e10) {
    return create(n, e10);
  }
  public boolean is_Decimal() { return true; }
  public java.math.BigInteger dtor_n() {
    return this._n;
  }
  public java.math.BigInteger dtor_e10() {
    return this._e10;
  }
}
