// Class DeserializationError_UnsupportedEscape
// Dafny class DeserializationError_UnsupportedEscape compiled into Java
package Std.JSON.Errors;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class DeserializationError_UnsupportedEscape extends DeserializationError {
  public dafny.DafnySequence<? extends dafny.CodePoint> _str;
  public DeserializationError_UnsupportedEscape (dafny.DafnySequence<? extends dafny.CodePoint> str) {
    super();
    this._str = str;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    DeserializationError_UnsupportedEscape o = (DeserializationError_UnsupportedEscape)other;
    return true && java.util.Objects.equals(this._str, o._str);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 1;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._str);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Errors.DeserializationError.UnsupportedEscape");
    s.append("(");
    s.append(dafny.Helpers.ToStringLiteral(this._str));
    s.append(")");
    return s.toString();
  }
}
