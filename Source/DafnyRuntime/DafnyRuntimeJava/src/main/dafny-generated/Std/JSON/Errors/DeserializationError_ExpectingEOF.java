// Class DeserializationError_ExpectingEOF
// Dafny class DeserializationError_ExpectingEOF compiled into Java
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
import Std.JSON.Values.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class DeserializationError_ExpectingEOF extends DeserializationError {
  public DeserializationError_ExpectingEOF () {
    super();
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    DeserializationError_ExpectingEOF o = (DeserializationError_ExpectingEOF)other;
    return true;
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 4;
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Errors.DeserializationError.ExpectingEOF");
    return s.toString();
  }
}
