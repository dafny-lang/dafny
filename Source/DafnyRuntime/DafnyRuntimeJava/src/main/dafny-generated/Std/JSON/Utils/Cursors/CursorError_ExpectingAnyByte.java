// Class CursorError_ExpectingAnyByte<R>
// Dafny class CursorError_ExpectingAnyByte<R> compiled into Java
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
import Std.JSON.Values.*;
import Std.JSON.Errors.*;
import Std.JSON.Spec.*;
import Std.JSON.Utils.Views.Core.*;
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;
import Std.JSON.Utils.Lexers.Strings.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class CursorError_ExpectingAnyByte<R> extends CursorError<R> {
  public dafny.DafnySequence<? extends java.lang.Byte> _expected__sq;
  public short _b;
  public CursorError_ExpectingAnyByte (dafny.TypeDescriptor<R> _td_R, dafny.DafnySequence<? extends java.lang.Byte> expected__sq, short b) {
    super(_td_R);
    this._expected__sq = expected__sq;
    this._b = b;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    CursorError_ExpectingAnyByte<R> o = (CursorError_ExpectingAnyByte<R>)other;
    return true && java.util.Objects.equals(this._expected__sq, o._expected__sq) && this._b == o._b;
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 2;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._expected__sq);
    hash = ((hash << 5) + hash) + java.lang.Short.hashCode(this._b);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Cursors.CursorError.ExpectingAnyByte");
    s.append("(");
    s.append(dafny.Helpers.toString(this._expected__sq));
    s.append(", ");
    s.append(this._b);
    s.append(")");
    return s.toString();
  }
}
