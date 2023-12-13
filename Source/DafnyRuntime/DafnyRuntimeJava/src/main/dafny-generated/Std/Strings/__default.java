// Class __default
// Dafny class __default compiled into Java
package Std.Strings;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> OfNat(java.math.BigInteger n) {
    return Std.Strings.DecimalConversion.__default.OfNat(n);
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> OfInt(java.math.BigInteger n) {
    return Std.Strings.DecimalConversion.__default.OfInt(n, '-');
  }
  public static java.math.BigInteger ToNat(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    return Std.Strings.DecimalConversion.__default.ToNat(str);
  }
  public static java.math.BigInteger ToInt(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    return Std.Strings.DecimalConversion.__default.ToInt(str, '-');
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> EscapeQuotes(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    return Std.Strings.CharStrEscaping.__default.Escape(str, dafny.DafnySet.<dafny.CodePoint> of(dafny.CodePoint.valueOf('\"'), dafny.CodePoint.valueOf('\'')), '\\');
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> UnescapeQuotes(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    return Std.Strings.CharStrEscaping.__default.Unescape(str, '\\');
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> OfBool(boolean b) {
    if (b) {
      return dafny.DafnySequence.asUnicodeString("true");
    } else {
      return dafny.DafnySequence.asUnicodeString("false");
    }
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> OfChar(int c) {
    return dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(c));
  }
  @Override
  public java.lang.String toString() {
    return "Std.Strings._default";
  }
}
