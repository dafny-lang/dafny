// Class WellFormedCodeUnitSeq
// Dafny class WellFormedCodeUnitSeq compiled into Java
package Std.Unicode.Utf16EncodingForm;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class WellFormedCodeUnitSeq {
  public WellFormedCodeUnitSeq() {
  }
  public static dafny.DafnySequence Witness = dafny.DafnySequence.<java.lang.Short> empty(dafny.TypeDescriptor.SHORT);
  public static dafny.DafnySequence<? extends java.lang.Short> defaultValue() {
    return Witness;
  }
  private static final dafny.TypeDescriptor<dafny.DafnySequence<? extends java.lang.Short>> _TYPE = dafny.TypeDescriptor.<dafny.DafnySequence<? extends java.lang.Short>>referenceWithInitializer(dafny.DafnySequence.class, () -> WellFormedCodeUnitSeq.defaultValue());
  public static dafny.TypeDescriptor<dafny.DafnySequence<? extends java.lang.Short>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.DafnySequence<? extends java.lang.Short>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
