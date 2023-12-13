// Class __default
// Dafny class __default compiled into Java
package Std.Unicode.Utf8EncodingScheme;

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
import Std.Strings.*;
import Std.Unicode.Base.*;
import Std.Unicode.Utf8EncodingForm.*;
import Std.Unicode.Utf16EncodingForm.*;
import Std.Unicode.UnicodeStringsWithUnicodeChar.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Serialize(dafny.DafnySequence<? extends java.lang.Byte> s) {
    return Std.Collections.Seq.__default.<java.lang.Byte, java.lang.Byte>Map(dafny.TypeDescriptor.BYTE, Std.BoundedInts.uint8._typeDescriptor(), ((java.util.function.Function<java.lang.Byte, java.lang.Byte>)(_308_c_boxed0) -> {
      byte _308_c = ((byte)(java.lang.Object)(_308_c_boxed0));
      return (_308_c);
    }), s);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> Deserialize(dafny.DafnySequence<? extends java.lang.Byte> b) {
    return Std.Collections.Seq.__default.<java.lang.Byte, java.lang.Byte>Map(Std.BoundedInts.uint8._typeDescriptor(), dafny.TypeDescriptor.BYTE, ((java.util.function.Function<java.lang.Byte, java.lang.Byte>)(_309_b_boxed0) -> {
      byte _309_b = ((byte)(java.lang.Object)(_309_b_boxed0));
      return (_309_b);
    }), b);
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Utf8EncodingScheme._default";
  }
}
