// Class __default
// Dafny class __default compiled into Java
package Std.Unicode.Base;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean IsInAssignedPlane(int i) {
    byte _189_plane = ((byte) ((int)  ((i) >>> ((byte) 16))));
    return (__default.ASSIGNED__PLANES()).<java.lang.Byte>contains(_189_plane);
  }
  public static int HIGH__SURROGATE__MIN()
  {
    return 55296;
  }
  public static int HIGH__SURROGATE__MAX()
  {
    return 56319;
  }
  public static int LOW__SURROGATE__MIN()
  {
    return 56320;
  }
  public static int LOW__SURROGATE__MAX()
  {
    return 57343;
  }
  public static dafny.DafnySet<? extends java.lang.Byte> ASSIGNED__PLANES()
  {
    return dafny.DafnySet.<java.lang.Byte> of((byte) 0, (byte) 1, (byte) 2, (byte) 3, (byte) 14, (byte) 15, (byte) 16);
  }
  @Override
  public java.lang.String toString() {
    return "Std.Unicode.Base._default";
  }
}
