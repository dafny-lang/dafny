// Class __default
// Dafny class __default compiled into Java
package Std.Arithmetic.Power;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger Pow(java.math.BigInteger b, java.math.BigInteger e)
  {
    java.math.BigInteger _133___accumulator = java.math.BigInteger.ONE;
    TAIL_CALL_START: while (true) {
      if ((e).signum() == 0) {
        return (java.math.BigInteger.ONE).multiply(_133___accumulator);
      } else {
        _133___accumulator = (_133___accumulator).multiply(b);
        java.math.BigInteger _in38 = b;
        java.math.BigInteger _in39 = (e).subtract(java.math.BigInteger.ONE);
        b = _in38;
        e = _in39;
        continue TAIL_CALL_START;
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Arithmetic.Power._default";
  }
}
