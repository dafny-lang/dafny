// Class __default
// Dafny class __default compiled into Java
package Std.Arithmetic.ModInternals;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger ModRecursive(java.math.BigInteger x, java.math.BigInteger d)
  {
    TAIL_CALL_START: while (true) {
      if ((x).signum() == -1) {
        java.math.BigInteger _in30 = (d).add(x);
        java.math.BigInteger _in31 = d;
        x = _in30;
        d = _in31;
        continue TAIL_CALL_START;
      } else if ((x).compareTo(d) < 0) {
        return x;
      } else {
        java.math.BigInteger _in32 = (x).subtract(d);
        java.math.BigInteger _in33 = d;
        x = _in32;
        d = _in33;
        continue TAIL_CALL_START;
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Arithmetic.ModInternals._default";
  }
}
