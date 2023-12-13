// Class __default
// Dafny class __default compiled into Java
package Std.Arithmetic.DivInternals;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger DivPos(java.math.BigInteger x, java.math.BigInteger d)
  {
    java.math.BigInteger _147___accumulator = java.math.BigInteger.ZERO;
    TAIL_CALL_START: while (true) {
      if ((x).signum() == -1) {
        _147___accumulator = (_147___accumulator).add(java.math.BigInteger.valueOf(-1L));
        java.math.BigInteger _in38 = (x).add(d);
        java.math.BigInteger _in39 = d;
        x = _in38;
        d = _in39;
        continue TAIL_CALL_START;
      } else if ((x).compareTo(d) < 0) {
        return (java.math.BigInteger.ZERO).add(_147___accumulator);
      } else {
        _147___accumulator = (_147___accumulator).add(java.math.BigInteger.ONE);
        java.math.BigInteger _in40 = (x).subtract(d);
        java.math.BigInteger _in41 = d;
        x = _in40;
        d = _in41;
        continue TAIL_CALL_START;
      }
    }
  }
  public static java.math.BigInteger DivRecursive(java.math.BigInteger x, java.math.BigInteger d)
  {
    if ((d).signum() == 1) {
      return __default.DivPos(x, d);
    } else {
      return (java.math.BigInteger.valueOf(-1L)).multiply(__default.DivPos(x, (java.math.BigInteger.valueOf(-1L)).multiply(d)));
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Arithmetic.DivInternals._default";
  }
}
