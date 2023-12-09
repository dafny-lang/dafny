// Class __default
// Dafny class __default compiled into Java
package Std.Arithmetic.MulInternals;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger MulPos(java.math.BigInteger x, java.math.BigInteger y)
  {
    java.math.BigInteger _131___accumulator = java.math.BigInteger.ZERO;
    TAIL_CALL_START: while (true) {
      if ((x).signum() == 0) {
        return (java.math.BigInteger.ZERO).add(_131___accumulator);
      } else {
        _131___accumulator = (_131___accumulator).add(y);
        java.math.BigInteger _in28 = (x).subtract(java.math.BigInteger.ONE);
        java.math.BigInteger _in29 = y;
        x = _in28;
        y = _in29;
        continue TAIL_CALL_START;
      }
    }
  }
  public static java.math.BigInteger MulRecursive(java.math.BigInteger x, java.math.BigInteger y)
  {
    if ((x).signum() != -1) {
      return __default.MulPos(x, y);
    } else {
      return (java.math.BigInteger.valueOf(-1L)).multiply(__default.MulPos((java.math.BigInteger.valueOf(-1L)).multiply(x), y));
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Arithmetic.MulInternals._default";
  }
}
