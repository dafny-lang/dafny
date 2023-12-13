// Class __default
// Dafny class __default compiled into Java
package Std.Arithmetic.Logarithm;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger Log(java.math.BigInteger base, java.math.BigInteger pow)
  {
    java.math.BigInteger _149___accumulator = java.math.BigInteger.ZERO;
    TAIL_CALL_START: while (true) {
      if ((pow).compareTo(base) < 0) {
        return (java.math.BigInteger.ZERO).add(_149___accumulator);
      } else {
        _149___accumulator = (_149___accumulator).add(java.math.BigInteger.ONE);
        java.math.BigInteger _in44 = base;
        java.math.BigInteger _in45 = dafny.DafnyEuclidean.EuclideanDivision(pow, base);
        base = _in44;
        pow = _in45;
        continue TAIL_CALL_START;
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Arithmetic.Logarithm._default";
  }
}
