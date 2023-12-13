// Class __default
// Dafny class __default compiled into Java
package Std.Arithmetic.DivMod;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean MultiplesVanish(java.math.BigInteger a, java.math.BigInteger b, java.math.BigInteger m)
  {
    return java.util.Objects.equals(dafny.DafnyEuclidean.EuclideanModulus(((m).multiply(a)).add(b), m), dafny.DafnyEuclidean.EuclideanModulus(b, m));
  }
  @Override
  public java.lang.String toString() {
    return "Std.Arithmetic.DivMod._default";
  }
}
