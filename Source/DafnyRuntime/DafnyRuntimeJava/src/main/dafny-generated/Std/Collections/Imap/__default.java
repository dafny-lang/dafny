// Class __default
// Dafny class __default compiled into Java
package Std.Collections.Imap;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;
import Std.Collections.Array.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__X, __Y> Std.Wrappers.Option<__Y> Get(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m, __X x)
  {
    if ((m).<__X>contains(x)) {
      return Std.Wrappers.Option.<__Y>create_Some(_td___Y, ((__Y)(java.lang.Object)((m).get(x))));
    } else {
      return Std.Wrappers.Option.<__Y>create_None(_td___Y);
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Collections.Imap._default";
  }
}
