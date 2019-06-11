using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Text;
using Microsoft.Boogie;

  /// <summary>
    /// A class containing static methods to extend the functionality of Code Contracts
    /// </summary>

public static class cce {
  [Pure]
  public static T NonNull<T>(T t) where T : class {
    Contract.Assert(t != null);
    return t;
  }
  [Pure]
  public static bool NonNullElements<T>(IEnumerable<T> collection) where T : class {
    return collection != null && Contract.ForAll(collection, c => c != null);
  }
  [Pure]
  public static bool NonNullDictionaryAndValues<TKey, TValue>(IDictionary<TKey, TValue> collection) where TValue : class {
    return collection != null && NonNullElements(collection.Values);
  }
  [Pure]
  public static bool NonNullElements<T>(Microsoft.Dafny.Graph<T> collection) where T : class {
    return collection != null && cce.NonNullElements(collection.TopologicallySortedComponents());
  }
  [Pure]
  public static void BeginExpose(object o) {
  }
  [Pure]
  public static void EndExpose() {
  }
  public static class Owner {
    [Pure]
    public static bool Same(object o, object p) {
      return true;
    }
    [Pure]
    public static void AssignSame(object o, object p) {
    }
    [Pure]
    public static object ElementProxy(object o) {
      return o;
    }
    [Pure]
    public static bool None(object o) {
      return true;
    }
  }
  [Pure]
  public static void LoopInvariant(bool p) {
    Contract.Assert(p);
  }

  public class UnreachableException : Exception {
    public UnreachableException() {
    }
  }
}

public class PeerAttribute : System.Attribute {
}
public class RepAttribute : System.Attribute {
}
public class CapturedAttribute : System.Attribute {
}
public class NotDelayedAttribute : System.Attribute {
}
public class NoDefaultContractAttribute : System.Attribute {
}
public class VerifyAttribute : System.Attribute {
  public VerifyAttribute(bool b) {

  }
}
public class StrictReadonlyAttribute : System.Attribute {
 }
public class AdditiveAttribute : System.Attribute {
}
public class ReadsAttribute : System.Attribute {
  public enum Reads {
    Nothing,
  };
  public ReadsAttribute(object o) {
  }
}
