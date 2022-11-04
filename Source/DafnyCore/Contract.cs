using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Dafny;

class Contract {
  public static void Requires(bool condition) {
  }

  public static bool ForAll<T>(IEnumerable<T> collection, Predicate<T> predicate) {
    return collection.All(v => predicate(v));
  }

  public static void Assume(bool condition, string userMessage = null) {

  }
  public static void Invariant(bool condition, string userMessage = null) {
  }

  [Conditional("CONTRACTS_FULL")]
  public static void Ensures(bool condition, string userMessage = null) {
  }
  public static T Result<T>() { return default!; }
  public static void Assert(bool condition, string userMessage = null) {
  }

  public static bool Exists<T>(IEnumerable<T> collection, Predicate<T> predicate) {
    return collection.Any(v => predicate(v));
  }

  public static T ValueAtReturn<T>(out T value) {
    value = default!;
    return value;
  }

  public static T OldValue<T>(T value) { return default!; }
}