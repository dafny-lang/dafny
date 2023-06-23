module {:compile false} {:extern "System"} System {
  trait {:compile false} {:termination false} {:extern} IComparable {}
  trait {:compile false} {:termination false} {:extern} Attribute {}

  newtype {:compile false} {:extern} {:nativeType "int"} int32 =
    x: int | -0x8000_0000 <= x < 0x8000_0000

  class {:compile false} {:extern} Func<TArg, TRet>{}
  class {:compile false} {:extern} Int32 {}
  class {:compile false} {:extern} String {}
  class {:compile false} {:extern} Boolean {}
  class {:compile false} {:extern} Nullable {}
  class {:compile false} {:extern} ValueTuple {}

  class {:compile false} {:extern "Tuple"} Tuple2<T1, T2> {}
  class {:compile false} {:extern "Tuple"} Tuple3<T1, T2, T3> {}
  class {:compile false} {:extern "Tuple"} Tuple4<T1, T2, T3, T4> {}

  module {:compile false} {:extern "System.CommandLine"} CommandLine {
    class {:compile false} {:extern "Option"} Option<T> {}
  }

  module {:compile false} {:extern "System.Collections"} Collections {
  }

  module {:compile false} {:extern "System.Collections.Generic"} Collections.Generic {
    class {:compile false} {:extern} List<T> {}
    class {:compile false} {:extern} IEnumerable<T> {}
    class {:compile false} {:extern} ISet<T> {}
    class {:compile false} {:extern} HashSet<T> {}
    class {:compile false} {:extern} Dictionary<TKey, TValue> {}
  }

  module {:compile false} {:extern "System.Numerics"} Numerics {
    class {:compile false} {:extern} BigInteger {}
  }

  module {:compile false} {:extern "System.Threading"} Threading {
    class {:compile false} {:extern} AsyncLocal<A> {}
  }
}
