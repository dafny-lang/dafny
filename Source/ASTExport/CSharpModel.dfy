module {:extern "System"} {:compile false} System {
  trait {:termination false} {:extern} IComparable {}

  class {:extern} Func<TArg, TRet>{}
  class {:extern} String {}
  class {:extern} ValueTuple {}

  class {:extern "Tuple"} Tuple2<T1, T2> {}
  class {:extern "Tuple"} Tuple3<T1, T2, T3> {}
  class {:extern "Tuple"} Tuple4<T1, T2, T3, T4> {}

  module {:extern "System.Collections.Generic"} Collections.Generic {
    class {:extern} List<T> {}
    class {:extern} ISet<T> {}
    class {:extern} HashSet<T> {}
    class {:extern} Dictionary<TKey, TValue> {}
  }
}
