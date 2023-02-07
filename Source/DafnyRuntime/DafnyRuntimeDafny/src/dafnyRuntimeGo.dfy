
include "dafnyRuntime.dfy"

module {:extern "dafny"} {:options "/functionSyntax:4"} DafnyGo refines Dafny {

  const SIZE_T_LIMIT: nat := 0x8000_0000

  lemma EnsureSizeTLimitAboveMinimum() ensures 128 <= SIZE_T_LIMIT {}

  trait {:extern} Sequence<T> ... {

    method SetString() returns (ret: Sequence<T>)
      modifies this
    {
      isString := true;
      return this;
    }
  }
}
