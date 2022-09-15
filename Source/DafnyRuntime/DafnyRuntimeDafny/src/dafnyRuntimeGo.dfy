
include "dafnyRuntime.dfy"

module {:extern "dafny"} DafnyGo refines Dafny {

  const SIZE_T_LIMIT: nat := 0x8000_0000

  lemma EnsureSizeTLimitAboveMinimum() ensures 128 <= SIZE_T_LIMIT {}
}