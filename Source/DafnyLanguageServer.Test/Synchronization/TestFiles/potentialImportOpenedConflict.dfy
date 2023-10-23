include "./notCached.dfy"

module ContainsPotentialImportOpenedConflict {
  import Conflict = ConflictOptionB
  import opened ExposesConflictOptionA
  import ChangedClonedId

  // This causes KeyResolution to miss the cache, but its import declarations don't miss it, so they're copied into KeyResolution
  const useChanged := ChangedClonedId.changed

  // Use Types which can become ambigious of the opened resolution fails to decide which Types we're referring to.
  const valueUser := Conflict.value
}

module ConflictOptionB
{
  const value := 3
}

module ExposesConflictOptionA {
  import Conflict = ConflictOptionA
}

module ConflictOptionA
{
  const value := 2
}