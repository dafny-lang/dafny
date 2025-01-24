// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --general-traits=legacy

trait GeneralTrait { }
trait ReferenceTrait extends object { }

type SubsetType = x: GeneralTrait | true // error: cannot find witness (tried null)
type Reference = x: ReferenceTrait | true // error: cannot find witness (tried null)
