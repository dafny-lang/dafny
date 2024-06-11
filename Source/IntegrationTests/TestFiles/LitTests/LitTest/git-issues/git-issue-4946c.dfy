// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --general-traits=datatype

trait GeneralTrait { }
trait ReferenceTrait extends object { }

type SubsetType = x: GeneralTrait | true // error: cannot find witness (didn't try anything)
type Reference = x: ReferenceTrait | true // error: cannot find witness (tried null)
