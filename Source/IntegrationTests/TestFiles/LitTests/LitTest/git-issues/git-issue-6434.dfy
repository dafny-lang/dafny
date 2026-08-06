// RUN: %testDafnyForEachResolver "%s"

// An untyped, module-level const whose RHS reads a datatype discriminator or destructor used to
// crash the resolver: these fields are not tracked individually, so their pre-types were still
// unfilled when the const's RHS was resolved eagerly.

datatype Mode = Owned | Loaned | Other

const discriminatorConst := (m: Mode) => m.Owned? || m.Loaned?

datatype Cell = Cell(value: int)

const destructorConst := (c: Cell) => c.value

// The same staleness affects a constructor's formals, which are filled in at the same place and are
// likewise untracked. Their three consumers each read Formals[i].PreType: a constructor call, a
// case pattern, and a match pattern.

const constructorCall := D.Mk(0)

datatype D = Mk(x: int)

const casePattern := (d: D) => var Mk(v) := d; v

const datatypeUpdate := (c: Cell) => c.(value := 5)

// The match case needs an ambiguous constructor name, so that resolution does not first take the
// constructor-name path (which already resolves the signature on demand).

const matchPattern := (p: P) => match p { case Mk(a, b) => a + b }

datatype P = Mk(x: int, y: int)

datatype R = Mk(u: int, v: int)

