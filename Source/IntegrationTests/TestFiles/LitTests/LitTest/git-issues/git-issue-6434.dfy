// RUN: %baredafny resolve --use-basename-for-filename --show-snippets:false "%s" > "%t"
// RUN: %baredafny resolve --type-system-refresh --general-newtypes --use-basename-for-filename --show-snippets:false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// An untyped, module-level const whose RHS reads a datatype discriminator or destructor used to
// crash the resolver: these fields are not tracked individually, so their pre-types were still
// unfilled when the const's RHS was resolved eagerly.

datatype Mode = Owned | Loaned | Other

const discriminatorConst := (m: Mode) => m.Owned? || m.Loaned?

datatype Cell = Cell(value: int)

const destructorConst := (c: Cell) => c.value
