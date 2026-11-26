// RUN: %testDafnyForEachResolver "%s"

// A named constructor's unresolved Path type is not the only way MatchFlattener's clone meets a
// UserDefinedType with a null ResolvedClass. A refined method body is another: the body cloned
// from A into B keeps an array allocation whose element type is not resolved in B, so flattening
// the match in B crashed in the UserDefinedType clone constructor -- on an error-free program,
// through LiteralModuleDecl.Resolve rather than MakeAbstractSignature.
//
// The three element types reach the clone by three different routes: E directly, seq<E> through
// a recursive CloneType, and map<int, E> through MapType's own clone constructor, which is the
// frame that made the second report on the issue look like a separate bug.

module A {
  datatype E = E(x: int)
  datatype D = X | Y

  method M(d: D) {
    match d
    case X =>
      var direct := new E[10];
      var nested := new seq<E>[10];
      var viaMap := new map<int, E>[10];
    case Y =>
  }
}

module B refines A { }
