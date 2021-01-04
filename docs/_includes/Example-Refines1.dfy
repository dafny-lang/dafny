module A {
  const a := 10
}

module B refines A { // the top-level A, not the submodule A
  module A { const a := 30 }
  method m() { assert a == 10; } // true
}
