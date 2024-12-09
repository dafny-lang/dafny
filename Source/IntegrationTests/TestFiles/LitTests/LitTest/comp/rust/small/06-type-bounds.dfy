// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait SuperTrait {
  function toString(): string
}

trait SubSuperTrait extends SuperTrait {
}

method PrintTwice<K extends SuperTrait>(k: K) {
  print (k as SuperTrait).toString();
  print (k as SuperTrait).toString();
}

datatype TestPrintTwice extends SubSuperTrait = TestPrintTwice {
  function toString(): string { "hello" }
}

method Main() {
  PrintTwice(TestPrintTwice());
  PrintTwice((TestPrintTwice() as SubSuperTrait));
  PrintTwice((TestPrintTwice() as SuperTrait));
}