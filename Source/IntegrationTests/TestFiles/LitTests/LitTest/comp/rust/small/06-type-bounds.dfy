// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=datatype --general-newtypes "%s" > "%t"
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

datatype NoSupportEquality extends SuperTrait = NoSupportEquality(ghost f: int -> int) {
  function toString(): string { "Not a string" }
}

newtype MapWrapper<T> = x: map<int, T> | true {
  predicate Empty() {
    |this| == 0
  }
}

newtype SeqWrapper<T> = x: seq<T> | true {
  predicate Empty() {
    |this| == 0
  }
}

method Main() {
  expect (map[] as MapWrapper<int>).Empty();
  expect !(map[1 := 2] as MapWrapper<int>).Empty();
  expect ([] as SeqWrapper<int>).Empty();
  expect !([1] as SeqWrapper<int>).Empty();
  PrintTwice(TestPrintTwice());
  PrintTwice((TestPrintTwice() as SubSuperTrait));
  PrintTwice((TestPrintTwice() as SuperTrait));
}