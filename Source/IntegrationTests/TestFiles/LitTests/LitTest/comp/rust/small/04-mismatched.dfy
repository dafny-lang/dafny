// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Super {
  function AsSuper(): Super
  function GetInt(): int
  
  function GetDoubleInt(): int {
    GetInt() * 2
  }
}

datatype Sub extends Super = Sub {
  function AsSuper(): Super {
    this
  }
  function GetInt(): int {
    3
  }
  function Total(): int {
    this.AsSuper().GetInt() + this.GetDoubleInt()
  }
}

method Main() {
  expect Sub().Total() == 9;
}