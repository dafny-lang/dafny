// RUN: ! %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo(x: int) {
  match x {

  }
}

method Baz(x: int) {
  match x {
    case 3 =>
  }
}

function Qar(x: int): int {
  match x {
    case 3 => 3
  }
}

function Bar(x: int): int {
  match x {
  }
}
