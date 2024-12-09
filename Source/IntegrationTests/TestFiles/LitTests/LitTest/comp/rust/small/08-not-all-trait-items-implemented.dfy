// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --emit-uncompilable-code --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Reversible {
  function reverse():(r:Reversible)
}

trait SubReversible extends Reversible {
    function reverse():(r:Reversible)
}

datatype {:rust_rc false} Ping extends Reversible, SubReversible = Ping {
    function reverse():(r:Reversible) { Pong }
}

datatype {:rust_rc false} Pong extends Reversible, SubReversible = Pong {
  function reverse():(r:Reversible) { Ping }
}


method Main() {
  var x := Pong;
  expect x.reverse() is Ping;
  expect Ping().reverse() is Pong;
  print "ping pong";
}