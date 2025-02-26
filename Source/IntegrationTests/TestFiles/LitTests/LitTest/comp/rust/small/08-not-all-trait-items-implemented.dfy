// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows

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


trait Singleton<G(!new)> {
    function id():G       
}


trait A<G(!new),T(!new)> {
    function g():Singleton<G>
}


trait F<V(!new)> extends A<int,V> {
    function g():Singleton<int> { Zero }
}

datatype Zero extends Singleton<int> = Zero {
  function id(): int { 0 }
}

datatype C extends F<int> = C {
}

trait RequiresEquality<S(==),T> {
}
datatype TraitExtender<S> extends RequiresEquality<S,seq<S>> = TraitExtender {}

method Main() {
  var x := Pong;
  expect x.reverse() is Ping;
  expect Ping().reverse() is Pong;
  print "ping pong";
}