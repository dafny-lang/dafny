// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Super<!K,D> {
    function get(d:D,ks:K):(r:int)
}
datatype ZeroComputation = ZeroComputation {
  function top(): int { 0 }
}
 
datatype ComputationWrapper<!K(==,!new)> extends Super<K,K> = ComputationWrapper {
  function Computation_():ZeroComputation { ZeroComputation }
  const computation := Computation_()
  function get(d:K,ks:K):(r:int) {
      computation.top()
  }
  function Copy(): ComputationWrapper<K> {
    this
  }
  function AsSuper(): Super<K, K> {
    this as Super<K,K>
  }
}

method Main() {
  expect ComputationWrapper<int>.ComputationWrapper().Copy().get(1, 2) == 0;
  print "ok";
}