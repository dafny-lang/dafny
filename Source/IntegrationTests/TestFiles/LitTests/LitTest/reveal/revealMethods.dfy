// echo ''
// NoRUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// NoRUN: %diff "%s.expect" "%t"

blind method MethodEnsuresAreHidden() {
  // var x := Bar();
  // if (*) {
  //   reveal Bar();
  //   assert x;
  // } else {
  //   assert x; // error
  // }
  // assert x;
}

method Bar() returns (x: bool) 
  ensures x

// Consequence axiom also contains information about subset types of the return types
// Reveals in contracts are fine, but they never escape the contract.

// Add an option 
// TODO what to do with reveals in contracts?
// TODO add test cases that see how blindness interops with contracts of the blind callable
// TODO if a contract has reveals clauses, do they get copied to the caller?