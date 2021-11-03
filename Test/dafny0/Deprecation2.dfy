// RUN: %dafny /compile:3 /deprecation:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains tests for messages about various /deprecation:2 features.
// As those features go away completely, so can the corresponding tests.

method Main() {
  // Test that we get all the way to compilation, despite the deprecation warnings below
  print "yet here we are\n";
}

// ----------

class C {
  var data: int; // deprecation warning: ";"
  const N: int; // deprecation warning: ";"

  method M(n: nat)
    requires true; // deprecation warning: ";"
    modifies this; // deprecation warning: ";"
    ensures true; // deprecation warning: ";"
    decreases n; // deprecation warning: ";"
  {
    if n != 0 {
      for i := 1 to n
        invariant 0 <= i <= n; // deprecation warning: ";"
      {
        M(i - 1);
      }
    }
  }

  function F(n: nat): nat
    requires true; // deprecation warning: ";"
    reads this; // deprecation warning: ";"
    ensures true; // deprecation warning: ";"
    decreases n; // deprecation warning: ";"
  {
    if n == 0 then 0 else F(n - 1)
  }
}

// ----------

function method F(): int { 5 } // deprecation warning: "function method" is now "compiled function"

predicate method P() { true } // deprecation warning: "predicate method" is now "compiled predicate"

compiled function F'(): int { 5 }

compiled predicate P'() { true }
