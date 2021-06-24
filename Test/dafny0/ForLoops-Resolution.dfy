// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  method M0() {
    for i := 0 to i + 1 {  // error: i is not in scope
    }
  }

  method M1() {
    for i := i + 1 to 100 {  // error: i is not in scope
    }
  }

  method M2(i: int) {
    for i := i to i + 3 {
    }
  }

  newtype Nat = x | 0 <= x
  function method F(): nat
  function method G(): Nat

  method P0(x: int) returns (r: nat) {
    for i := F() to 5 {
      r := i;
    }
  }

  method P1(x: int) returns (r: nat) {
    for i := G() to 5 {
      r := i; // error: cannot assign Nat to nat
    }
  }

  method P2(x: int) returns (r: Nat) {
    for i := F() to 5 {
      r := i; // error: cannot assign nat to Nat
    }
  }

  method P3(x: int) returns (r: Nat) {
    for i := G() to 5 {
      r := i;
    }
  }

  method P4(x: int) returns (r: Nat) {
    for i := 0 to 5 {
      r := i;
    }
  }

  function method Pow(b: nat, n: nat): nat {
    if n == 0 then 1 else b * Pow(b, n - 1)
  }

  method DebunkFermatAndWiles()
    decreases *
  {
    for i := 1 to * {
      for j := 1 to i {
        for k := 1 to i {
          for n := 3 to i {
            if Pow(i, n) + Pow(j, n) == Pow(k, n) {
              print "By golly, Fermat and Wiles were wrong!\n";
              return;
            }
          }
        }
      }
    }
  }

  method TerminationProblem0()
  {
    var s := 0;
    for i := 0 to * { // error: * is allowed only if method uses "modifies *"
      s := s + i;
    }
  }

  method TerminationProblem1()
  {
    var s := 0;
    for i := 0 downto * { // error: * is allowed only if method uses "modifies *"
      s := s + i;
    }
  }

  method Real() {
    for i := 0.0 to 10.0 { // error (x2): type must be an integer type
    }
  }

  method RealExplicit() {
    for i: real := 0.0 to 10.0 { // error: index-variable type must be an integer type
    }
  }

  method RealExplicit'() {
    for i: real := 0 to 10.0 { // error (x2): index-variable type must be an integer type; int not assignable to real
    }
  }

  method Bitvector() {
    for i := 0 as bv8 to 20 { // error: type must be an integer type
    }
  }

  method BigOrdinal() {
    for i := 0 to 1000 as ORDINAL { // error: type must be an integer type
    }
  }

  method Mutation() {
    for i := 0 to 1000 {
      i := i + 3;  // error: i is not mutable
    }
  }

  method Wild() {
    for _ := 0 to 10 {
    }
  }
}

module Ghosts {
  class C {
    ghost var g: int
    var h: int
  }

  method GhostIf0(c: C, b0: bool, ghost b1: bool)
    modifies c
  {
    if b0 {
      c.g := 68;
    }
    if b1 { // this is a ghost statement
      c.g := 68;
    }
  }

  method GhostIf1(c: C, b0: bool, ghost b1: bool)
    modifies c
  {
    if b0 {
      c.h := 68;
    }
    if b1 { // this is a ghost statement
      c.h := 68; // error: cannot assign compiled field in ghost statement
    }
  }

  method GhostForall0(s: set<C>, ghost t: set<C>)
    modifies s, t
  {
    forall c | c in s {
      c.g := 68;
    }
    forall c | c in t { // this is a ghost statement
      c.g := 68;
    }
  }

  method GhostForall1(s: set<C>, ghost t: set<C>)
    modifies s, t
  {
    forall c | c in s {
      c.h := 68;
    }
    forall c | c in t { // this is a ghost statement
      c.h := 68; // error: cannot assign compiled field in ghost statement
    }
  }

  method GhostForLoop0(c: C, x: nat, ghost y: nat)
    modifies c
  {
    for i := 0 to x {
      c.g := 68;
    }
    for i := 0 to y { // this is a ghost statement
      c.g := 68;
    }
  }

  method GhostForLoop1(c: C, x: nat, ghost y: nat)
    modifies c
  {
    for i := 0 to x {
      c.h := 68;
    }
    for i := 0 to y { // this is a ghost statement
      c.h := 68; // error: cannot assign compiled field in ghost statement
    }
  }

  method GhostForLoop2(c: C, x: nat, ghost y: nat)
    requires x <= 100 && y <= 100
    modifies c
  {
    for i := x to 100 {
      c.h := 68;
    }
    for i := y to 100 { // this is a ghost statement
      c.h := 68; // error: cannot assign compiled field in ghost statement
    }
  }

  method GhostForLoop3(c: C, x: nat, ghost y: nat)
    modifies c
  {
    for i := x downto 0 {
      c.h := 68;
    }
    for i := y downto 0 { // this is a ghost statement
      c.h := 68; // error: cannot assign compiled field in ghost statement
    }
  }

  method GhostForLoop4(c: C, x: nat, ghost y: nat) returns (ghost r: int)
    modifies c
  {
    for i := x downto 0 {
      r := i;
    }
    for i := y downto 0 { // this is a ghost statement
      r := i;
    }
  }

  method GhostForLoop5(c: C, x: nat, ghost y: nat) returns (r: int)
    modifies c
  {
    for i := x downto 0 {
      r := i;
    }
    for i := y downto 0 { // this is a ghost statement
      r := i; // error: cannot assign compiled field in ghost statement
    }
  }
}
