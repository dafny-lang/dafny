// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
/* SOON:
method DebunkFermatAndWiles()
  decreases *
{ SOON:
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
*/
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
