// RUN: %exits-with 2 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
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
  function F(): nat
  function G(): Nat

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

  function Pow(b: nat, n: nat): nat {
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

  method Termination0()
  {
    var s := 0;
    for i := 0 to * { // error: * is allowed only if method uses "decreases *"
      s := s + i;
    }
  }

  method Termination1()
  {
    var s := 0;
    for i := 0 downto * { // error: * is allowed only if method uses "decreases *"
      s := s + i;
    }
  }

  method Termination2()
  {
    var s := 0;
    for i := 0 downto *
      decreases * // error: * is allowed only if method uses "decreases *"
    {
      s := s + i;
    }
  }

  method Termination3()
  {
    var s := 0;
    for i := 0 downto * // fine, since there's a decreases clause
      decreases 100 - i
    {
      if i == 20 { break; }
      s := s + i;
    }
  }

  method Termination4()
    decreases *
  {
    var s := 0;
    for i := 0 downto *
      decreases * // fine, since method also says "decreases *"
    {
      s := s + i;
    }
  }

  method Termination5()
    decreases *
  {
    var s := 0;
    for i := 0 downto * { // fine, since method also says "decreases *"
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

  method Char() {
    for ch := 'a' to 'z' { // error: type must be an integer type
    }
    for i := 'a' as int to 'z' as int {
      var ch := i as char;
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
    for _ := 10 downto 0 {
      for _ := 0 to 10 {
      }
    }
  }

  method Nested(i: real, a: array<bool>)
    modifies a
  {
    for i := 0 to a.Length {
      for i := a.Length downto 0 {
        var i := 0;
        while i < a.Length {
          forall i | 0 <= i < a.Length {
            a[i] := i < 27;
          }
          var b := forall i :: 0 <= i < a.Length ==> a[i];
          for i := 0 to a.Length {
          }
        }
      }
    }
  }
} module BodyLessLoops {
  method BodyLessLoop(a: nat, b: nat) {
    for i := a to b // body-less loop
  }

  method BodyLessLoop1(a: nat, b: nat) {
    var x, y := a, b;
    for i := a to b // body-less loop (loop frame: y)
      invariant i <= y
  }

  method BodyLessLoop2(a: nat, b: nat) {
    var arr := new int[25];
    for i := a to b // body-less loop (loop frame: $Heap)
      modifies arr
  }
} module MoreTests {
  method LoopSpecs(a: array<int>, b: array<int>)
    modifies a, b
  {
    // the body of this method resolves, but it wouldn't verify (for several reasons)
    for n := 0 to a.Length
      invariant forall i :: 0 <= i < n ==> old(a[n]) < a[n]
    {
      a[n] := a[n] + 1;
    }
    for n := 0 to a.Length
      invariant forall i :: 0 <= i < n ==> old(a[n]) < a[n]
      modifies a
    {
      for j := 0 to b.Length
        modifies b
      {
      }
      a[n] := a[n] + 1;
    }
  }

  method Breaks(k: int) {
    for i := 0 to 100 {
      if i == 17 {
        break;
      }
    }
    for i := 0 to 100 {
      if i == 17 {
        break break; // error: there aren't two loop levels here
      }
    }
    for i := 0 to 100 {
      for j := 0 to 100 {
        if i == 17 {
          break break;
        }
      }
    }
    for i := 0 to 100 {
      for j := 0 to 100 {
        if i == 17 {
          break break break; // error: there aren't 3 loop levels here
        }
      }
    }
    for i := 0 to 100 {
      var j := 0;
      while j < 100 {
        if i == 17 {
          break break;
        } else if j == k {
          break;
        }
      }
    }
    var m := 0;
    while m < 100 {
      for j := 0 to 100 {
        if m == 17 {
          break break;
        } else if j == k {
          break;
        }
      }
    }
  }

  method BreakLabels(s: seq<int>)
    requires |s| == 1000
  {
    label A:
    for i := 0 to 100 {
      label B:
      label C:
      for j := 100 downto 0 {
        if i == s[0] {
          break A;
        } else if i == s[1] {
          break B;
        } else if i == s[2] {
          break C;
        } else if i == s[20] {
          break D; // error: no label D in scope
        } else if i == s[21] {
          break XYZ; // error: no label XYZ in scope
        }
        var m := 0;
        while m < 100 {
          label D: {
            assert m < 100;
            for i := 0 to 100 {
              if i == s[3] {
                break D;
              } else if i == s[4] {
                break B;
              } else if * {
                break A;
              }
            }
            var u := 25;
            assert m < 4 * u;
            if m == s[5] {
              break D;
            }
          }
          if m == s[6] {
            break D; // error: no label D in scope
          }
          m := m + 1;
        }
      }
    }
  }

  method MoreScopeThings(N: nat) {
    for i := 0 to N {
    }
    assert i == N; // error: i is not in scope
    var i := 0;
    while i < N {
      i := i + 1;
    }
    assert i == N;
    for i := 0 to 3 {
    }
    assert i == N;
  }

  method IllegalBreaks(k: int, ghost g: int) {
    label A: {
      for j := 54 to 56 {
        calc {
          3;
        ==  {
              for i := 0 to 100 {
                if i == 17 {
                  break;
                } else if i == k {
                  break A; // error: label A not in scope
                } else if * {
                  break break; // error: there aren't 2 levels to break out of here
                }
              }
            }
          2 + 1;
        }
      }
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

  method IllegalReturns(k: int, ghost g: int, h: int) {
    label A: {
      calc {
        3;
      ==  {
            for i := 0 to 100 {
              if i == 17 {
                return; // error (x2): cannot return from inside calc hint
              }
            }
          }
        2 + 1;
      }
    }
    for i := 0 to h {
      if i == k {
        return;
      }
    }
    for i := 0 to g {
      return; // error: return not allowed from inside ghost context
    }
  }

  method GhostTermination0(ghost start: int)
    decreases *
  {
    for i := start to * { // error: ghost loop must be terminating
    }
  }

  method GhostTermination1(ghost start: int)
    decreases *
  {
    for i := start to * // error: ghost loop must be terminating
      decreases *
    {
    }
  }

  method GhostTermination2(ghost start: int)
    decreases *
  {
    for i := start to *
      decreases start + 1000 - i
    {
    }
  }

  ghost method GhostTermination3(start: int) {
    for i := start to *
      decreases start + 1000 - i
    {
    }
  }
}
