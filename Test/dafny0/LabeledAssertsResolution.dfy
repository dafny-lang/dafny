// RUN: %exits-with 2 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ResolutionTests {
  lemma A(b: bool, m: int, n: int)
    requires m < n
    requires sea: m + 3 < n
    requires sjc: m + 5 < n
    requires sjc: m + 7 < n  // error: dominating label
    requires jfk: m + 9 < n
    requires m < n
  {
    label a: assert true;
    if b {
      label x: assert true;
      label K: assert {:myAttr 30} m < n;
      label L: assert {:myAttr 30} m < n;
      label 0: assert {:myAttr 30} m < n;
      label 0: assert {:myAttr 30} m < n;  // error: dominating label
      label jfk: assert true;  // error: dominating label
    } else {
      label x: assert true;
      assert {:myAttr 30} K: m < n;
      assert {:myAttr 30} L: m < n;
      assert {:myAttr 30} 0: m < n;
      assert {:myAttr 30} 0: m < n;  // error: dominating label
      var x: int;
      assert jfk: true;  // error: dominating label
      assert old(b) == old@a(b) == old@x(b);
    }
    assert 0010: m < n;
    assert {:myAttr 30} K: m < n;
    label L:
    assert {:myAttr 30} L: m < n;  // error: dominating label
    assert old(b) == old@a(b);
    assert old(b) == old@sjc(b);
    // var r := assert NotAllowedHere: 0 <= m; 10;  // not allowed; won't parse
  }

  function R(u: int): int
    // requires i: 0 <= u  // not allowed; won't parse
  {
    // assert NotAllowedHere: 0 <= u;  // not allowed; won't parse
    u
  }

  iterator Iter(x: int) yields (y: int)
    requires A: 0 <= x
    // yield requires B: 0 <= y  // not allowed; won't parse
  {
    assert C: 0 <= x < |ys|;
    assert A: 0 <= x < |ys|;  // error: dominating label
    yield;
    assert C: 0 <= x < |ys|;  // error: dominating label
  }

  twostate predicate Twop(x: int)
    // requires A: 0 <= x  // not allowed; won't parse
  {
    true
  }

  twostate lemma Twol(x: int)
    requires A: 0 <= x
  {
  }

  lemma Calc(x: int)
    requires A: x < 10
  {
    assert B: x < 150 by { reveal A; }
    label QRS: assert TUV: x < 10 by {
      break ABC;  // error: a break is not allowed to leave the proof body
      reveal A;
    }

    calc {
      x < 200;
    ==  { reveal B;
          label XYZ:
          reveal C;  // error: C is not dominated here
          assert old@XYZ(x) == x;
        }
      x < 150;
    ==  { assert C: x < 90 by { reveal A; }
          reveal C;
        }
      x < 102;
    ==  { assert C: x < 90 by { reveal A; }  // it's okay to have another C here
        }
      x < 100;
    ==  { reveal A;}
      x < 10;
    ==  { assert old@XYZ(x) == x; }  // error: XYZ is not in scope here
      x < 100;
    ==
      { label ABC: assert DEF: x < 10 by { reveal A; } }
      { label ABC: assert DEF: x < 10 by { reveal A; } }
      x < 100;
    }
  }

  class C {
    var g: int
    var h: int
  }

  twostate lemma T3(c: C)
    requires old(c.g) == 10
    requires c.g == 20
    requires A: old(c.h) == 100
    requires B: c.h == 200
  {
    reveal A, B, A, A;  // this can be a list
    reveal A, X, A, A;  // error: C not defined
  }

}  // module ResolutionTests

module GitIssue408 {
  method Test() {
    ghost var x := 5;
    assert x == 6 by {
      // regression test: the following had once been unchecked:
      x := 6;  // error: x is declared outside the assert-by block
    }
    assert x == 5; // This would be provable if the assignment to x above were allowed.
    assert false;  // And then this assertion, too.
  }

  method MoreTests() {
    ghost var x := 5;
    var y := 9;
    assert x == 6 by {
      var u := 10;  // in this ghost context, every local variable is effectively ghost
      u := u + 1;  // this is fine, since u is declared in the assert-by block
      ghost var v := 10;
      v := v + x + 1;  // this is also fine, since v is declared in the assert-by block
      y := 8;  // error: y is non-ghost (and is declared outside the assert-by block)
    }
  }

  class C {
    ghost var data: real
  }

  datatype Record = Record(x: int, y: int)
  method GetRecord(c: C)
    modifies c
  {
    c.data := 21.0;
  }

  ghost method Six() returns (x: int) {
    x := 6;
  }

  method Nesting(c: C, a: array<real>, m: array2<real>)
    requires a.Length != 0 && m.Length0 == m.Length1 == 100
    modifies c, a, m
  {
    ghost var x := 5;

    assert 2 < 10 by {
      var y := 9;
      assert 2 < 11 by {
        var u := 11;
        u := 20;
        x := 20;  // error: x is declared outside this assert-by block
        x := Six();  // error (x2): x is declared outside this assert-by block, and Six is a ghost method
        y := 20;  // error: y is declared outside this assert-by block
        c.data := 20.0;  // error: assert-by cannot modify heap locations
        a[0] := 20.0;  // error: assert-by cannot modify heap locations
        m[0,0] := 20.0;  // error: assert-by cannot modify heap locations
        modify c;  // error: assert-by cannot modify heap locations
      }
      c.data := 20.0;  // error: assert-by cannot modify heap locations
      a[0] := 20.0;  // error: assert-by cannot modify heap locations
      m[0,0] := 20.0;  // error: assert-by cannot modify heap locations
      modify c;  // error: assert-by cannot modify heap locations
    }

    calc {
      5;
    ==  { x := 10; }  // error: x is declared outside the hint
      5;
    ==  { c.data := 20.0;  // error: hint cannot modify heap locations
          a[0] := 20.0;  // error: hint cannot modify heap locations
          m[0,0] := 20.0;  // error: hint cannot modify heap locations
          modify c;  // error: hint cannot modify heap locations
        }
      5;
    ==  { var y := 9;
          y := 10;
          x := Six();  // error (x2): x is declared outside this hint, and Six is a ghost method
          assert 2 < 12 by {
            var u := 11;
            u := 20;
            x := 6;  // error: x is declared outside this assert-by block
            y := 11;  // error: y is declared outside this assert-by block
            calc {
              19;
            ==  { y := 13;  // error: y is declared outside the hint
                  u := 21;  // error: u is declared outside the hint
                }
              19;
            }
          }
          y := 12;
        }
      5;
    }

    forall f | 0 <= f < 82
      ensures f < 100
    {
      var y := 9;
      assert 2 < 4 by {
        x := 6;  // error: x is declared outside the assert-by statement
        y := 11;  // error: y is declared outside the assert-by statement
      }
      var rr := (calc { 5; =={ return; /*error: return not allowed in hint*/ } 5; } Record(6, 8));
      var Record(xx, yy) := (calc { 5; =={ return; /*error: return not allowed in hint*/ } 5; } Record(6, 8));
    }
  }

  method Return() {
    label A: {
      while true {
        calc {
          5;
        ==  { return; }  // error: return not allowed in hint
          5;
        }

        assert 2 < 3 by {
          return;  // error: return not allowed in assert-by
        }
      }
    }
  }

  iterator Iter() {
    calc {
      5;
    ==  { yield; }  // error: yield not allowed in hint
      5;
    }

    assert 2 < 3 by {
      yield;  // error: yield not allowed in assert-by
    }
  }
}

module ForallStmtTests {
  // it so happens that forall statements are checked separately from hints in
  // the Resolver, so we use a separate module for these tests to avoid having
  // these errors shadow the others

  class C {
    ghost var data: real
  }

  datatype Record = Record(x: int, y: int)
  method GetRecord(c: C)
    modifies c
  {
    c.data := 21.0;
  }

  ghost method Six() returns (x: int) {
    x := 6;
  }

  method Forall(c: C, a: array<real>, m: array2<real>) {
    ghost var x := 5;

    forall f | 0 <= f < 82
      ensures f < 100
    {
      var y := 9;
      x := 6;  // error: x is declared outside forall statement
      x := Six();  // error: x is declared outside forall statement
    }
  }

  method Nested(c: C, a: array<real>, m: array2<real>) {
    ghost var x := 5;

    forall f | 0 <= f < 82
      ensures f < 100
    {
      var y := 9;
      assert 2 < 4 by {
        var w := 18;
        forall u | 0 <= u < w {
          x := 6;  // error: x is declared outside the forall statement
          y := 12;  // error: y is declared outside the forall statement
          w := 19;  // error: w is declared outside the forall statement
        }
      }
    }
  }

  method Return() {
    forall f | 0 <= f < 82
      ensures f < 100
    {
      return;  // error: return not allowed in forall statement
    }
  }

  iterator Iter() {
    forall f | 0 <= f < 82
      ensures f < 100
    {
      yield;  // error: yield not allowed in forall statement
    }
  }
}

module Breaks {
  method Break() {
    label A: {
      while true {
        calc {
          5;
        ==  { break; }  // error: break not allowed in hint
          5;
        ==  { break A; }  // error: break not allowed in hint
          5;
        }

        assert 2 < 3 by {
          break;  // error: break not allowed in assert-by
          break A;  // error: break not allowed in assert-by
        }

        forall f | 0 <= f < 82
          ensures f < 100
        {
          break;  // error: break not allowed in forall statement
          break A;  // error: break not allowed in forall statement
        }
      }
    }
  }
}

module OddExpressionChecks {
  type Odd = x |
    var rr :=
      assert 2 < 23 by {
        return;  // error: return not allowed in assert-by
      }
      2;
    x % rr == 1
    witness
      var ww :=
        assert 2 < 23 by {
          return;  // error: return not allowed in assert-by
        }
        2;
      ww + 7

  newtype NewOdd = x |
    var rr :=
      assert 2 < 23 by {
        return;  // error: return not allowed in assert-by
      }
      2;
    x % rr == 1
    ghost witness
      var ww :=
        assert 2 < 23 by {
          return;  // error: return not allowed in assert-by
        }
        2;
      ww + 7
}

module MoreGhostTests {
  class C {
    ghost var data: real
  }

  ghost method Six() returns (x: int) {
    x := 6;
  }

  method Forall(c: C, a: array<real>, m: array2<real>) {
    ghost var x := 5;

    forall f | 0 <= f < 82
      ensures f < 100
    {
      var y := 9;
      c.data := 20.0;  // error: proof-forall statement cannot modify heap locations
      a[0] := 20.0;  // error: proof-forall statement cannot modify heap locations
      m[0,0] := 20.0;  // error: proof-forall statement cannot modify heap locations
      modify c;  // error: proof-forall cannot modify heap locations
    }
  }
}
