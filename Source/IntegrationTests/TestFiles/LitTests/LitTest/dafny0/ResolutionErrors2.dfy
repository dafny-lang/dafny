// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// ------------------------- statements in expressions ------------------------------

module StatementsInExpressions {
  class MyClass {
    ghost method SideEffect()
      modifies this
    {
    }

    method NonGhostMethod()
    {
    }

    ghost function F(): int
    {
      calc {
        6;
        { assert 6 < 8; }
        { var x := 8;
          while x != 0
            decreases *  // error: cannot use 'decreases *' here
          {
            x := x - 1;
          }
        }
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        6;
      }
      5
    }

    var MyField: int
    ghost var MyGhostField: int

    method N()
    {
      var y :=
      calc {
        6;
        { assert 6 < 8; }
        { var x := 8;
          while x != 0
            decreases *  // error: cannot use 'decreases *' here
          {
            x := x - 1;
          }
        }
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        6;
      }
      5;
    }
  }
}

module StmtExprOutParams {

  lemma MyLemma()

  lemma OutParamLemma() returns (y: int)

  ghost function UseLemma(): int
  {
    MyLemma();
    OutParamLemma(); // error: has out-parameters
    10
  }
}

module GhostLetExpr {
  method M() {
    ghost var y;
    var x;
    var g := G(x, y);
    ghost var h := ghost var ta := F(); 5;
    var j; j := var tb := F(); 5;  // fine (tb is ghost, j is not, but RHS body doesn't depend on tb)
    assert h == j;
  }

  ghost function F(): int {
    5
  }

  function G(x: int, ghost y: int): int {
    assert y == x;
    y  // error: not allowed in non-ghost context
  }

  datatype Dt = MyRecord(a: int, ghost b: int)

  method P(dt: Dt) {
    match dt {
      case MyRecord(aa, bb) =>
        ghost var z := aa + F();
        ghost var t0 := var y := z; z + 3;
        ghost var t1 := ghost var y := z + bb; y + z + 3;
        var t2; t2 := ghost var y := z; y + 3;  // t2 is not ghost - error
    }
  }

  function FM(e: bool): int {
    if e then
      G(5, F())
    else
      var xyz := F();  // fine, because 'xyz' becomes ghost automatically
      G(5, xyz)
  }
}

module ObjectType {
  type B
  datatype Dt = Blue | Green
  codatatype CoDt = Cons(int, CoDt)
  class MyClass { }

  method M<G>(zz: array<B>, j: int, b: B, co: CoDt, g: G) returns (o: object)
    requires zz != null && 0 <= j < zz.Length
  {
    o := b;  // error
    o := 17;  // error
    o := zz[j];  // error
    o := null;
    o := zz;
    o := new MyClass;
    o := o;
    o := g;  // error
    o := Blue;  // error
    o := co;  // error
  }
}

// ------------------ modify statment ---------------------------

module MiscModify {
  class ModifyStatementClass {
    var x: int
    ghost var g: int
    method M() {
      modify x;  // error: type error
    }
  }
}

module MiscModifiesGhost {
  class ModifyStatementClass {
    var x: int
    ghost var g: int
    ghost method G0()
      modifies `g
      modifies `x  // error: non-ghost field mentioned in ghost context
  }
}

module ModifyStatementClass_More {
  class C {
    var x: int
    ghost var g: int

    ghost method G0()
      modifies `g
    {
      modify `g;
      modify `x;  // error: non-ghost field mentioned in ghost context
    }

    method G1()
      modifies this
    {
      modify `x;
      if g < 100 {
        // we are now in a ghost context
        modify `x;  // error: non-ghost field mentioned in ghost context
      }
    }

    method G2(y: nat)
      modifies this
    {
      if g < 100 {
        // we're now in a ghost context
        var n := 0;
        while n < y
          modifies `x  // error: non-ghost field mentioned in ghost context
        {
          if * {
            g := g + 1;  // if we got as far as verification, this would be flagged as an error too
          }
          n := n + 1;
        }
      }
      modify `x;  // fine

      ghost var i := 0;
      while i < y
        modifies `x  // error: non-ghost field mentioned in ghost context
      {
        i := i + 1;
      }
    }
  }
}

module LhsLvalue {
  datatype MyRecord = Make(x: int, y: int)

  method MyMethod() returns (w: int)

  method M0() returns (mySeq: seq<int>) {
    mySeq[0] := 5;  // error: cannot assign to a sequence element
  }

  method M1() returns (mySeq: seq<int>) {
    mySeq[0] := MyMethod();  // error: cannot assign to a sequence element
  }

  method M2() returns (mySeq: seq<int>) {
    mySeq[0..4] := 5;  // error: cannot assign to a range
  }

  method M3() returns (mySeq: seq<int>) {
    mySeq[0..4] := MyMethod();  // error: cannot assign to a range
  }

  method M()
  {
    var mySeq: seq<int>;
    var a := new int[78];
    var b := new int[100, 200];
    var c := new MyRecord[29];

    a[0] := 5;
    a[0] := MyMethod();
    b[20, 18] := 5;
    b[20, 18] := MyMethod();
    c[25].x := 5;  // error: cannot assign to a destructor
    c[25].x := MyMethod();  // error: ditto
    a[0..4] := 5;  // error: cannot assign to a range
    a[0..4] := MyMethod();  // error: ditto
  }
}

// ------------------- dirty loops -------------------

module MiscEtc {
  method DirtyM(S: set<int>) {
    forall s | s in S ensures s < 0
    assert s < 0; // error: s is unresolved
  }

  // ------------------- tuples -------------------

  method TupleResolution(x: int, y: int, r: real)
  {
    var unit: () := ();
    var expr: int := (x);
    var pair: (int,int) := (x, x);
    var triple: (int,int,int) := (y, x, x);
    var badTriple: (int,real,int) := (y, x, r);  // error: parameters 1 and 2 have the wrong types
    var quadruple: (int,real,int,real) := (y, r, x);  // error: trying to use a triple as a quadruple

    assert unit == ();
    assert pair.0 == pair.1;
    assert triple.2 == x;

    assert triple.2;  // error: 2 has type int, not the expected bool
    assert triple.3 == pair.x;  // error(s):  3 and x are not destructors

    var k0 := (5, (true, 2, 3.14));
    var k1 := (((false, 10, 2.7)), 100, 120);
    if k0.1 == k1.0 {
      assert false;
    } else if k0.1.1 < k1.0.1 {
      assert k1.2 == 120;
    }

    // int and (int) are the same type (i.e., there are no 1-tuples)
    var pp: (int) := x;
    var qq: int := pp;
  }

  // ------------------- conversions -------------------

  method TypeConversions(m: nat, i: int, r: real) returns (n: nat, j: int, s: real)
  {
    n := r as int;
    j := r as int;
    s := m as real;  // nat->real is allowed, just like int->real is
    s := i as real;
    s := i as real / 2;  // error: division expects two reals
    s := 15 % s;  // error: modulus is not defined for reals

    s := (2.0 / 1.7) + (r / s) - (--r) * -12.3;

    s := s as real;  // fine (identity transform)
    j := j as int;  // fine (identity transform)
    j := n as int;  // fine (identity transform)
  }
}

// --- filling in type arguments and checking that there aren't too many ---

module TypeArgumentCount {
  class C<T> {
    var f: T
  }

  method R0(a: array3, c: C)

  method R1()
  {
    var a: array3;
    var c: C;
  }

  method R2<T>()
  {
    var a: array3<T,int>;  // error: too many type arguments
    var c: C<T,int>;  // error: too many type arguments
  }
}

// --- Type synonyms ---

module BadTypeSynonyms {
  datatype List<T> = Nil | Cons(T, List)
  type BadSyn0 = List  // error: must have at least one type parameter
  type BadSyn1 = badName  // error: badName does not denote a type
  type BadSyn2 = List<X>  // error: X does not denote a type
  type BadSyn2 = int  // error: repeated name
}

// --- cycles ---

module CycleError0 {
  type A = A  // error: cycle: A -> A
}

module CycleError1 {
  type A = B  // error: cycle: A -> B -> A
  type B = A
}

module CycleError2 {
  type A = B  // error: cycle: A -> B -> A
  type B = set<A>
}

module CycleErrors3 {
  type A = (B, D<bool>)
  type B = C
  class C { // error: since A is not auto-init, class C needs a constructor
    var a: A  // this is fine
  }
  datatype D<X> = Make(A, B, C)  // warning: D<X> is empty
}

module CycleError4 {
  type A = B  // error: cycle: A -> B -> A
  type B = C<A>
  class C<T> { }
}

module CycleError5 {
  type A = B  // error: cycle: A -> B -> A
  type B = Dt<A>
  datatype Dt<T> = Make(T)
}

module CycleError6 {
  type A = Dt<Dt<A>>  // error: cycle A -> A
  datatype Dt<T> = Make(T)
}

// --- attributes in top-level declarations ---

module MiscIterator {
  iterator {:myAttribute x} Iter() {  // error: x does not refer to anything
  }

  class {:myAttribute x} C {  // error: x does not refer to anything
  }

  datatype {:myAttribute x} Dt = Blue  // error: x does not refer to anything

  type {:myAttribute x} Something  // error: x does not refer to anything

  type {:myAttribute x} Synonym = int  // error: x does not refer to anything
}

module {:myAttribute x} Modulette {  // error: x does not refer to anything
}

// --- abstract types with type parameters ---

module OpaqueTypes0 {
  type P<AA>
  method M<B>(p: P<B>) returns (q: P<B,B>)  // error: wrong param count
  {
    q := p;
  }
}

module OpaqueTypes1 {
  type P<A>

  method M0<B>(p: P<B>) returns (q: P<B>)
  {
    q := p;
    var m: P<BX>;  // error: BX undefined
  }

  method M1<B>(p: P<B>) returns (q: P)  // type parameter of q's type inferred
  {
    q := p;
  }

  method M2(p: P<int>) returns (q: P<bool>)
  {
    q := p;  // error: cannot assign P<bool> to P<int>
  }

  method M3<A,B>(p: P<A>) returns (q: P<B>)
  {
    q := p;  // error: cannot assign P<A> to P<B>
  }

  method M4<A>() returns (p: P<A>, q: P<int>)
  {
    q := p;  // error: cannot assign P<A> to P<int>
    p := q;  // error: cannot assign P<int> to P<A>
  }

  method EqualityTests<X>(p: P<int>, q: P<bool>, r: P<X>)
  {
    assert p != r;  // error: types must be the same in order to do compare
    assert q != r;  // error: types must be the same in order to do compare
    assert p != q;  // error: types must be the same in order to do compare
  }
}

// ----- new trait -------------------------------------------

module MiscTrait {
  trait J { }
  type JJ = J
  method TraitSynonym()
  {
    var x := new JJ;  // error: new cannot be applied to a trait
  }
}

// ----- set comprehensions where the term type is finite -----

module ObjectSetComprehensionsNever {
  // the following set comprehensions are known to be finite
  ghost function A() : set<object> { set o : object | true :: o }  // error: a function is not allowed to depend on the allocated state
  function B() : set<object> { set o : object | true :: o }  // error: a function is not allowed to depend on the allocated state
}

module ObjectSetComprehensionsSometimes {
  // outside functions, the comprehension is permitted, but it cannot be compiled
  lemma C() { var x; x := set o : object | true :: o; }

  method D() { var x; x := set o : object | true :: o; }  // error: not (easily) compilable, so this is allowed only in ghost contexts
}

// ------ regression test for type checking of integer division -----

module MiscTests {
  method IntegerDivision(s: set<bool>)
  {
    var t := s / s;  // error: / cannot be used with sets
  }

  // ----- decreases * tests ----

  method NonTermination_A()
  {
    NonTermination_B();  // error: to call a non-terminating method, the caller must be marked 'decreases *'
  }

  method NonTermination_B()
    decreases *
  {
    while true
      decreases *
    {
    }
  }

  method NonTermination_C()
  {
    while true
      decreases *  // error: to use an infinite loop, the enclosing method must be marked 'decreases *'
    {
    }
  }

  method NonTermination_D()
    decreases *
  {
    var n := 0;
    while n < 100  // note, no 'decreases *' here, even if the nested loop may fail to terminate
    {
      while *
        decreases *
      {
      }
      n := n + 1;
    }
  }
}
