// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --allow-axioms


// ----- constructor-less classes with need for initialization -----

module ConstructorlessClasses {
  class C<T(==)> {  // error: must have constructor
    var x: int
    var s: string
    var t: set<T>
    var u: T
    const c: T
  }

  method Test()
  {
    var c := new C<set<real>>;
    print "int: ", c.x, "\n";
    print "string: ", c.s, "\n";
    print "set<set<real>>: ", c.t, "\n";
    print "real: ", c.u, "\n";
    print "real: ", c.c, "\n";
  }

  codatatype Co<X> = Suc(Co<seq<X>>)  // does not know a known compilable value
  codatatype Co2 = CoEnd | CoSuc(Co2)

  trait Trait {
    var co: Co<int>  // has no known initializer
  }

  class Class extends Trait {  // error: must have constructor, because of inherited field "co"
  }

  class CoClass0 {  // error: must have constructor
    const co: Co<int>
  }

  class CoClass1 {  // fine
    const co: Co2 := CoEnd
  }

  trait CoTrait {
    const co: Co2 := CoEnd
  }

  class CoClass2 extends CoTrait {  // fine
  }

  iterator Iter<T>(u: T) yields (v: T)
  {
  }
}

module GhostWitness {
  type BadGhost_EffectlessArrow<A,B> = f: A -> B
    | true
    witness (GhostEffectlessArrowWitness<A,B>)  // error: a ghost witness must use the keyword "ghost"

  type GoodGhost_EffectlessArrow<A,B> = f: A -> B
    | true
    ghost witness (GhostEffectlessArrowWitness<A,B>)

  ghost function GhostEffectlessArrowWitness<A,B>(a: A): B
  {
    var b: B :| true; b
  }
}

module BigOrdinalRestrictions {  // also see BigOrdinalRestrictionsExtremePred below
  method Test() {
    var st: set<ORDINAL>;  // error: cannot use ORDINAL as type argument
    var p: (int, ORDINAL);  // error: cannot use ORDINAL as type argument
    var o: ORDINAL;  // okay
    ghost var f := F(o);  // error: cannot use ORDINAL as type argument
    f := F'<ORDINAL>();  // error: cannot use ORDINAL as type argument
    f := F'<(char,ORDINAL)>();  // error: cannot use ORDINAL as type argument
    var lambda := F'<ORDINAL>;  // error: cannot use ORDINAL as type argument
    ParameterizedMethod(o);  // error: cannot use ORDINAL as type argument
    assert forall r: ORDINAL :: P(r);
    assert forall r: (ORDINAL, int) :: F(r.1) < 8;
    assert exists x: int, r: ORDINAL, y: char :: P(r) && F(x) == F(y);
    var s := set r: ORDINAL | r in {};  // error: cannot use ORDINAL as type argument (to set)
    var s' := set r: ORDINAL | true :: 'G';
    ghost var m := imap r: ORDINAL :: 10;
    var sq := [o, o];  // error: cannot use ORDINAL as type argument (to seq)
    var mp0 := map[o := 'G'];  // error: cannot use ORDINAL as type argument (to map)
    var mp1 := map['G' := o];  // error: cannot use ORDINAL as type argument (to map)
    var w := var h: ORDINAL := 100; h + 40;  // okay
    var w': (int, ORDINAL);  // error: cannot use ORDINAL as type argument
    var u: ORDINAL :| u == 15;
    var ti: ORDINAL :| assume true;
    var u': (ORDINAL, int) :| u' == (15, 15);  // error (x2): ORDINAL cannot be a type argument
    var ti': (ORDINAL, ORDINAL) :| assume true;  // error (x4): ORDINAL cannot be a type argument
    var lstLocal := var lst: ORDINAL :| lst == 15; lst;
    var lstLocal' := var lst: (ORDINAL, int) :| lst == (15, 15); lst.1;  // error: ORDINAL cannot be a type argument

    if yt: ORDINAL :| yt == 16 {
      ghost var pg := P(yt);
    }

    if {
      case zt: ORDINAL :| zt == 180 =>
        ghost var pg := P(zt);
    }

    forall om: ORDINAL  // allowed
      ensures om < om+1
    {
    }

    var arr := new int[23];
    forall om: ORDINAL | om == 11  // allowed
    {
      arr[0] := 0;
    }
  }

  ghost function F<G>(g: G): int
  ghost function F'<G>(): int
  method ParameterizedMethod<G>(g: G)
  ghost predicate P(g: ORDINAL)
}

module IteratorDuplicateParameterNames {
  // each of the following once caused a crash in the resolver
  iterator MyIterX(u: char) yields (u: char)  // error: duplicate name "u"
  iterator MyIterY(us: char) yields (u: char)  // error: in-effect-duplicate name "us"
}

module TernaryTypeCheckinngAndInference {
  codatatype Stream = Cons(int, Stream)

  method M(k: nat, K: ORDINAL, A: Stream, B: Stream)
    requires A == B
  {
    // all of the following are fine
    assert A ==#[k] B;
    assert A ==#[K] B;
    assert A ==#[3] B;
    var b;
    assert A ==#[b] B;
  }
}

module DontQualifyWithNonNullTypeWhenYouMeanAClass {
  module Z {
    class MyClass {
      static const g := 100
    }

    method M0() {
      var x := MyClass?.g;  // error: use MyClass, not MyClass?
      assert x == 100;
    }

    method M1() {
      var x := MyClass.g;  // that's it!
      assert x == 100;
    }

    method P(from: MyClass) returns (to: MyClass?) {
      to := from;
    }

    method Q() {
      var x := MyClass;  // error: type used as variable
      var y := MyClass?;  // error: type used as variable
    }
  }

  module A {
    class MyClass {
      static const g := 100
    }
  }

  module B {
    import A

    method M0() {
      var x := A.MyClass?.g;  // error: use MyClass, not MyClass?
      assert x == 100;
    }

    method M1() {
      var x := A.MyClass.g;  // that's it!
      assert x == 100;
    }

    method P(from: A.MyClass) returns (to: A.MyClass?) {
      to := from;
    }

    method Q() {
      var x := A.MyClass;  // error: type used as variable
      var y := A.MyClass?;  // error: type used as variable
    }
  }
}

module UninterpretedModuleLevelConst {
  type Six = x | 6 <= x witness 6
  type Odd = x | x % 2 == 1 ghost witness 7
  const S: Six  // fine
  const X: Odd  // error: the type of a non-ghost static const must have a known initializer

  class MyClass { }
  const Y: MyClass  // error: the type of a non-ghost static const must have a known (non-ghost) initializer
  ghost const Y': MyClass  // error: the type of a ghost static const must be known to be nonempty

  class AnotherClass {  // fine, the class itself is not required to have a constructor, because the bad fields are static
    static const k := 18
    static const W: MyClass  // error: the type of a non-ghost static const must have a known (non-ghost) initializer
    static const U: Six  // fine, since Six has a non-ghost witness and thus has a known initializer
    static const O: Odd  // error: the type of a non-ghost static const must have a known initializer
    const u: Six
  }

  trait Trait {
    static const k := 18
    static const W: MyClass  // error: the type of a non-ghost static const must have a known (non-ghost) initializer
    static const U: Six  // fine, since Six has a non-ghost witness and thus has a known initializer
    static const O: Odd  // error: the type of a non-ghost static const must have a known initializer
  }

  class ClassyTrait extends Trait {  // fine, since the bad fields in Trait are static
  }

  trait InstanceConst extends object {
    const w: MyClass
  }

  class Instance extends InstanceConst {  // error: because of "w", must declare a constructor
  }

  trait GhostTr extends object {
    ghost const w: MyClass  // the responsibility to initialize "w" lies with any class that implements "GhostTr"
  }

  class GhostCl extends GhostTr {  // error: w and z need initialization, so GhostCl must have a constructor
    ghost const z: MyClass
  }
}

module NonThisConstAssignments {
  const X: int

  class Cla {
    constructor () {
      X := 15;  // error: can never assign to static const (this used to crash)
      Clb.Y := 15;  // error: can never assign to static const (this used to crash)
    }
  }

  class Clb {
    static const Y: int

    constructor () {
      Y := 15;  // error: cannot ever assign to a static const (this used to crash)
    }
  }

  class Clc {
    const Z: int

    constructor (c: Clc) {
      c.Z := 15;  // error: can assign to const only for 'this' (this used to crash)
    }
  }

  class Cld {
    const Z: int

    constructor () {
      Z := 15;
    }
  }
}

module ConstGhostRhs {
  class S {
    const m: int := n  // error: use of ghost to assign non-ghost field
    ghost const n: int
  }

  const a: int := b  // error: use of ghost to assign non-ghost field
  ghost const b: int

  class S' {
    ghost const m': int := n'
    const n': int
  }

  ghost const a': int := b'
  const b': int

}

module Regression15 {
  predicate F(i: int, j: int) { true }
  function S(i: int): set<int> { {i} }

  method M0() returns (b: bool) {
    b := forall i, j | j <= i <= 100 && i <= j < 100 :: true;  // error: this bogus cyclic dependency was once allowed
  }

  method M4() returns (b: bool) {
    b := forall i, j :: j <= i < 100 && j in S(i) ==> F(i,j);  // error: this bogus cyclic dependency was once allowed
  }
}

module AllocDepend0a {
  class Class {
    const z := if {} == set c: Class | true then 5 else 4  // error: condition depends on alloc (also not compilable, but that's not reported in the same pass)
  }

  const y := if {} == set c: Class | true then 5 else 4  // error: condition depends on alloc (also not compilable, but that's not reported in the same pass)

  newtype byte = x | x < 5 || {} == set c: Class | true  // error: condition not allowed to depend on alloc
  type small = x | x < 5 || {} == set c: Class | true  // error: condition not allowed to depend on alloc
}

module AllocDepend0b {
  class Class { }

  method M() returns (y: int, z: int) {
    z := if {} == set c: Class | true then 5 else 4; // error: not compilable
    y := if {} == set c: Class | true then 5 else 4; // error: not compilable
  }
}

module AllocDepend1 {
  class Class { }

  predicate P(x: int) {
    x < 5 || {} == set c: Class | true  // error: function not allowed to depend on alloc
  }
}

module AllocDepend2 {
  class Klass {
    const z := if exists k: Klass :: allocated(k) then 3 else 4  // error (x2): condition depends on alloc
  }

  const y := if exists k: Klass :: allocated(k) then 3 else 4  // error (x2): condition depends on alloc

  newtype byte = x | x < 5 || exists k: Klass :: allocated(k)  // error: condition not allowed to depend on alloc
  type small = x | x < 5 || exists k: Klass :: allocated(k)  // error: condition not allowed to depend on alloc
}

module AllocDepend3 {
  class Klass { }

  predicate P(x: int) {
    x < 5 || exists k: Klass :: allocated(k)  // error: function not allowed to depend on alloc
  }
}

module AllocDepend4 {
  class Xlass {
    const z := if var k: Xlass? := null; allocated(k) then 3 else 4  // error (x2): condition depends on alloc
  }

  const y := if var k: Xlass? := null; allocated(k) then 3 else 4  // error (x2): condition depends on alloc

  newtype byte = x | x < 5 || var k: Xlass? := null; allocated(k)  // error: condition not allowed to depend on alloc
  type small = x | x < 5 || var k: Xlass? := null; allocated(k)  // error: condition not allowed to depend on alloc
}

module AllocDepend5 {
  class Xlass { }

  predicate P(x: int) {
    x < 5 || var k: Xlass? := null; allocated(k)  // error: function not allowed to depend on alloc
  }
}

module AbstemiousCompliance {
  codatatype EnormousTree<X> = Node(left: EnormousTree, val: X, right: EnormousTree)

  ghost function {:abstemious} Five(): int {
    5  // error: an abstemious function must return with a co-constructor
  }

  ghost function {:abstemious} Id(t: EnormousTree): EnormousTree
  {
    t  // to be abstemious, a parameter is as good as a co-constructor
  }

  ghost function {:abstemious} IdGood(t: EnormousTree): EnormousTree
  {
    match t
    case Node(l, x, r) => Node(l, x, r)
  }

  ghost function {:abstemious} AlsoGood(t: EnormousTree): EnormousTree
  {
    Node(t.left, t.val, t.right)
  }

  ghost function {:abstemious} UniformTree<X>(x: X): EnormousTree<X>
  {
    Node(UniformTree(x), x, UniformTree(x))
  }

  ghost function {:abstemious} AlternatingTree<X>(x: X, y: X): EnormousTree<X>
  {
    Node(AlternatingTree(y, x), x, AlternatingTree(y, x))
  }

  ghost function {:abstemious} AnotherAlternatingTree<X>(x: X, y: X): EnormousTree<X>
  {
    var t := Node(AlternatingTree(x, y), y, AlternatingTree(x, y));
    Node(t, x, t)
  }

  ghost function {:abstemious} NonObvious<X>(x: X): EnormousTree<X>
  {
    AlternatingTree(x, x)  // error: does not return with a co-constructor
  }

  ghost function {:abstemious} BadDestruct(t: EnormousTree): EnormousTree
  {
    Node(t.left, t.val, t.right.right)  // error: cannot destruct t.right
  }

  ghost function {:abstemious} BadMatch(t: EnormousTree): EnormousTree
  {
    match t.right  // error: cannot destruct t.right
    case Node(a, x, b) =>
      Node(a, x, b)
  }

  ghost function {:abstemious} BadEquality(t: EnormousTree, u: EnormousTree, v: EnormousTree): EnormousTree
  {
    if t == u then  // error: cannot co-compare
      Node(t.left, t.val, t.right)
    else if u != v then  // error: cannot co-compare
      Node(u.left, u.val, u.right)
    else
      Node(v.left, v.val, v.right)
  }

  ghost function {:abstemious} Select(b: bool, t: EnormousTree, u: EnormousTree): EnormousTree
  {
    if b then t else u  // abstemious yes: parameters are as good as a co-constructors
  }

  ghost function {:abstemious} Select'(b: bool, t: EnormousTree, u: EnormousTree): EnormousTree
  {
    if b then
      Node(t.left, t.val, t.right)  // fine, too
    else
      Node(u.left, u.val, u.right)  // fine, too
  }
}

module BigOrdinalRestrictionsExtremePred {
  least predicate Test() {
    var st: set<ORDINAL> := {};  // error: cannot use ORDINAL as type argument
    var p: (int, ORDINAL) := (0,0);  // error: cannot use ORDINAL as type argument
    var o: ORDINAL := 0;  // okay
    ghost var f := F(o);  // error: cannot use ORDINAL as type argument
    var f := F'<ORDINAL>();  // error: cannot use ORDINAL as type argument
    var f := F'<(char,ORDINAL)>();  // error: cannot use ORDINAL as type argument
    var lambda := F'<ORDINAL>;  // error: cannot use ORDINAL as type argument
    ParameterizedLemma(o);  // error: cannot use ORDINAL as type argument
    assert forall r: ORDINAL :: P(r);  // error: cannot quantify over ORDINAL here
    assert forall r: (ORDINAL, int) :: F(r.1) < 8;  // error: cannot quantify over ORDINAL here
    assert exists x: int, r: ORDINAL, y: char :: P(r) && F(x) == F(y);  // error: cannot quantify over ORDINAL here
    var s := set r: ORDINAL | r in {};  // error (x2): cannot use ORDINAL as type argument (to set)
    var s' := set r: ORDINAL | true :: 'G';  // error: cannot use ORDINAL here
    ghost var m := imap r: ORDINAL :: 10;  // error (x2): cannot use ORDINAL here
    var sq := [o, o];  // error: cannot use ORDINAL as type argument (to seq)
    var mp0 := map[o := 'G'];  // error: cannot use ORDINAL as type argument (to map)
    var mp1 := map['G' := o];  // error: cannot use ORDINAL as type argument (to map)
    var w := var h: ORDINAL := 100; h + 40;  // okay
    var w': (int, ORDINAL) := (8,8);  // error: cannot use ORDINAL as type argument
    var u: ORDINAL :| u == 15;
    var ti: ORDINAL :| true;
    var u': (ORDINAL, int) :| u' == (15, 15);  // error (x2): ORDINAL cannot be a type argument
    var ti': (ORDINAL, ORDINAL) :| true;  // error (x2): ORDINAL cannot be a type argument
    var lstLocal := var lst: ORDINAL :| lst == 15; lst;
    var lstLocal' := var lst: (ORDINAL, int) :| lst == (15, 15); lst.1;  // error: ORDINAL cannot be a type argument

    var gr := if yt: ORDINAL :| yt == 16 then
      ghost var pg := P(yt); 5
    else
      7;

    calc {
      100;
    ==  {
          forall om: ORDINAL  // allowed
            ensures om < om+1
          {
          }
        }
      100;
    }

    true
  }

  ghost function F<G>(g: G): int
  ghost function F'<G>(): int
  lemma ParameterizedLemma<G>(g: G)
  ghost predicate P(g: ORDINAL)
}

// ----- label domination -----

module LabelDomination {
  method DuplicateLabels(n: int) {
    var x;
    if (n < 7) {
      label L: x := x + 1;
    } else {
      label L: x := x + 1;
    }
    assert old@L(true);  // error: L is not available here
    label L: x := x + 1;
    assert old@L(true);
    label L: x := x + 1;  // error: duplicate label
    assert old@L(true);

    {
      label K:
      x := x + 1;
    }
    assert old@K(true);
    label K:  // error: duplicate label
    assert old@K(true);
  }

  datatype Color = A | B | C
  method Branches(n: int, c: Color) {
    var x: int;
    if n < 2 {
      label X: x := x + 1;
    } else if n < 4 {
      label X: x := x + 1;
    } else {
      label X: x := x + 1;
    }
    if * {
      label X: x := x + 1;
    } else {
      label X: x := x + 1;
    }

    if {
      case true =>
        label X: x := x + 1;
      case true =>
        label X: x := x + 1;
    }

    var i := 0;
    while i < x {
      label X: x := x + 1;
      i := i + 1;
    }

    i := 0;
    while {
      case i < x =>
        label X: x := x + 1;
        i := i + 1;
      case i < x =>
        label X: x := x + 1;
        i := i + 1;
    }

    match c {
      case A =>
        label X: x := x + 1;
      case B =>
        label X: x := x + 1;
      case C =>
        label X: x := x + 1;
    }

    label X: x := x + 1;  // all okay
  }

  method A0() {
    label Q:
    assert true;
  }

  method A1() {
    label Q:
    assert true;
  }

  class MyClass {
    var x: int

    method LabelNotInScope_Old(y: int) {
      label GoodLabel:
      if y < 5 {
        label Treasure:
        assert true;
      }
      assert old(x) == old@Treasure(x);  // error: no label Treasure in scope
      assert 10 == old@WonderfulLabel(x);  // error: no label WonderfulLabel in scope
      assert old(x) == old@GoodLabel(x);
      assert old(x) == old@FutureLabel(x);  // error: no label FutureLabel in scope
      label FutureLabel: {}
    }

    method LabelNotInScope_Unchanged(y: int) {
      label GoodLabel:
      if y < 5 {
        label Treasure:
        assert true;
      }
      assert unchanged@Treasure(`x);  // error: no label Treasure in scope
      assert unchanged@WonderfulLabel(this);  // error: no label WonderfulLabel in scope
      assert unchanged@GoodLabel(this);
      assert unchanged@FutureLabel(this);  // error: no label FutureLabel in scope
      label FutureLabel: {}
    }

    method LabelNotInScope_Fresh(y: int, c: MyClass) {
      label GoodLabel:
      if y < 5 {
        label Treasure:
        assert true;
      }
      assert fresh@Treasure(c);  // error: no label Treasure in scope
      assert fresh@WonderfulLabel(c);  // error: no label WonderfulLabel in scope
      assert fresh@GoodLabel(c);
      assert fresh@FutureLabel(c);  // error: no label FutureLabel in scope
      label FutureLabel: {}
    }
  }
}
