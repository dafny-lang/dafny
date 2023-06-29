// RUN: %exits-with 4 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ReadsRequiresReads {
  ghost function MyReadsOk<A,B>(f : A ~> B, a : A) : set<object?>
    reads f.reads(a)
  {
    f.reads(a)
  }

  ghost function MyReadsOk2<A,B>(f : A ~> B, a : A) : set<object?>
    reads f.reads(a)
  {
    (f.reads)(a)
  }

  ghost function MyReadsOk3<A,B>(f : A ~> B, a : A) : set<object?>
    reads (f.reads)(a)
  {
    f.reads(a)
  }

  ghost function MyReadsOk4<A,B>(f : A ~> B, a : A) : set<object?>
    reads (f.reads)(a)
  {
    (f.reads)(a)
  }

  ghost function MyReadsBad<A,B>(f : A ~> B, a : A) : set<object?>
  {
    f.reads(a)  // error: MyReadsBad does not have permission to read what f.reads(a) reads
  }

  ghost function MyReadsBad2<A,B>(f : A ~> B, a : A) : set<object?>
  {
    (f.reads)(a)  // error: MyReadsBad2 does not have permission to read what f.reads(a) reads
  }

  ghost function MyReadsOk'<A,B>(f : A ~> B, a : A, o : object) : bool
    reads f.reads(a)
  {
    o in f.reads(a)
  }

  ghost function MyReadsBad'<A,B>(f : A ~> B, a : A, o : object) : bool
  {
    o in f.reads(a)  // error: MyReadsBad' does not have permission to read what f.reads(a) reads
  }

  ghost function MyRequiresOk<A,B>(f : A ~> B, a : A) : bool
    reads f.reads(a)
  {
    f.requires(a)
  }

  ghost function MyRequiresBad<A,B>(f : A ~> B, a : A) : bool
  {
    f.requires(a)  // error: MyRequiresBad does not have permission to read what f.requires(a) reads
  }
}

module WhatWeKnowAboutReads {
  ghost function ReadsNothing():(){()}

  lemma IndeedNothing() {
    assert ReadsNothing.reads() == {};
    assert ((ReadsNothing).reads)() == {};
  }

  method NothingHere() {
    assert (() => ()).reads() == {};
  }

  class S {
    var s : S?
  }

  ghost function ReadsSomething(s : S?):()
    reads s
  {()}

  method MaybeSomething() {
    var s  := new S;
    var s' := new S;
           if * { assert s in ReadsSomething.reads(s) || ReadsSomething.reads(s) == {};
    } else if * { assert s in ReadsSomething.reads(s);
    } else if * { assert ReadsSomething.reads(s) == {};  // error
    } else if * { assert s' !in ReadsSomething.reads(s);
    } else if * { assert s' in ReadsSomething.reads(s);  // error
    }
  }

  method SomethingHere() {
    var s  := new S;
    var s' := new S;
    var f := (u) reads u => ();
           if * { assert s in f.reads(s) || f.reads(s) == {};
    } else if * { assert s in f.reads(s);
    } else if * { assert f.reads(s) == {};  // error
    } else if * { assert s' !in f.reads(s);
    } else if * { assert s' in f.reads(s);  // error
    }
  }
}

module ReadsAll {
  ghost function A(f: int ~> int) : int
    reads set x,o | o in f.reads(x) :: o  // note, with "set o,x ..." instead, Dafny complains (this is perhaps less than ideal)
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }

  function B(f: int ~> int) : int
    reads set x,o | o in f.reads(x) :: o  // note, with "set o,x ..." instead, Dafny complains (this is perhaps less than ideal)
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }

  ghost function C(f: int ~> int) : int
    reads f.reads
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }

  function D(f: int ~> int) : int
    reads f.reads
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }
}

module ReadsOnFunctions {
  lemma Requires_Reads_What_Function_Reads(f: int ~> int)
  {
    var g := f.requires;
    assert g.reads(10) == f.reads(10);
  }
}

module FuncCollectionRegressions {
  class C {
    var x: int
    var y: int
  }

  ghost function F(st: set<C>, ss: iset<C>, sq: seq<C>, ms: multiset<C>): int
    reads st
    reads ss
    reads sq
    reads ms

  method CallF0(c: C, st: set<C>, ss: iset<C>, sq: seq<C>, ms: multiset<C>)
    requires c !in st && c !in ss && c !in sq && c !in ms
    modifies c
  {
    var a := F(st, ss, sq, ms);
    c.x := c.y + 3;
    var b := F(st, ss, sq, ms);
    assert a == b;
  }

  method CallF1(c: C, st: set<C>, ss: iset<C>, sq: seq<C>, ms: multiset<C>)
    requires c !in ss && c !in sq && c !in ms
    modifies c
  {
    var a := F(st, ss, sq, ms);
    c.x := c.y + 3;
    var b := F(st, ss, sq, ms);
    assert a == b; // error: F may have changed
  }

  method CallF2(c: C, st: set<C>, ss: iset<C>, sq: seq<C>, ms: multiset<C>)
    requires c !in st && c !in sq && c !in ms
    modifies c
  {
    var a := F(st, ss, sq, ms);
    c.x := c.y + 3;
    var b := F(st, ss, sq, ms);
    assert a == b; // error: F may have changed
  }

  method CallF3(c: C, st: set<C>, ss: iset<C>, sq: seq<C>, ms: multiset<C>)
    requires c !in st && c !in ss && c !in ms
    modifies c
  {
    var a := F(st, ss, sq, ms);
    c.x := c.y + 3;
    var b := F(st, ss, sq, ms);
    assert a == b; // error: F may have changed
  }

  method CallF4(c: C, st: set<C>, ss: iset<C>, sq: seq<C>, ms: multiset<C>)
    requires c !in st && c !in ss && c !in sq
    modifies c
  {
    var a := F(st, ss, sq, ms);
    c.x := c.y + 3;
    var b := F(st, ss, sq, ms);
    assert a == b; // error: F may have changed
  }

  ghost function A0(): set<C>
  ghost function A1(): iset<C>
  ghost function A2(): seq<C>
  ghost function A3(): multiset<C>

  ghost function G(): int
    reads A0
    reads A1
    // regression: the following line once caused malformed Boogie
    reads A2
    // regression: the following line once caused malformed Boogie
    reads A3

  method P0(c: C)
    requires c !in A0() && c !in A1() && c !in A2() && c !in A3()
    modifies c
  {
    var a := G();
    c.x := c.y + 3;
    var b := G();
    assert a == b;
  }

  method P1(c: C)
    requires c !in A1() && c !in A2() && c !in A3()
    modifies c
  {
    var a := G();
    c.x := c.y + 3;
    var b := G();
    assert a == b; // error: G may have changed
  }

  method P2(c: C)
    requires c !in A0() && c !in A2() && c !in A3()
    modifies c
  {
    var a := G();
    c.x := c.y + 3;
    var b := G();
    assert a == b; // error: G may have changed
  }

  method P3(c: C)
    requires c !in A0() && c !in A1() && c !in A3()
    modifies c
  {
    var a := G();
    c.x := c.y + 3;
    var b := G();
    assert a == b; // error: G may have changed
  }

  method P4(c: C)
    requires c !in A0() && c !in A1() && c !in A2()
    modifies c
  {
    var a := G();
    c.x := c.y + 3;
    var b := G();
    assert a == b; // error: G may have changed
  }
}
