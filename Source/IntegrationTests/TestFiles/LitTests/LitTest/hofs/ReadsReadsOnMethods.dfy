// RUN: %exits-with 4 %dafny /print:"%t.print" /readsClausesOnMethods:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Clone of ReadsReads.dfy but using methods instead of functions

module ReadsRequiresReads {
  ghost method MyReadsOk<A,B>(f : A ~> B, a : A) returns (r: set<object?>)
    requires f.requires(a) reads f.reads(a)
  {
    r := f.reads(a);
  }

  ghost method MyReadsOk2<A,B>(f : A ~> B, a : A) returns (r: set<object?>)
    requires f.requires(a)
    reads f.reads(a)
  {
    r := (f.reads)(a);
  }

  ghost method MyReadsOk3<A,B>(f : A ~> B, a : A) returns (r: set<object?>)
    requires (f.requires)(a)
    reads (f.reads)(a)
  {
    r := f.reads(a);
  }

  ghost method MyReadsOk4<A,B>(f : A ~> B, a : A) returns (r: set<object?>)
    requires (f.requires)(a)
    reads (f.reads)(a)
  {
    r := (f.reads)(a);
  }

  ghost method MyReadsBad<A,B>(f : A ~> B, a : A) returns (r: set<object?>)
    reads {}
  {
    r := f.reads(a);  // error: MyReadsBad does not have permission to read what f.reads(a) reads
  }

  ghost method MyReadsBad2<A,B>(f : A ~> B, a : A) returns (r: set<object?>)
    reads {}
  {
    r := (f.reads)(a);  // error (x2): MyReadsBad2 does not have permission to read what f.reads(a) reads, function precondition cannot be proved
  }

  ghost method MyReadsOk'<A,B>(f : A ~> B, a : A, o : object) returns (r: bool)
    requires f.requires(a) reads f.reads(a)
  {
    r := o in f.reads(a);
  }

  ghost method MyReadsBad'<A,B>(f : A ~> B, a : A, o : object) returns (r: bool)
    reads {}
  {
    r := o in f.reads(a);  // error: MyReadsBad' does not have permission to read what f.reads(a) reads
  }

  ghost method MyRequiresOk<A,B>(f : A ~> B, a : A) returns (r: bool)
    requires f.requires(a) reads f.reads(a)
  {
    r := f.requires(a);
  }

  ghost method MyRequiresBad<A,B>(f : A ~> B, a : A) returns (r: bool)
    reads {}
  {
    r := f.requires(a);  // error: MyRequiresBad does not have permission to read what f.requires(a) reads
  }
}

// WhatWeKnowAboutReads not that applicable since we don't have method references as first class values

module ReadsAll {
  ghost method A(f: int ~> int) returns (r: int)
    reads set x,o | o in f.reads(x) :: o  // note, with "set o,x ..." instead, Dafny complains (this is perhaps less than ideal)
    requires forall x :: f.requires(x)
  {
    return f(0) + f(1) + f(2);
  }

  method B(f: int ~> int) returns (r: int)
    reads set x,o | o in f.reads(x) :: o  // note, with "set o,x ..." instead, Dafny complains (this is perhaps less than ideal)
    requires forall x :: f.requires(x)
  {
    return f(0) + f(1) + f(2);
  }

  ghost method C(f: int ~> int) returns (r: int)
    reads f.reads
    requires forall x :: f.requires(x)
  {
    return f(0) + f(1) + f(2);
  }

  method D(f: int ~> int) returns (r: int)
    reads f.reads
    requires forall x :: f.requires(x)
  {
    return f(0) + f(1) + f(2);
  }
}

// ReadsOnFunctions not relevant
// FuncCollectionRegressions not relevant since we're not using method reads clauses
// in a similar way (yet :)
