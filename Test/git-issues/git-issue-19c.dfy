// RUN: %exits-with 2 %dafny /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Resolution checks for functions appearing in reads clauses

module Types {
  class Basic {
    var data: int
  }

  datatype Record<X> = Record(X)
}

module A {
  import opened Types

  function F0(f: int ~> real): real
    requires f.requires(0) && f.requires(1)
    reads f.reads(0), f.reads(1)
  {
    f(0) + f(1)
  }

  function F1(f: int ~> real): real
    requires f.requires(0) && f.requires(1)
    reads f.reads
  {
    f(0) + f(1)
  }

  function G0(f: Basic ~> real, c: Basic): real
    requires f.requires(c)
    reads f.reads(c)
  {
    f(c)
  }

  function G2(f: Basic ~> real, c: Basic): real
    requires f.requires(c)
    // the following line is equivalent to writing "f.reads" like in G1 above
    reads set basic: Basic, obj: object | obj in f.reads(basic) :: obj // error: this makes G1 depend on the allocation state
  {
    f(c)
  }

  function G4<X(!new)>(f: X ~> real, x: X): real
    requires f.requires(x)
    reads f.reads // fine, since X is !new
  {
    f(x)
  }

  function H0(f: Basic ~> real): Basic ~> real
  {
    f
  }

  function H1(f: Basic ~> real, c: Basic): int
    reads
      // f and f.reads are allowed to be mentioned in a reads clause, just not be the result of a frame expression
      var ff := f;
      var fr := f.reads;
      {c}
  {
    c.data
  }

  function K0(f: int -> set<object>, g: int ~> set<Basic?>, h: int --> iset<Basic>): int
    reads f, g, h
  {
    15
  }

  function K1(f: int -> multiset<object>, g: int ~> seq<Basic?>): int
    reads f, g
  {
    15
  }
}

module B {
  import opened Types

  function G1(f: Basic ~> real, c: Basic): real
    requires f.requires(c)
    reads f.reads // error: this makes G1 depend on the allocation state
  {
    f(c)
  }

  function G3<X>(f: X ~> real, x: X): real
    requires f.requires(x)
    reads f.reads // error: this makes G3 depend on the allocation state
  {
    f(x)
  }

  function G5<X>(f: (int, X, real) ~> real, x: X): real
    requires f.requires(2, x, 2.0)
    reads f.reads // error: this makes G5 depend on the allocation state
  {
    f(2, x, 2.0)
  }
}

module C {
  import opened Types

  function K1(f: int -> set<int>, g: int ~> iset<bool>, h: int --> map<Basic, Basic>, k: int --> imap<Basic, Basic>): int
    reads f // error: type not supported in reads clause
    reads g // error: type not supported in reads clause
    reads h // error: type not supported in reads clause
    reads k // error: type not supported in reads clause
  {
    15
  }

  method M4(f: int ~> int) {
    var u := (x: int)
      requires x < 10
      reads f // error: type not supported in reads clause
      =>
      25;
  }
}

module D {
  import opened Types

  method M0(f: int -> set<object>) {
    var u := (x: int)
      requires x < 10
      reads f
      =>
      25;
  }

  method M1(f: Basic -> set<object>) {
    var u := (x: int)
      requires x < 10
      reads f // error: this makes the lambda expression depend on the allocation state
      =>
      25;
  }

  method M2(f: Basic ~> int) {
    var u := (x: int)
      requires x < 10
      reads f.reads // error: this makes the lambda expression depend on the allocation state
      =>
      25;
  }

  method M3(f: int ~> int) {
    var u := (x: int)
      requires x < 10
      reads f.reads // fine
      =>
      25;
  }
}
  
module E {
  import opened Types

  method N0(f: Basic -> set<object>) {
    var u := () => set c: Basic | c.data == 11; // error: this makes the lambda expression depend on the allocation state
  }

  method N1(f: Basic -> set<object>) {
    var u := ()
      requires |set c: Basic | c.data == 11| == 3 // error: this makes the lambda expression depend on the allocation state
      =>
      25;
  }

  method N2(f: Basic -> set<object>, c: Basic) {
    var u := ()
      reads if |set c: Basic | c.data == 11| == 3 then {} else {c} // error: this makes the lambda expression depend on the allocation state
      =>
      25;
  }

  method N3<X>(f: X -> set<object>, c: Basic, p: (X, int) -> bool) {
    var u := ()
      reads if |set x: X | p(x, 0) :: p(x, 1)| == 3 then {} else {c} // error: this makes the lambda expression depend on the allocation state
      =>
      25;
  }
}
