// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass<G> {
  const x: G
  var y: G
  ghost var oxA: G  // error (TODO: "ghosts never need to be assigned" applies if G were marked as nonempty)
  ghost const oxB: G  // error (TODO: "ghosts never need to be assigned" applies if G were marked as nonempty)
  constructor C0()
  {
    x := y;  // error: y has not yet been defined
    this.y := (((this))).x;
    new;  // error (x2): oxA and oxB have not been assigned
  }
  constructor C1(g: G)
  {
    x := g;
    new;  // error: y was never assigned, neither was oxA or oxB
  }
  constructor C2(g: G)
  {
    x := g;
  }  // error: y was never assigned, neither was oxA or oxB
  constructor C3(g: G)
  {
    y := g;
  }  // error: x was never assigned, neither was oxA or oxB
  constructor C4(g: G)
  {
    this.y := *;
    x := y;
  }
}

method M0<G>(x: int, a: G, b: G) returns (y: G)
  ensures true
{
  if x < 10 {
    y := a;
  } else if x < 100 {
    return b;
  } else {
    // this is the branch where y has not been assigned
  }
}  // error: y is not assigned

method M1<G>(x: int, a: G, b: G) returns (y: G, z: G)
  ensures true
{
  if x < 10 {
    z, y := a, a;
  } else if x < 20 {
    y := z;  // error: z is used before it is assigned
    z := a;
  } else if x < 30 {
    var i, j := a, b;
    y, z := i, j;
  } else if x < 40 {
    var i, j;
    i := a;
    y, z := i, j;  // error: j is used before it is assigned
  } else if x < 100 {
    z := a;
    return;  // error: y is not assigned
  } else {
    y := b;
  }
}  // error: z is not assigned

class C { var u: int }

function method F(): C

type NonNullC = c: C? | c != null witness F()

method Main()
{
  var c: NonNullC := new C;
  var y := M0<NonNullC>(102, c, c);
  assert y != null;
  print y.u, "\n";  // this would crash at run time if, contrary to what the
                    // previous assertion says, y were null
}

method DontForgetHavoc<G>(a: G, h: int) returns (k: G) {
  var x:G, y:G, z:G := a, *, a;
  if h < 10 {
    k := x;  // fine
  } else if h < 20 {
    k := y;
  } else {
    z := *;
    return z;  // this is fine, since z was assigned before the havoc
  }
}

method OtherAssignments<G(==)>(a: G, h: int) returns (k: G) {
  var e0: G, e1: G;
  e0 :| e0 == e1;  // error (x2): about the use of e1, but not the use of e0; and about can't prove existence
  var x:G, y:G, z:G :| x == z == a;  // (note, the compiler would complain here that it doesn't know how to compile the
                                     // statement, but it does satisfy the definite-assignment rules)
  if h < 10 {
    k := x;  // fine
  } else if h < 20 {
    k := y;  // fine (the problem lies with the assignment statement above)
  } else {
    return z;
  }
}
method OtherAssignments'<G(==,0)>() {
  var e0: G, e1: G;
  e0 :| e0 == e1;  // all is fine here
}
method Callee<G>(a: G) returns (x: G, y: G, z: G) {
  return a, a, a;
}

method Caller<G>(g: G) returns (k: G) {
  var a:G, b:G, c:G := Callee(g);
  if * {
    k := a;
  } else if * {
    k := b;
  } else {
    return c;
  }
}

ghost method GM<G>() returns (g: G)
{
  var a: G, b: G;
  a := b;  // error: since b has not been assigned
}  // error: g was never assigned

method MM<G>(ghost x: int, g: G) returns (vv: G, ww: G)
{
  ghost var a: G, b: G;
  a := b;  // error: b has not been assigned
  if x < 10 {
    var c: G;
    a := c;  // error: c has not been assigned
  }
  var v: G := g;
  v := *;  // this assignment does not make v un-assigned, since it was assigned before
  vv := v;  // fine
  var w: G := *;
  w := *;
  ww := w;
}

// ----- iterators ----------------------------

// To check that yield parameters, which are stored as fields of "this",
// get values before "this" is available, one would need some sort of
// mechanism like the "new;" in constructors.  Until such a mechanism
// is invented for iterators, yield-parameters must be auto-init types
// (and ghost yield-parameters must be nonempty).
// Still, definite-assignment rules are enforced for local variables
// declared in the iterator body.
iterator Iter<G(0)>(n: nat, g: G) yields (y: G, ghost ug: G, z: G)
{
  var i;
  i := 0;
  while i < n
  {
    if i % 17 == 0 {
      yield g, g, g;
      yield;  // this is now fine
    } else if i == n/2 {
      y := g;
      z := y;
      yield;
      yield;
    } else if i == n % 11 {
      if * {
        ug, y := g, g;
        yield;
      } else {
        y := g;
        yield;
      }
      y := if i % 2 == 0 then y else y;
    }
    i := i + 1;
  }
}

// ----- loops ------------------------------

method Loop<G>(a: G, b: G, n: nat, k: int) returns (g: G)
{
  var w: G, x: G, y: G, z: G;
  w, x := a, a;
  if k < 100 {
    z := a;
  }
  if * { y := a; } else { y := b; }
  var i := 0;
  while i < n
    invariant 4 < i ==> y == a
    invariant y == b || i <= n
  {
    if i == 4 {
      y := a;
    }
    if i % 2 == 0 {
      x, z := b, b;
    }
    var lw := w;
    var lx := x;
    i := i + 1;
  }
  g := w;  // fine, since w was assigned even before the loop (Boogie figures this out)
  g := x;  // fine, since x was assigned even before the loop (amazingly, Boogie figures this out with no help from Dafny)
  if k < 100 {
    g := z;  // fine, since z was assigned before the loop in cases where k < 100 (here, Boogie needs help from Dafny)
  }
  g := *;
  // some local scopes
  { var t: G; }
  { var t: G; }
  while 0 < i {
    i := i - 1;
  }
}

// ----- multiple returns, LHS patterns, and underscores -----

function method Two<T>(t: T): (T, T)
{
  (t, t)
}

method TwoMethod<T>(t: T) returns (a: T, b: T)
{
  a, b := t, t;
}

method UnderscoresAndPatterns0<T>(tt: T)
{
  var a: T, b: T;
  var a' := a;  // error: use before definition
  var b' := b;  // error: use before definition
  print a', " ", b', "\n";
}

method UnderscoresAndPatterns1<T>(tt: T)
{
  var (a, b) := Two<T>(tt);
  var a' := b;
  var b' := b;
  print a', " ", b', "\n";
}

method UnderscoresAndPatterns2<T>(tt: T)
{
  var (_, b) := Two<T>(tt);
  var a' := b;
  var b' := b;
  print a', " ", b', "\n";
}

method UnderscoresAndPatterns3<T>(tt: T)
{
  var _, b := TwoMethod<T>(tt);
  var b' := b;
}

// ----- regression tests from github issue #213 -----

class Regression213 {
  constructor A() {
    var f: object;  // regression; previously, this caused a crash in Dafny
  }
  constructor B() {
    new;
    var f: object;  // regression; previously, this caused a crash in Dafny
  }
  constructor C() {
    var f: object;
    var g := f;  // error: use of f before a definition
  }
  constructor D() {
    new;
    var f: object;
    var g := f;  // error: use of f before a definition
  }

  method M() {
    var f: object;
  }
  method N() {
    var f: object;
    var g := f;  // error: use of f before a definition
  }
}

// -------------------

module AssignSuchThat {
  type D(==)

  method BadCompiled0()
  {
    var d: D :| true;  // error: cannot prove existence of such a "d"
  }
  method BadCompiled1()
  {
    // we don't expect any "variable used before defined" errors on the next line
    var d: D :| d == d;  // error: cannot prove existence of such a "d"
  }
  method BadCompiled2()
  {
    var d: D;
    d :| true;  // error: cannot prove existence of such a "d"
  }
  method BadCompiled3()
  {
    var d: D;
    // we don't expect any "variable used before defined" errors on the next line
    d :| d == d;  // error: cannot prove existence of such a "d"
  }
}

module AssignSuchThatReference {
  trait D {
    const x: int
  }

  method BadCompiled0()
  {
    // we don't expect any "variable used before defined" errors on the next line,
    // and no null errors, either.
    var d: D :| d.x == d.x;  // error: cannot prove existence of such a "d"
  }
  method BadCompiled1()
  {
    var d: D;
    // we don't expect any "variable used before defined" errors on the next line,
    // and no null errors, either.
    d :| d.x == d.x;  // error: cannot prove existence of such a "d"
  }
  method Good(y: D)
  {
    var d: D;
    d :| d.x == d.x;  // fine, since parameter "y" serves as a witness
  }
}

module LetSuchThat {
  type C

  function Bad(): int
  {
    // regression: in the the following line, the verifier once used the fact that all types were nonempty
    var c: C :| true;  // error: cannot prove existence of such a "c"
    5
  }

  function Good(y: C): int
  {
    var c: C :| true;  // fine, since parameter "y" serves as a witness
    5
  }
}

module NonEmpty {
  class MyClass<G(00)> {
    const x: G
    var y: G
    ghost var oxA: G  // since G is nonempty, oxA does not need to be initialized by the constructor
    ghost const oxB: G  // ditto
    constructor C0()
    {
      x := y;  // error: y has not yet been defined
      this.y := (((this))).x;
      new;
    }
    constructor C1(g: G)
    {
      x := g;
      new;  // error: y was never assigned
    }
    constructor C2(g: G)
    {
      x := g;
    }  // error: y was never assigned
    constructor C3(g: G)
    {
      oxB := oxA;  // fine
      y := g;
    }  // error: x was never assigned
  }
}

module Regression {
  class Class { }

  // The resolver didn't always compute the smallest set of used type parameters. That made
  // it pick "Large" as the grounding constructor instead of "Small".
  datatype D<X, Y> = Small(X, X, X, X) | Large(X, Y)

  // The following method detects if Large is picked as the grounding constructor. If it
  // is (and it once was), then a definite-assignment error would be generated. However,
  // if it properly picks Small as the ground constructor, then there is no error.
  method M() returns (d: D<int, Class>) {
  }

  // Similarly, the following should pick "Little" as the ground constructor, because it
  // does not make use of any type parameters.
  type Opaque(0)
  datatype E<Z> = Little(Opaque, Opaque, Opaque) | Big(Z)

  // If Big is picked as the grounding constructor, then a definite-assignment error
  // would be generated for the following method. This was once the case. But if the
  // grounding constructor is picked to be Little (as it should be), then there is no
  // error in method N.
  method N() returns (e: E<Class>) {
  }
}

module AdditionalTests {
  type GGG(00)

  method DefiniteAssignmentLocal0() returns (r: GGG) {
    var g: GGG;
    r := g; // error: g is subject to definite-assignment rules and cannot be used unless first initialized
  }

  method DefiniteAssignmentLocal1(a: bool, ghost b: bool) returns (ghost r: GGG, r': GGG) {
    var g: GGG;
    if a {
      r := g; // error: g is subject to definite-assignment rules and cannot be used unless first initialized (despite being assigned to a ghost)
      r' := g; // this is an error, but it is masked by the error on the previous line
    } else {
      if b {
        var h: GGG;
        h := g; // error: g is subject to definite-assignment rules and cannot be used unless first initialized (despite being assigned to a ghost)
      }
    }
  } // error: r' may not have been assigned

  ghost method DefiniteAssignmentLocal2() returns (r: GGG) {
    var g: GGG; // no initialization needed, since we're in a ghost context
    r := g;
  }

  method DefiniteAssignmentOut0() returns (r: GGG) {
  } // error: g is subject to definite-assignment rules and cannot be used unless first initialized

  method DefiniteAssignmentOut1() returns (ghost r: GGG) {
  } // no initialization needed, since the out-parameter is ghost

  ghost method DefiniteAssignmentOut2() returns (r: GGG) {
  } // no initialization needed, since we're in a ghost context

  lemma DefiniteAssignmentOut3() returns (r: GGG) {
  } // no initialization needed, since we're in a ghost context
}
