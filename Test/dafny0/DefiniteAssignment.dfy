// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass<G> {
  const x: G
  var y: G
  ghost var oxA: G  // ghosts never need to be assigned
  ghost const oxB: G  // ghosts never need to be assigned
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
    y := g;
  }  // error: x was never assigned
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
    k := y;  // error: y has not yet been assigned
  } else {
    z := *;
    return z;  // this is fine, since z was assigned before the havoc
  }
}

method OtherAssignments<G(==)>(a: G, h: int) returns (k: G) {
  var e0: G, e1: G;
  e0 :| e0 == e1;  // error: about the use of e1, but not the use of e0
  var x:G, y:G, z:G :| x == z == a;  // (note, the compiler would complain here
                                     // that it doesn't know how to compile the
                                     // statement, but it does satisfy the
                                     // definite-assignment rules)
  if h < 10 {
    k := x;  // fine
  } else if h < 20 {
    k := y;  // fine (the problem lies with the assignment statement above)
  } else {
    return z;
  }
}

method Callee<G>(a: G) returns (x: G, y: G, z: G)
{
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
  a := b;  // no problem, since we're in a ghost method
}  // no problem that g was never assigned, since we're in a ghost method

method MM<G>(ghost x: int, g: G) returns (vv: G, ww: G)
{
  ghost var a: G, b: G;
  a := b;  // no problem, since this is a ghost assignment
  if x < 10 {
    var c: G;
    a := c;  // no problem, since this is a ghost assignment
  }
  var v: G := g;
  v := *;  // this assignment does not make v un-assigned, since it was assigned before
  vv := v;  // fine
  var w: G := *;
  w := *;
  ww := w;  // error: w is used before it is really assigned
}

// ----- iterators ----------------------------

// To check that yield parameters, which are stored as fields of "this",
// get values before "this" is available, one would need some sort of
// mechanism like the "new;" in constructors.  Until such a mechanism
// is invented for iterators, iterators cannot be allowed to be instantiated
// with "difficult to initialize" type arguments.
// Still, definite-assignment rules are enforced for local variables
// declared in the iterator body.
iterator Iter<G>(n: nat, g: G) yields (y: G, ghost ug: G, z: G)
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
