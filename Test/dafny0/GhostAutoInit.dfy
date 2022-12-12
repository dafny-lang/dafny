// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module DeclaredTypes {

  trait MaybeEmpty { }
  type GhostAutoInit = x: MaybeEmpty? | true ghost witness null
  type CompileAutoInit = MaybeEmpty?

  method NotUsed() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
  }

  method Used() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      var x := a;  // error: a has not been initialized
    case true =>
      var x := b;  // error: b has not been initialized
    case true =>
      var x := c;
  }

  method GhostUsed() {
    ghost var a: MaybeEmpty;
    ghost var b: GhostAutoInit;
    ghost var c: CompileAutoInit;
    if
    case true =>
      ghost var x := a;  // error: a has not been initialized
    case true =>
      ghost var x := b;
    case true =>
      ghost var x := c;
  }

  method UsedByGhost() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      ghost var x := a;  // error: a has not been initialized
    case true =>
      ghost var x := b;  // error: b has not been initialized
    case true =>
      ghost var x := c;
  }

  method PassToCompiled() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      TakeParameter(a);  // error: a has not been initialized
    case true =>
      TakeParameter(b);  // error: b has not been initialized
    case true =>
      TakeParameter(c);
  }
  method TakeParameter<G>(g: G) {
  }

  method PassToGhost() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      TakeGhostParameter(a);  // error: a has not been initialized
    case true =>
      TakeGhostParameter(b);  // error: a has not been initialized
    case true =>
      TakeGhostParameter(c);
  }
  method TakeGhostParameter<G>(ghost g: G) {
  }

  method GhostPassToGhost() {
    ghost var a: MaybeEmpty;
    ghost var b: GhostAutoInit;
    ghost var c: CompileAutoInit;
    if
    case true =>
      TakeGhostParameter(a);  // error: a has not been initialized
    case true =>
      TakeGhostParameter(b);
    case true =>
      TakeGhostParameter(c);
  }
}

module TypeParameters {
  method NotUsed<MaybeEmpty, GhostAutoInit(00), CompileAutoInit(0)>() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
  }

  method Used<MaybeEmpty, GhostAutoInit(00), CompileAutoInit(0)> () {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      var x := a;  // error: a has not been initialized
    case true =>
      var x := b;  // error: b has not been initialized
    case true =>
      var x := c;
  }

  method GhostUsed<MaybeEmpty, GhostAutoInit(00), CompileAutoInit(0)>() {
    ghost var a: MaybeEmpty;
    ghost var b: GhostAutoInit;
    ghost var c: CompileAutoInit;
    if
    case true =>
      ghost var x := a;  // error: a has not been initialized
    case true =>
      ghost var x := b;
    case true =>
      ghost var x := c;
  }

  method UsedByGhost<MaybeEmpty, GhostAutoInit(00), CompileAutoInit(0)>() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      ghost var x := a;  // error: a has not been initialized
    case true =>
      ghost var x := b;  // error: b has not been initialized
    case true =>
      ghost var x := c;
  }
}

module OutParameters {
  trait EmptyType {
    lemma False()
      ensures false
  }

  method M0() returns (e: EmptyType) {
  }  // error: there's no definite assignment to "e"

  method M1() returns (e: EmptyType) {
    // The following line should give an error, because it's not possible to prove the
    // existence of such a "d". This tests that the "where" clause of out-parameter "e"
    // has the form "defass ==> typeAntecedent" (if the "where" clause were just
    // "typeAntecedent", then the verifier would be able to find a value for "d", which
    // would be bad).
    var d: EmptyType :| true;  // error: failure to prove existence of such a "d"
  }  // error: there's no definite assignment to "e"
}

module FiftyShadesOfGhost {
  // A variable of type G is not subject to definite-assignment rules if the variable
  // is ghost--more precisely, either a variable declared with "ghost" or a variable contained
  // in a ghost context. The tests in this module check that the enclosing context is
  // considered when making decisions about definite assignments.
  type G = x | x % 2 == 1 ghost witness 1  // nonempty type
  trait H { }                              // (treated as) may be empty

  method L() returns (c: G, ghost g: G, d: H, ghost h: H) {
  }  // error (x3): c,d,h have not been assigned (but g is fine, since g is ghost and of type G)

  method M() {
    var m: G;
    ghost var n: G;
    ghost var b0 := m == n;  // error: m is used before it's been initialized
    var x: H;
    ghost var y: H;
    ghost var b1 := x == y;  // error (x2): neither x nor y has been initialized
  }

  ghost method N() returns (g: G, h: H) {
    var m: G;  // even without the "ghost" keyword, this is really a ghost variable
    ghost var n: G;
    ghost var b0 := m == n;  // all is fine
    var x: H;
    ghost var y: H;
    ghost var b1 := x == y;  // error (x2): neither x nor y has been initialized
  }  // error: h has not been assigned (but g is fine)

  method O() returns (c: G, ghost g: G, d: H, ghost h: H)
    ensures c == g && d == h ==> g == c && h == d  // out-parameters can be assumed to have value in ensures clauses
  {
  }  // error (x3): c,d,h have not been assigned

  method P(z: int) {
    assert z < 10 by {
      var m: G;  // even without the "ghost" keyword, this is really a ghost variable--it will never be compiled
      ghost var n: G;
      ghost var b0 := m == n;  // all is fine
      var x: H;
      ghost var y: H;
      ghost var b1 := x == y;  // error (x2): neither x nor y has been initialized
      assume z < 2;  // this will make the assertion failure go away
    }
  }

  method Q(ghost z: int, w: int) {
    if z < w {  // this "if" statement is a ghost statement
      var m: G;  // even without the "ghost" keyword, this is really a ghost variable--it will never be compiled
      ghost var n: G;
      ghost var b0 := m == n;  // all is fine
      var x: H;
      ghost var y: H;
      ghost var b1 := x == y;  // error (x2): neither x nor y has been initialized
    }
  }

  method R(z: int, w: int)
    requires z == w
  {
    calc {
      z;
    <=  {
          var m: G;  // even without the "ghost" keyword, this is really a ghost variable--it will never be compiled
          ghost var n: G;
          ghost var b0 := m == n;  // all is fine
          var x: H;
          ghost var y: H;
          ghost var b1 := x == y;  // error (x2): neither x nor y has been initialized
        }
      z;
    }
  }

  method S() {
    var m: G;
    ghost var n: G;
    var x: H;
    ghost var y: H;
    Callee(m, n, x, y);  // error (3x): m,x,y have not been assigned
  }
  method Callee(c: G, ghost g: G, d: H, ghost h: H)
  ghost method GhostCallee(c: G, g: G, d: H, h: H)

  datatype LongCell = LongGH(c: G, ghost g: G, d: H, ghost h: H)
  datatype SmallCell = SmallGH(g: G, h: H)

  method T() {
    var m: G;
    ghost var n: G;
    var x: H;
    ghost var y: H;
    var cell := LongGH(m, n, x, y);  // error (3x): m,x,y have not been assigned
  }

  method U(cell: LongCell) {
    match cell
    case LongGH(m, n, x, y) =>  // all 4 get bound to values
      Callee(m, n, x, y);  // all fine
  }

  method V(cell: LongCell) {
    if m, n, x, y :| cell == LongGH(m, n, x, y) {  // all 4 get bound to values
      // we're in a ghost context here
      GhostCallee(m, n, x, y);  // all fine
    }
  }

  method W(cell: SmallCell) {
    if m, x :| cell == SmallGH(m, x) {  // all 2 get bound to values
      // this is still a ghost context
      GhostCallee(m, m, x, x);  // all fine
    }
  }
}

module EmptyTypeNotDeclaredAsSuch {
  type Empty = x: int | false  // error: no witness
}

module EmptyType {
  type Empty = x: int | false witness *

  function F(x: Empty): nat {
    -3  // no problem, since the function can't ever be called
  }

  method M(x: Empty, y: int) {
    var u := 10 / y;  // no problem, since the method can't ever be called
  }

  lemma Bad()
    ensures false
  {  // error (the presence of type Empty should not make verification unsound)
  }

  method EmptyLocal() returns (n: nat) {
    var e: Empty;  // it's okay to declare a variable of type Empty, as long as it's never used
    n := -8;  // error
  }

  lemma EmptyLocalGhost() returns (n: nat) {
    var e: Empty;  // it's okay to declare a variable of type Empty, as long as it's never used
    n := -8;  // error
  }

  datatype WellFoundedButEmpty = WFBE(e: Empty)

  method EmptyLocalDatatype() returns (n: nat) {
    var e: WellFoundedButEmpty;  // it's okay to declare a variable of type Empty, as long as it's never used
    n := -8;  // error
  }

  datatype Cell<X> = Cell(x: X)

  method CellNonemptyPayload(y: int) returns (n: nat) {
    var cell: Cell<int>;
    n := y;  // error: y may be negative
    var cell' := cell;  // fine, since Cell<int> is not under definite-assignment rules
    cell := Cell(y);
  }

  method CellEmptyPayload(y: int) returns (n: nat) {
    var cell: Cell<Empty>;
    n := y;  // error: y may be negative
    if * {
      var cell' := cell;  // error: cell is used before it's been defined
      n := -8;  // error: -8 is not a nat
    } else {
      var e: Empty;
      cell := Cell(e);  // error: e is used before it's been defined
      n := -8;  // control never reaches this point
    }
  }
}
