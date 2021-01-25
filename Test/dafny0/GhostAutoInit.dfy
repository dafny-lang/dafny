// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module DeclaredTypes {
  // type KnownToBeEmpty = x: int | false  // TODO
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
  method NotUsed<MaybeEmpty, GhostAutoInit(0)/*TODO*/, CompileAutoInit(0)>() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
  }

  method Used<MaybeEmpty, GhostAutoInit(0)/*TODO*/, CompileAutoInit(0)> () {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      var x := a;  // error: a has not been initialized
    case true =>
      // TODO: var x := b;
    case true =>
      var x := c;
  }

  method GhostUsed<MaybeEmpty, GhostAutoInit(0)/*TODO*/, CompileAutoInit(0)>() {
    var a: MaybeEmpty;
    var b: GhostAutoInit;
    var c: CompileAutoInit;
    if
    case true =>
      ghost var x := a;  // error: a has not been initialized
    case true =>
      // TODO: ghost var x := b;
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
