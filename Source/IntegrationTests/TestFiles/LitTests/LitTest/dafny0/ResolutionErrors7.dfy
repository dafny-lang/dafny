// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// --------------- ghost function error messages ------------------------------

module GhostFunctionErrorMessages {
  ghost function GhostFunction(): int
  ghost predicate GhostPredicate()
  least predicate LeastPredicate()
  greatest predicate GreatestPredicate()
  twostate function TwoFunction(): int
  twostate predicate TwoPredicate()

  method GhostsUsedInCompiledContexts() {
    var x, b;
    x := GhostFunction(); // error
    b := GhostPredicate(); // error
    b := LeastPredicate(); // error
    b := GreatestPredicate(); // error
    x := TwoFunction(); // error
    b := TwoPredicate(); // error
  }
}

module TypeParameterCount {
  ghost function F0(): int
  ghost function F1<A>(): int
  ghost function F2<A, B>(): int
  method M0()
  method M1<A>()
  method M2<A, B>()

  method TestFunction() {
    var x;
    x := F0();
    x := F1();  // type argument inferred
    x := F2();  // type arguments inferred
    x := F0<int>();  // error: wrong number of type parameters
    x := F1<int>();
    x := F2<int>();  // error: wrong number of type parameters
    x := F0<int, real>();  // error: wrong number of type parameters
    x := F1<int, real>();  // error: wrong number of type parameters
    x := F2<int, real>();
  }

  method TestMethods() {
    M0();
    M1();  // type argument inferred
    M2();  // type arguments inferred
    M0<int>();  // error: wrong number of type parameters
    M1<int>();
    M2<int>();  // error: wrong number of type parameters
    M0<int, real>();  // error: wrong number of type parameters
    M1<int, real>();  // error: wrong number of type parameters
    M2<int, real>();
  }
}

module AutoGhostRegressions {
  datatype Quad<T, U> = Quad(0: T, 1: T, ghost 2: U, ghost 3: U)

  method Test() {
    var q := Quad(20, 30, 40, 50);
    print q, "\n";

    var Quad(a, b, c, d) := q;
    print c, "\n";  // error: c is ghost (this was once not handled correctly)

    match q {
      case Quad(r, s, t, u) =>
        print t, "\n";  // error: t is ghost
    }

    ghost var p := Quad(20, 30, 40, 50);
    var Quad(a', b', c', d') := p;
    print a', "\n";  // error: a' is ghost
    print c', "\n";  // error: c' is ghost
  }

  datatype NoEquality = NoEquality(ghost u: int)
  newtype NT = x | var s: set<NoEquality> := {}; |s| <= x  // fine, since constraint is a ghost context
  type ST = x | var s: set<NoEquality> := {}; |s| <= x  // fine, since constraint is a ghost context
}

module TypeCharacteristicsInGhostCode {
  function MustBeNonempty<T(00)>(): int { 5 }
  function MustBeAutoInit<T(0)>(): int { 5 }
  function MustSupportEquality<T(==)>(): int { 5 }
  function NoReferences<T(!new)>(): int { 5 }

  type PossiblyEmpty = x: int | true witness *
  type Nonempty = x: int | true ghost witness 0
  datatype NoEquality = NoEquality(ghost u: int)
  class Class { }
  type Good = bool

  method TestCompiled<Z>()
  {
    var w;

    w := MustBeNonempty<PossiblyEmpty>();  // error
    w := MustBeNonempty<Nonempty>();
    w := MustBeNonempty<NoEquality>();
    w := MustBeNonempty<Class?>();
    w := MustBeNonempty<Good>();
    w := MustBeNonempty<Z>();  // error (a hint is given)

    w := MustBeAutoInit<PossiblyEmpty>();  // error
    w := MustBeAutoInit<Nonempty>();  // error
    w := MustBeAutoInit<NoEquality>();
    w := MustBeAutoInit<Class?>();
    w := MustBeAutoInit<Good>();
    w := MustBeAutoInit<Z>();  // error (a hint is given)

    w := MustSupportEquality<PossiblyEmpty>();
    w := MustSupportEquality<Nonempty>();
    w := MustSupportEquality<NoEquality>();  // error
    w := MustSupportEquality<Class?>();
    w := MustSupportEquality<Good>();
    w := MustSupportEquality<Z>();  // error (a hint is given)

    w := NoReferences<PossiblyEmpty>();
    w := NoReferences<Nonempty>();
    w := NoReferences<NoEquality>();
    w := NoReferences<Class?>();  // error
    w := NoReferences<Good>();
    w := NoReferences<Z>();  // error (a hint is given)
  }

  method TestGhost()
  {
    ghost var w;

    w := MustBeNonempty<PossiblyEmpty>();  // error
    w := MustBeNonempty<Nonempty>();
    w := MustBeNonempty<NoEquality>();
    w := MustBeNonempty<Class?>();
    w := MustBeNonempty<Good>();

    w := MustBeAutoInit<PossiblyEmpty>();  // error
    w := MustBeAutoInit<Nonempty>();  // fine, because the call appears in a ghost context
    w := MustBeAutoInit<NoEquality>();
    w := MustBeAutoInit<Class?>();
    w := MustBeAutoInit<Good>();

    w := MustSupportEquality<PossiblyEmpty>();
    w := MustSupportEquality<Nonempty>();
    w := MustSupportEquality<NoEquality>();
    w := MustSupportEquality<Class?>();
    w := MustSupportEquality<Good>();

    w := NoReferences<PossiblyEmpty>();
    w := NoReferences<Nonempty>();
    w := NoReferences<NoEquality>();
    w := NoReferences<Class?>();  // error
    w := NoReferences<Good>();
  }

  function FF(a: bool, ghost b: bool): int { 5 }
  method MM(a: bool, ghost b: bool) { }
  function GetInt<T(==)>(): int { 2 }

  method GhostContexts<T>(x: T, y: T) {
    var r;
    r := FF(x == y, true);  // error: T must support equality
    r := FF(true, x == y);  // no problem, since this is a ghost context
    MM(x == y, true);  // error: T must support equality
    MM(true, x == y);  // no problem, since this is a ghost context

    r := FF(GetInt<NoEquality>() == 0, true);  // error: type argument must support equality
    r := FF(true, GetInt<NoEquality>() == 0);  // okay, since this is a ghost context
    MM(GetInt<NoEquality>() == 0, true);  // error: type argument must support equality
    MM(true, GetInt<NoEquality>() == 0);  // okay, since this is a ghost context

    var q0 := Quad(GetInt<NoEquality>() == 0, true, true, true);  // error: type argument must support equality
    var q1 := Quad(true, true, GetInt<NoEquality>() == 0, true);  // fine, since in a ghost context
  }

  datatype Quad<T, U> = Quad(0: T, 1: T, ghost 2: U, ghost 3: U)
  datatype QuadEq<T(==), U(==)> = QuadEq(0: T, 1: T, ghost 2: U, ghost 3: U)

  method VarDecls<T>(x: T, y: T) {
    var a := x == y;  // error: this requires T to support equality
    ghost var b := x == y;  // fine

    var q := Quad(x, y, x, y);
    var Quad(k, l, m, n) := q;  // k,l are compiled; m,n are ghost
    var c := k == l;  // error: this requires T to support equality
    var d := m == n;  // fine, since d is implicitly ghost
    d, c, d := m == n, k == l, m == n;  // error: "k == l" requires T to support equality

    var q' := QuadEq([x], [x], [0], [0]);  // error: seq<T> requires T to support equality (1 error for local var, 1 for datatype ctor)
    var q'' := QuadEq([0], [0], [x], [x]); // error: seq<T> requires T to support equality (1 error for local var, 1 for datatype ctor)
  }

  newtype NT = x | var s: set<NoEquality> := {}; |s| <= x  // fine, since constraint is a ghost context
  type ST = x | var s: set<NoEquality> := {}; |s| <= x  // fine, since constraint is a ghost context

  method LetVarDecls<T>(x: T, y: T) {
    var lhs;
    lhs :=
      var a := x == y;  // error: this requires T to support equality
      0;
    lhs :=
      ghost var b := x == y;  // fine
      0;

    var q := Quad(x, y, x, y);
    var Quad(k, l, m, n) := q;  // k,l are compiled; m,n are ghost
    lhs :=
      var c := k == l;  // error: this requires T to support equality
      0;
    lhs :=
      var d := m == n;  // fine, since d is implicitly ghost
      0;

    ghost var ghostLhs;
    ghostLhs :=
      var a := x == y;  // fine
      0;
    ghostLhs :=
      ghost var b := x == y;  // fine
      0;
  }

  datatype DatatypeHasMembersToo = Abc | Def {
    method Test() {
      var w;
      w := MustBeNonempty<PossiblyEmpty>();  // error
      w := MustBeAutoInit<PossiblyEmpty>();  // error
      w := MustBeAutoInit<Nonempty>();  // error
      w := MustSupportEquality<NoEquality>();  // error
      w := NoReferences<Class?>();  // error
    }
  }

  newtype NewtypeHasMembersToo = x: int | x == MustBeNonempty<PossiblyEmpty>()  // error: constraint has bad type instantiation
    witness MustBeNonempty<PossiblyEmpty>()  // error: witness expression has bad type instantiation
  {
    method Test() {
      var w;
      w := MustBeNonempty<PossiblyEmpty>();  // error
      w := MustBeAutoInit<PossiblyEmpty>();  // error
      w := MustBeAutoInit<Nonempty>();  // error
      w := MustSupportEquality<NoEquality>();  // error
      w := NoReferences<Class?>();  // error
    }
  }

  type SubsetTypeHasExpressionToo = x: int | x == MustBeNonempty<PossiblyEmpty>()  // error: constraint has bad type instantiation
    witness MustBeNonempty<PossiblyEmpty>()  // error: witness expression has bad type instantiation

  newtype NT_CompiledWitness = x | 0 <= x
    witness MustSupportEquality<NoEquality>()  // error
  newtype NT_GhostWitness = x | 0 <= x
    ghost witness MustSupportEquality<NoEquality>()  // fine, since it's ghost
  type ST_CompiledWitness = x | 0 <= x
    witness MustSupportEquality<NoEquality>()  // error
  type ST_GhostWitness = x | 0 <= x
    ghost witness MustSupportEquality<NoEquality>()  // fine, since it's ghost

  trait
    {:MyAttribute MustSupportEquality<NoEquality>(), MustBeNonempty<PossiblyEmpty>()}  // error: about MustBeNonempty (no prob with (==))
    MyTrait
  {
    const x := (CallMyLemma(MustSupportEquality<NoEquality>(), MustBeNonempty<PossiblyEmpty>()); 23)  // error: about MustBeNonempty (no prob with (==))
  }
  lemma CallMyLemma(x: int, y: int)
}

module MoreAutoGhostTests {
  datatype Quad<T, U> = Quad(0: T, 1: T, ghost 2: U, ghost 3: U)

  method SomeLetVarsAreGhost0(q: Quad<int, int>) returns (r: int) {
    r :=
      var Quad(k, l, m, n) := q;  // k,l are compiled; m,n are ghost
      k + l;
  }

  method SomeLetVarsAreGhost1(q: Quad<int, int>) returns (r: int) {
    r :=
      var Quad(k, l, m, n) := q;  // k,l are compiled; m,n are ghost
      m;  // error: m is ghost
  }

  method AssignSuchThat(ghost m: int) {
    var d :| d == m;  // error: LHS is not inferred to be ghost for :|
  }

  function LetSuchThat(ghost m: int): int {
    var d :| d == m;  // error: LHS is not inferred to be ghost for :|
    0
  }
}

module RelaxedAutoInitChecking {
  // In a ghost context, the (==) is never relevant. Therefore, checking of adherence to (==) for
  // type arguments is suppressed in ghost contexts.
  // Similarly, in a ghost context, there's no difference between (0) and (00). Therefore, a
  // formal parameter that expects (0) can take either a (0) or a (00) in a ghost context.

  function MustBeNonempty<T(00)>(): int { 5 }
  function MustBeAutoInit<T(0)>(): int { 5 }
  function MustSupportEquality<T(==)>(): int { 5 }
  function NoReferences<T(!new)>(): int { 5 }

  type PossiblyEmpty = x: int | true witness *
  type Nonempty = x: int | true ghost witness 0
  datatype NoEquality = NoEquality(ghost u: int)
  class Class { }
  type Good = bool

  method M(compiledValue: int, ghost ghostValue: int)

  method TestCompiled()
  {
    M(MustBeNonempty<PossiblyEmpty>(), 0);  // error
    M(MustBeNonempty<Nonempty>(), 0);
    M(MustBeNonempty<NoEquality>(), 0);
    M(MustBeNonempty<Class?>(), 0);
    M(MustBeNonempty<Good>(), 0);

    M(MustBeAutoInit<PossiblyEmpty>(), 0);  // error
    M(MustBeAutoInit<Nonempty>(), 0);  // error
    M(MustBeAutoInit<NoEquality>(), 0);
    M(MustBeAutoInit<Class?>(), 0);
    M(MustBeAutoInit<Good>(), 0);

    M(MustSupportEquality<PossiblyEmpty>(), 0);
    M(MustSupportEquality<Nonempty>(), 0);
    M(MustSupportEquality<NoEquality>(), 0);  // error
    M(MustSupportEquality<Class?>(), 0);
    M(MustSupportEquality<Good>(), 0);

    M(NoReferences<PossiblyEmpty>(), 0);
    M(NoReferences<Nonempty>(), 0);
    M(NoReferences<NoEquality>(), 0);
    M(NoReferences<Class?>(), 0);  // error
    M(NoReferences<Good>(), 0);
  }

  method TestGhost()
  {
    M(0, MustBeNonempty<PossiblyEmpty>());  // error
    M(0, MustBeNonempty<Nonempty>());
    M(0, MustBeNonempty<NoEquality>());
    M(0, MustBeNonempty<Class?>());
    M(0, MustBeNonempty<Good>());

    M(0, MustBeAutoInit<PossiblyEmpty>());  // error
    M(0, MustBeAutoInit<Nonempty>());  // this is fine in a ghost context
    M(0, MustBeAutoInit<NoEquality>());
    M(0, MustBeAutoInit<Class?>());
    M(0, MustBeAutoInit<Good>());

    M(0, MustSupportEquality<PossiblyEmpty>());
    M(0, MustSupportEquality<Nonempty>());
    M(0, MustSupportEquality<NoEquality>());  // this is fine in a ghost context
    M(0, MustSupportEquality<Class?>());
    M(0, MustSupportEquality<Good>());

    M(0, NoReferences<PossiblyEmpty>());
    M(0, NoReferences<Nonempty>());
    M(0, NoReferences<NoEquality>());
    M(0, NoReferences<Class?>());  // error
    M(0, NoReferences<Good>());
  }
}
