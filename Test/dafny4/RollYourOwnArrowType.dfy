// RUN: %exits-with 4 %dafny /dprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ----- arrows with no read effects -------------------------------------

type NoWitness_EffectlessArrow<!A(!new), B> = f: A ~> B  // error: cannot find witness
  | forall a :: f.reads(a) == {}

type NonGhost_EffectlessArrow<!A(!new), B> = f: A ~> B
  | forall a :: f.reads(a) == {}
  witness EffectlessArrowWitness<A, B>

// The following compilable function, which is used in the witness clause above, can never
// be implemented, because there is no way to produce a B (for any B) in compiled code.
function method EffectlessArrowWitness<A, B>(a: A): B

type EffectlessArrow<!A(!new), B(00)> = f: A ~> B
  | forall a :: f.reads(a) == {}
  ghost witness GhostEffectlessArrowWitness<A, B>

function GhostEffectlessArrowWitness<A, B(00)>(a: A): B
{
  var b: B :| true; b
}


function method Twice(f: EffectlessArrow<int,int>, x: int): int
  requires forall x :: f.requires(x)
{
  var y := f(x);
  f(y)
}

function method Twice'(f: EffectlessArrow<int,int>, x: int): int
  reads f.reads
  requires forall x :: f.requires(x)
{
  f(f(x))
}

function method Twice''(f: EffectlessArrow<int,int>, x: int): int
  reads f.reads
  requires forall x :: f.requires(x)
{
  assert f.requires(f(x));  // this is another workaround to the problem with Twice'
  f(f(x))
}

function method TwoTimes(f: int ~> int, x: int): int
  requires forall x :: f.reads(x) == {}
  requires forall x :: f.requires(x)
{
  f(f(x))
}

function method Inc(x: int): int
{
  x + 1
}

method Main()
{
  var y := TwoTimes(Inc, 3);
  assert y == 5;
  var z := Twice(Inc, 12);
  assert z == 14;
}

// ----- totality constraint by predicate Total -------------------------------------

predicate Total<A(!new), B>(f: A ~> B)  // (is this (!new) really necessary?)
  reads f.reads
{
  forall a :: f.reads(a) == {} && f.requires(a)
}

type TotalArrow<!A(!new), B(00)> = f: EffectlessArrow<A, B>
  | Total(f)
  ghost witness TotalWitness<A, B>

function TotalWitness<A, B(00)>(a: A): B
{
  var b: B :| true; b
}

lemma TotalWitnessIsTotal<A, B>()
  ensures Total(TotalWitness<A, B>)
{
}

function TotalClientTwice(f: TotalArrow<int,int>, x: int): int
{
  f(f(x))
}

// ----- inlined totality constraint -------------------------------------

type DirectTotalArrow<!A(!new), B(00)> = f: EffectlessArrow<A, B>
  | forall a :: f.requires(a)
  ghost witness TotalWitness<A, B>

lemma DirectTotalWitnessIsTotal<A(!new), B(00)>(f: DirectTotalArrow<A, B>)
  ensures Total(TotalWitness<A, B>)
{
}

function DirectTotalClientTwice(f: DirectTotalArrow<int,int>, x: int): int
{
  f(f(x))
}

// ----- using two predicates, and showing which conjunct of constraint is violated ------

predicate EmptyReads<A(!new), B>(f: A ~> B)  // (is this (!new) really necessary?)
  reads f.reads
{
  forall a :: f.reads(a) == {}
}

predicate TruePre<A(!new), B>(f: A ~> B)  // (is this (!new) really necessary?)
  reads f.reads
{
  forall a :: f.requires(a)
}

type TwoPred_TotalArrow<!A(!new), B(00)> = f: A ~> B
  | EmptyReads(f) && TruePre(f)
  ghost witness TotalWitness<A, B>

predicate SomeCondition<A>(a: A)

function PartialFunction<A, B(00)>(a: A): B
  requires SomeCondition(a)
{
  var b: B :| true; b
}

type Bad_TwoPred_TotalArrow<!A(!new), B(00)> = f: A ~> B
  | EmptyReads(f) && TruePre(f)
  // cool: the type instantiation of "PartialFunction" below is inferred
  ghost witness PartialFunction  // error: the second conjunct of the constraint is not satisfied

// ----- Interaction between user-defined conditions and built-in arrows -----

method Any_to_Partial(f: int ~> int) returns (g: int --> int)
  requires forall x :: f.reads(x) == {}
{
  g := f;
}

method Partial_to_Any(g: int --> int) returns (f: int ~> int)
  ensures forall x :: f.reads(x) == {}
{
  f := g;
}

method Partial_to_Total(g: int --> int) returns (tot: int -> int)
  requires forall x :: g.requires(x)
{
  tot := g;
}

method Total_to_Partial(tot: int -> int) returns (g: int --> int)
  ensures forall x :: g.requires(x)
{
  g := tot;
}


method Any_to_Total(f: int ~> int) returns (tot: int -> int)
  requires forall x :: f.reads(x) == {} && f.requires(x)
{
  tot := f;
}

method Total_to_Any(tot: int -> int) returns (f: int ~> int)
  ensures forall x :: f.reads(x) == {} && f.requires(x)
{
  f := tot;
}
