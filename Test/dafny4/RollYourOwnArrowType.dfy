// RUN: %dafny /dprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type NoWitness_EffectlessArrow<A,B> = f: A -> B  // error: cannot find witness
  | forall a :: f.reads(a) == {}

type NonGhost_EffectlessArrow<A,B> = f: A -> B
  | forall a :: f.reads(a) == {}
  witness EffectlessArrowWitness<A,B>

// The following compilable function, which is used in the witness clause above, can never
// be implemented, because there is no way to produce a B (for any B) in compiled code.
function method EffectlessArrowWitness<A,B>(a: A): B

type EffectlessArrow<A,B> = f: A -> B
  | forall a :: f.reads(a) == {}
  ghost witness GhostEffectlessArrowWitness<A,B>

function GhostEffectlessArrowWitness<A,B>(a: A): B
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

function method TwoTimes(f: int -> int, x: int): int
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

predicate Total<A,B>(f: A -> B)
  reads f.reads
{
  forall a :: f.reads(a) == {} && f.requires(a)
}

type TotalArrow<A,B> = f: EffectlessArrow<A,B>
  | Total(f)
  ghost witness
    (TotalWitnessIsTotal<A,B>();  // BUG: why is this lemma needed?
     TotalWitness<A,B>)

function TotalWitness<A,B>(a: A): B
{
  var b: B :| true; b
}

lemma TotalWitnessIsTotal<A,B>()
  ensures Total(TotalWitness<A,B>)
{
}

function TotalClientTwice(f: TotalArrow<int,int>, x: int): int
{
  f(f(x))
}
