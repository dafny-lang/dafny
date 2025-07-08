// RUN: %testDafnyForEachResolver "%s" -- --general-traits:datatype

trait Tr1 {
  function Decrease(): nat {
    0
  }

  function F(): nat
    decreases Decrease()
}

datatype Dt1 extends Tr1 = Dt {
  function F(): nat
    decreases 0
  {
    0
  }
}

trait Tr2<A> {
  function Decrease(): nat {
    0
  }

  function F(): A
    decreases Decrease()
}

datatype Dt2 extends Tr2<nat> = Dt {
  function F(): nat
    decreases 0
  {
    0
  }
}

trait ProgramTrait {
  function Rank(): nat

  method Compute() returns (r: Result)
    decreases Rank()
}

datatype Result = Bounce(next: ProgramTrait) | Done

datatype Trivial extends ProgramTrait = Trivial
{
  function Rank(): nat { 0 }

  method Compute() returns (r: Result)
    decreases Rank()
  {
    return Done();
  }
}
