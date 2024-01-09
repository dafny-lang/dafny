// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits=datatype

trait ProgramTrait {
  method Compute() returns (r: Result)
}

type Program = ProgramTrait | true // error: a subset type (unlike a newtype) must give an identifier-colon

datatype Result =
| Bounce(next: Program)
| Done()

datatype Trivial extends ProgramTrait =
  Trivial()
{
  method Compute() returns (r: Result)
  {
    return Done();
  }
}
