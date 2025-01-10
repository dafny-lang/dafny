// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

module A
{
  export
    provides T

  newtype T = int
}

module B
{
  import A
  type X = A.T
}