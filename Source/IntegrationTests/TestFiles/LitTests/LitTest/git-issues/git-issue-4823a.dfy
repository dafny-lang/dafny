// RUN: %baredafny verify %args --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Hello {
  trait Censored {
    ghost function Decrease(): int {
      0
    }

    ghost function NotCensored(): int
      decreases Decrease()
  }

  datatype Bar extends Censored =
    | Foo
  {
    opaque ghost function NotCensored(): int
      decreases 0
    {
      0
    }
  }
}