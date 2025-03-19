// From these parsers, we can create displayers
// and prove the roundtrip displayer / parser if we wanted to
abstract module Std.Parsers.Displayers {
  import Parsers = Core`All

  type Parser<R> = Parsers.Parser<R>
  type C = Parsers.C
  type Input(!new) = Parsers.Input

  type Displayer<-R> = (R, Input) -> Input

  function Concat<A, B>(
    left: Displayer<A>,
    right: Displayer<B>
  ): Displayer<(A, B)> {
    (ab: (A, B), remaining: Input) =>
      var remaining2 := right(ab.1, remaining);
      var remaining3 := left(ab.0, remaining2);
      remaining3
  }

  ghost predicate Roundtrip<A(!new)>(parse: Parser<A>, display: Displayer<A>)
    // The parser and the displayer are dual to each other
    // means that if we parse after printing, we get the same result
  {
    forall a: A, remaining: Input ::
      parse(display(a, remaining)) == Parsers.ParseSuccess(a, remaining)
  }

  lemma {:rlimit 1000} ConcatRoundtrip<A(!new), B(!new)>(
    pA: Parser<A>, ppA: Displayer<A>,
    pB: Parser<B>, ppB: Displayer<B>
  )
    requires Roundtrip(pA, ppA) && Roundtrip(pB, ppB)
    ensures Roundtrip(Parsers.Concat(pA, pB), Concat(ppA, ppB))
  {
    reveal Parsers.Concat();
    var p := Parsers.Concat(pA, pB);
    var d := Concat(ppA, ppB);
    forall ab: (A, B), remaining: Input ensures
        p(d(ab, remaining)) == Parsers.ParseSuccess(ab, remaining)
    {
      var remaining2 := ppB(ab.1, remaining);
      var remaining3 := ppA(ab.0, remaining2);
      calc {
        p(d(ab, remaining));
        p(remaining3);
        Parsers.ParseSuccess(ab, remaining);
      }
    }
  }
}