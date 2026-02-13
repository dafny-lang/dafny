// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

codatatype IList<X> = Nil | ICons(head: X, tail: IList<X>)

lemma ITest<X, Y>(xs: IList<X>, y: Y) {
  var b0 := y < xs; // error: < expects one operand to be an inductive datatype, not a codatatype
  var b1 := xs > y; // error: > expects one operand to be an inductive datatype, not a codatatype
}
