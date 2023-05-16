// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream<X> = Nil | Cons(head: X, tail: Stream<X>)

least predicate Finite<Y>(s: Stream<Y>) {
  // The following once generated malformed Boogie, because of a missing
  // type substitution in the datatype value Nil
  s == Nil || Finite(s.tail)
}

least predicate F0<Y>(s: Stream<Y>) {
  var nil := Nil;
  s == nil || F0(s.tail)
}

least predicate F1<Y>(s: Stream<Y>) {
  s.Nil? || F1(s.tail)
}

least predicate G0<Y>(s: Stream<Y>) {
  s is Stream<Y>
}

least predicate G1<Y>(s: Stream<Y>) {
  s == Identity(s)
}

least predicate G2<Y>(s: Stream<Y>) {
  s == Identity<Stream<Y>>(s)
}

ghost function Identity<W>(w: W): W { w }

least lemma About<Z>(s: Stream<Z>)
  requires s == Nil
  requires s.Nil?
  requires var nil := Nil; s == nil
  requires s is Stream<Z>
  requires s == Identity(s)
  requires s == Identity<Stream<Z>>(s)
  requires Finite(s)
  requires F0(s)
  requires F1(s)
  requires G0(s)
  requires G1(s)
  requires G2(s)
{
}
