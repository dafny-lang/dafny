// RUN: %dafny /compile:0 /rprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function F<A>(l: seq<A>): bool {
  forall i :: 0 <= i < |l|-1 ==> l[i] == l[i + 1] || l[i] == l[i + 1]
}

