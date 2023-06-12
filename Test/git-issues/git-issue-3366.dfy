// RUN: %exits-with 2 %baredafny verify --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C<T> {
  constructor (x: T) {}
}

datatype O<T> = Some(x: T) | None

method main() {
  // works
  var v := new C<nat>(0);
  var c := Some(v);

  // fails when inlining v
  var c2 := Some(new C<nat>(0));
}
