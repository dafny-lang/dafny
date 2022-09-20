datatype Option<V> = Some(v: V) | None

datatype X = X(ghost i: int)

datatype Y = Y(s: Option<X>)

method Main()
{
  var y1 := Y(Some(X(0)));
  var y2 := Y(Some(X(1)));

  // Dafny verifier knows that (mathematically) `y1 == y2` is false
  // But it evaluates to true at runtime
  if y1 == y2 {
    var c := 1 / 0;
  }
}
