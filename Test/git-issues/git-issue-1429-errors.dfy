// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
	
datatype Option<V> = Some(v: V) | None

datatype X = X(ghost i: int)

datatype Y = Y(s: Option<X>)

method Main()
{
  var x1 := Y(Some(X(0)));
  var x2 := Y(Some(X(1)));
	var y := x1 == x2;
}
