// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


// alas, whether or not a '-' is deemed to be a map subtraction is determined by
// what is known when type checking first reaches the operator
method TooEagerResolution(m: map<int, real>, n: map<int, real>, s: set<int>)
{
  // all fine here:
  var a, b;
  var r := a + b;
  a, b := m, n;

  // here, we see a consequence of the eager operator selection:
  var g, t;
  // since it's not yet known that g is a map, the next line will resolve to any '-' other than
  // map subtraction
  var r1 := g - t;  // this picks the wrong '-'
  g, t := m, s;  // error: the error is reported here
}
