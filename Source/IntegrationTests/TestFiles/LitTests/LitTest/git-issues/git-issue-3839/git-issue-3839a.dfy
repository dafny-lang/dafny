// RUN: ! %baredafny test --use-basename-for-filename --show-snippets:false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:test} M(x: int) returns (r: int) // error: in-parameters not supported
{
  expect x != x;
  return x;
}

method {:test} MethodWithTypeParameters<X(0)>() returns (y: X) { // error: type parameters not supported
  y := *;
}

method {:test} MethodWithTypeParameter<X>() returns (u: seq<X>) { // error: type parameters not supported
  u := [];
}

predicate {:test} UnusedTypeParameterForFunctionByMethod<A>() { // error: type parameters not supported
  true
} by method {
  return true;
}
