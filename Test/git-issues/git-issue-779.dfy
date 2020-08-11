// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Lines marked BOGUS were problems before this bug was fixed

method GenericMethod<X>(x: X) { }
method GenericMethodWithResult<X>(x: X) returns (y: int) { }
function method GenericFunction<X>(x: X): int { 5 }

method Main() {
  var r: int;

  // The following work and infer the type of each of a0, a1, and a2 to be "nat"
  var a0, a1, a2;
  GenericMethod<nat>(a0);
  r := GenericMethodWithResult<nat>(a1);
  r := GenericFunction<nat>(a2);

  // The following should also work and should infer the type of each of b0, b1, and b2 to be "nat -> bool"
  var b0, b1, b2;
  GenericMethod<nat -> bool>(b0);                 // BOGUS: gives "invalid UpdateStmt"
  r := GenericMethodWithResult<nat -> bool>(b1);  // BOGUS: gives "invalid UnaryExpression"
  r := GenericFunction<nat -> bool>(b2);          // BOGUS: gives "invalid UnaryExpression"

  // The same problem occurs with the arrow types "nat ~> bool" and "nat --> bool"

  // The following should also work and should infer the type of each of c0, c1, and c2 to be "nat -> bool"
  var c0, c1, c2;
  GenericMethod<int -> bool>(c0);                 // BOGUS: gives "invalid UpdateStmt"
  r := GenericMethodWithResult<int -> bool>(c1);  // BOGUS: thinks "int" is start of deprecated "int(Expr)" conversion
  r := GenericFunction<int -> bool>(c2);          // BOGUS: thinks "int" is start of deprecated "int(Expr)" conversion
}

