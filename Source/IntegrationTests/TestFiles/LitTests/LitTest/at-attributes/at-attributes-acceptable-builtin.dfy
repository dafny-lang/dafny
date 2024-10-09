// RUN: %resolve "%s"
// Attributes on top-level declarations

@Options("--function-syntax:3")
module SimpleLinearModule {
}

function f(x:int) : bool
  requires x > 3
{
  x > 7
}

@Compile(true)
@Fuel(low := 1)
@Fuel(low := 1, high := 2)
function g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}

@IsolateAssertions
method Test(a: int, b: int, c: int)
  requires a < b && b < c
{
  assert a < c; 
  assert c > a;
}

datatype Unary = Zero | Succ(Unary)

function UnaryToNat(n: Unary): nat {
  match n
  case Zero => 0
  case Succ(p) => 1 + UnaryToNat(p)
}

function NatToUnary(n: nat): Unary {
  if n == 0 then Zero else Succ(NatToUnary(n - 1))
}

@Induction(n)
lemma ByInduction(n: int){

}