// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function SimpleAssert(n: int): int
  ensures n < 100;
{
  assert n == 58;  // error: assert violation
  n  // but postcondition is fine
}

function SimpleAssume(n: int): int
  ensures n < 100;
{
  assume n == 58; n  // all is fine
}

function Subonacci(n: nat): nat
{
  if 2 <= n then
    // proving that this case is a nat requires more information,
    // which is here supplied by an assume expression
    assume Subonacci(n-2) <= Subonacci(n-1);
    Subonacci(n-1) - Subonacci(n-2)
  else
    n
}

function F(n: int): nat
{
  Subonacci(assume 0 <= n; n) -
  Subonacci(n)
}

function G(n: int, b: bool): nat
{
  if b then
    Subonacci(assume 0 <= n; n) + n  // the last n is also affected by the assume
  else
    Subonacci(n)  // error: n may not be a nat
}

ghost method M(m: nat, n: int)
{
  var k := F(m);
  assert k == 0;
  k := F(n);
  assert k == 0;  // this is still known
}

method M0(j: int) returns (n: nat)
{
  n := assert 0 <= j; j;  // error: j may be negative
}

method M1(j: int) returns (n: nat)
{
  n := (assume 0 <= j; j) + (assert 0 <= j; j);
  assert n == 2*j;
}

function SpecOnly(): bool { true }

function method FuncMeth(): int {
  assert SpecOnly();  // this call is allowed, because the .Guard of a
                      // PredicateExpr is not included in compilation
  15
}

method M5(a: int, b: int)
{
  var k := if a < 0 then
             assume b < 0; 5
           else
             5;
  if (*) {
    assert a == -7 ==> b < 0;
    assert b < 0;  // error: this condition does not hold on every path here
  } else {
    assert assume a == -7; b < 0;  // note, this is different than the ==> above
    assert b < 0;  // this condition does hold on all paths to here
  }
}
