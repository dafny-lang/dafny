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
    Subonacci(assume 0 <= n; n)
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
