// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(x: int): int
  decreases G(x) // error: decreases clause cannot use mutually recursive function
{
  G(x) - 1
}

function G(x: int): int
  decreases F(x) // error: decreases clause cannot use mutually recursive function
{
  F(x)
}

function K(x: nat): int
  decreases if x == 0 then 0 else 1 + K(x - 1) // error: decreases clause is not allowed to call enclosing function
{
  if x == 0 then 200 else 1 + K(x - 1)
}

function Id(x: int): int {
  IdBuddy(x)
}

function IdBuddy(x: int): int
  decreases x, 0
{
  if x <= 0 then x else
    var id := Id; // error: cannot use Id naked here
    id(x - 1)
}

ghost function H(x: int): int {
  if H != (H) then 0 else 3 // error (x2): cannot use H naked here
}

datatype Dt = Dt {
  ghost function J(x: int): int {
    if (this).J == J then 0 else 3 // error (x2): cannot use J naked here
  }
}
