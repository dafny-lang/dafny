// RUN: %exits-with 2 %dafny /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function E(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    E(x, y - 1) // the "+ 0" is what changes the 
  else
    E(x - 1, 65) + 13
}

function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then // error: ghost variable not allowed here
    F(x + 0, y - 1) // the "+ 0" is what changes the 
  else
    F(x - 1, 65) + 13
}

function G(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    G((x), y - 1) // parentheses are okay
  else
    G(x - 1, 65) + 13
}

function H(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else (if y != 0 then // parentheses around the entire expression are also okay
    H(x, y - 1)
  else
    H(x - 1, 65) + 13)
}

function K(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    // all good in the following
    (
    var u := 15;
     assert u == 15;
     (
      K(x, y - 1)
      )
      )
  else
    K(x - 1, 65) + 13
}
