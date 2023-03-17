// RUN: %exits-with 2 %dafny /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function E(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    E(x, y - 1) // the "+ 0" ruins the chance of a ghost-ITE transformation
  else
    E(x - 1, 65) + 13
}

function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then // error: ghost variable not allowed here
    F(x + 0, y - 1) // the "+ 0" ruins the chance of a ghost-ITE transformation
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

function L(x: nat, ghost y: nat): nat
{
  10 + // this renders the RHS ineligible for a ghost-ITE transformation
    if x == 0 then
      0
    else if y != 0 then // error: ghost variable not allowed here
      L(x, y - 1)
    else
      L(x - 1, 65) + 13
}

function M(x: nat, ghost y: nat): nat
{
  (
    var sixtyFive := 65;
    assert 0 <= sixtyFive;
    (
      if x == 0 then
        sixtyFive - sixtyFive
      else if y != 0 then
        M(x, sixtyFive + y - 66)
      else
        M(x - 1, sixtyFive) + 13
    )
  )
}

function N(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if 3 <= y then
    var z := x + x;
    // the terminal expressions of the following is: N(x, y - 1), N(x, y - 2)
    var a, b, c := 100, if x < z then N(x, y - 1) else N(x, y - 2), 200;
    assert a + b + c == N(x, y - 1) + 300;
    if y + a < 500 then b else b
  else
    N(x - 1, 60) + 13
}

function O(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if 4 <= y then
    var z := x + x;
    // the terminal expressions of the following is: O(x, y - 1), O(x, y - 2), O(x, y - 3), O(x, y - 4)
    var a, b, c, d := 100, if x < z then O(x, y - 1) else O(x, y - 2), 200, O(x, y - 3);
    assert a + b + c == O(x, y - 1) + 300;
    if y + a < 500 then b else if y + a < 700 then d else O(x, y - 4)
  else
    O(x - 1, 60) + 13
}

function P(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if 3 <= y then // error: y is ghost
    var z := x + x;
    // the "x + 0" in the following line ruins the chance of a ghost-ITE transformation
    var a, b, c, d := 100, if x < z then P(x, y - 1) else P(x + 0, y - 2), 200, P(x, y - 3);
    assert a + b + c == P(x, y - 1) + 300;
    if y + a < 500 then b else d // error: y is ghost
  else
    P(x - 1, 60) + 13
}

function Q(x: nat): nat
{
  ghost var u := x;
  if 100 <= u then // error: u is ghost
    Q(x) + 3
  else
    Q(x - 3)
}

class Natty {
  ghost const u: nat
  constructor (u: nat) {
    this.u := u;
  }
}

function R(x: nat, n: Natty): nat
{
  ghost var u := n.u;
  // The resolver is cool with the following, despite the fact that the if-then-else test
  // is a ghost expression. However, if passed to the verifier, the verifier would report a
  // failure to terminate. If the verifier is ignored and the code nevertheless compiled
  // (which is not sound, and any user who requests this is asking for trouble), then the
  // compiler will, on the resolver's advice, compile the entire method body as just
  // R(x - 3, n).
  if 100 <= u then
    R(x - 3, n)
  else
    R(x, n) // this is a failure to terminate (but the verifier is not run on this file)
}

function S(x: nat, n: Natty): nat
{
  ghost var u := n.u;
  // The following is like in R above, but with the cases reversed.
  if 100 <= u then
    S(x, n) // this is a failure to terminate (but the verifier is not run on this file)
  else
    S(x - 3, n) // this is a failure to pass in x as a nat (but the verifier is not run on this file)
}

function T(x: nat, n: Natty): nat
{
  ghost var u := n.u;
  if 100 <= u then // error: u is ghost
    T(x - 3, n)
  else
    T(x - 3, n)
}
