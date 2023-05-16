// RUN: %exits-with 4 %dafny /errorLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
*  This file demonstrates verification errors related to pattern matching
*/

// missing case in match expression : Nil

datatype List<T> = Nil | Cons(head: T, tail: List)

ghost function F(xs: List<int>): int {
  match xs
  case Cons(x, Cons(y, rest)) => 5
  case Nil => 8
}

// missing case in match statement

method N(xs: List<int>) returns (r: int)
{
  match xs {
    case Cons(y, Cons(z, zs)) => return z;
    case Nil => return 0;
  }
}

// Not all possibilities for constants of type real have been covered

method U(d: real) {
  match d
  case 15.0 =>
}

// More test about missing cases in presence of complexe structures and literals

datatype Tree = Leaf | Branch(left:Tree, b:bool, right: Tree)

method TreeTest(t:Tree) {
  match t {
    case Branch(Branch(left, true, right1), b, right2) =>
    case Branch(Leaf, b, Leaf) =>
  }
}


// value does not satisfy the subset constraints of 'nat'

datatype Dt = Make(d: int)

function GetNat(dt: Dt): nat {
  match dt
  case Make(y) => y
}

// postcondition might not hold on this return path (in least lemma)

datatype cmd = Inc | Seq(cmd, cmd) | Repeat(cmd)
type state = int

least predicate BigStep(c: cmd, s: state, t: state)
{
  match c
  case Inc =>
    t == s + 1
  case Seq(c0, c1) =>
    exists s' :: BigStep(c0, s, s') && BigStep(c1, s', t)
  case Repeat(body) =>
    s == t ||
    exists s' :: BigStep(body, s, s') && BigStep(c, s', t)
}

least lemma BadMonotonic1(c: cmd, s: state, t: state)
  requires BigStep(c, s, t)
  ensures s == t  // error: does not hold
{
  match c
  case Inc =>
  case Seq(c0, c1) =>
    var s' :| BigStep(c0, s, s') && BigStep(c1, s', t);
    BadMonotonic1(c0, s, s');
    BadMonotonic1(c1, s', t);
  case Repeat(body) =>
    if s == t{
    } else {
      var s' :| BigStep(body, s, s') && BigStep(c, s', t);
      BadMonotonic1(body, s, s');
      BadMonotonic1(c, s', t);
    }
}


// postcondition might not hold on this return path (in method)

method PostTest(xs: List<int>) returns (r: int)
  ensures r == 0;
{
  match xs {
    case Cons(y, Cons(z, zs)) => return z;
    case Cons(y, Nil) => return 0;
    case Nil => return 0;
  }
}

