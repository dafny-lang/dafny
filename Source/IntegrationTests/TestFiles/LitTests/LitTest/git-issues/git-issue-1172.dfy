// RUN: %exits-with 2 %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The following examples show that verification would be unsound if ghost methods would
// be allowed to avoid termination checking.

ghost function F(): int
  ensures false
  decreases *  // error: this is not allowed on a function
{
  F()
}

function G(): int
  ensures false
  decreases *  // error: this is not allowed on a function
{
  G()
}

twostate predicate P2()
  ensures false
  decreases *  // error: this is not allowed on a function
{
  P2()
}

ghost method GM()
  ensures false
  decreases *  // error: this is not allowed on a ghost method
{
  GM();
}

lemma Lemma()
  ensures false
  decreases *  // error: this is not allowed on a lemma
{
  Lemma();
}

twostate lemma L2()
  ensures false
  decreases *  // error: this is not allowed on a lemma
{
  L2();
}

least lemma Least()
  ensures false  // even without the "decreases *", this postcondition would not get passed the verifier
  decreases *  // error: this is not allowed on a lemma
{
  Least#[_k]();
}

method Main()
  decreases *
{
  if {
    case true =>
      var x := F();
    case true =>
      var x := G();
    case true =>
      var p := P2();
    case true =>
      GM();
    case true =>
      Lemma();
    case true =>
      L2();
    case true =>
      Least();
  }
  var x := 1 / 0;  // no error, because all postconditions of the called methods/functions imply "false"
}

// ---------------------- other decreases related errors ----------------------

least predicate Min(x: int)
  decreases x  // error: decreases not allowed on extreme predicates
{
  true
}

greatest predicate Max(x: int)
  decreases x  // error: decreases not allowed on extreme predicates
{
  true
}

least lemma MinLemma(x: int)
  decreases x  // fine
{
  if 0 < x {
    MinLemma(x - 1);
  }
}

greatest lemma MaxLemma(x: int)
  decreases x  // fine
{
  if 0 < x {
    MaxLemma(x - 1);
  }
}

// ---------------------- duplicate *'s ----------------------

method Recursive0(x: int, y: int)
  decreases x, y, *  // error: * can only be mentioned alone in a decreases clause

method Recursive1(x: int, y: int)
  decreases *, x, y  // error: * can only be mentioned alone in a decreases clause

method Recursive2(x: int, y: int)
  decreases x, y
  decreases *  // error: * can only be mentioned alone in a decreases clause

method Recursive3(x: int, y: int)
  decreases *
  decreases x, y  // error: * can only be mentioned alone in a decreases clause

method Recursive4(x: int, y: int)
  decreases x, *, y  // error: * can only be mentioned alone in a decreases clause

method Recursive5(x: int, y: int)
  decreases x, *, y, *  // error: * can only be mentioned alone in a decreases clause

method Recursive6(x: int, y: int)
  decreases *
  decreases x  // error: * can only be mentioned alone in a decreases clause
  decreases *  // error: * can only be mentioned alone in a decreases clause
  decreases y  // error: * can only be mentioned alone in a decreases clause
  decreases *  // error: * can only be mentioned alone in a decreases clause

method Loops(M: int, N: int, O: int, P: int) {
  var i, j, k, l := M, N, O,  P;
  while i != 0
    decreases i, *  // error: * can only be mentioned alone in a decreases clause
  {
    i := i - 1;
  }
  while j != 0
    decreases *, j  // error: * can only be mentioned alone in a decreases clause
  {
    j := j - 1;
  }
  while k != 0
    decreases k
    decreases *  // error: * can only be mentioned alone in a decreases clause
    decreases *  // error: * can only be mentioned alone in a decreases clause
  {
    k := k - 1;
  }
  while l != 0
    decreases *, k  // error: * can only be mentioned alone in a decreases clause
    decreases l, *  // error: * can only be mentioned alone in a decreases clause
  {
    l := l - 1;
  }
}

ghost function Function0(x: object, y: object): int
  reads x, y, *  // error: * can only be mentioned alone in a reads clause

ghost function Function1(x: object, y: object): int
  reads *, x, y  // error: * can only be mentioned alone in a reads clause

ghost function Function2(x: object, y: object): int
  reads x, y
  reads *  // error: * can only be mentioned alone in a reads clause

ghost function Function3(x: object, y: object): int
  reads *
  reads x, y  // error: * can only be mentioned alone in a reads clause

ghost function Function4(x: object, y: object): int
  reads x, *, y  // error: * can only be mentioned alone in a reads clause

ghost function Function5(x: object, y: object): int
  reads x, *, y, *  // error: * can only be mentioned alone in a reads clause

ghost function Function6(x: object, y: object): int
  reads *
  reads x  // error: * can only be mentioned alone in a reads clause
  reads *  // error: * can only be mentioned alone in a reads clause
  reads y  // error: * can only be mentioned alone in a reads clause
  reads *  // error: * can only be mentioned alone in a reads clause
