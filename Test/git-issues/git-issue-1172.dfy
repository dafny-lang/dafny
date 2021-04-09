// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The following examples show that verification would be unsound if ghost methods would
// be allowed to avoid termination checking.

function F(): int
  ensures false
  decreases *  // error: this is not allowed on a function
{
  F()
}

function method G(): int
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
