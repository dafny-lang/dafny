// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --show-hints --isolate-assertions --suggest-proof-refactoring --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


//Function Hiding

function Id(i: int): int { i }

function Pow(i: int): int { Id(i) * Id(i) }

function Zero(i: int): int { i * 0 }


method NoEffect() returns (r: int)
  ensures true
{
  r := Pow(Pow(3));
}

method Shallow() returns (r: int)
  ensures r == 3
{
  r := Zero(Pow(3));
  r := r + 3;
}

method Deep() returns (r: int)
  ensures r == 81
{
  if Pow(Pow(3)) > 9 {
    r := 81;
  } else {
    r := -81;
  }
}

method HiddenId() returns (r: int)
  ensures r == 0
{
  hide Id;
  r := -1;
  match Zero(Pow(3)) {
    case 0 => { r := 0; }
    case _ => {}
  }
}

method HiddenPow() returns (r: int)
  ensures r == 0
{
  hide Pow;
  r := Zero(Pow(3));
  var i := 3;
  while i > 0
    invariant r == 3 - i
    decreases i
  {
    r := r+1;
    i := i-1;
  }
  r := r - 3;
}

// By-proofs

opaque predicate P() { true }

method M() requires P() { }

method N() ensures P() { reveal P(); }

method NoSuggestion()
{
  N();
  M();
}

method Call()
{
  assert P() by { reveal P(); }
  M();
}

method CallFixed()
{
  M() by {
    assert P() by { reveal P(); }
  }
}

method Requires()
  requires P()
{
  assert P();
}

method RequiresFixed()
  requires p: P()
{
  assert P() by {
    reveal p;
  }
}

method CantMove(){
  var b := P();
  assert b by { reveal P(); }
  b := !b;
  assert !b;
}