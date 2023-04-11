// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function RevealInFunctionNotMethodOk(i: int): (r: int)
  requires p: i >= 0
  ensures r >= 0
{
  reveal p;
  i
} by method {
  r := i;
}

function NoRevealNotOk(i: int): (r: int) // Error: Could not verify
  requires p: i >= 0
  ensures r >= 0  // Error: related
{
  i
} by method { // Error: Could not verify + related
  r := i;
}

function RevealOnlyInMethodNotOk(i: int): (r: int) // Error: Could not verify
  requires p: i >= 0
  ensures r >= 0 // Related condition
{
  i
} by method {
  reveal p;  // Useless
  r := i;
}

function EnsureRevealPreconditionForComparisonWithFunction(i: int): (r: int)
  requires p: i >= 0
  ensures r >= 0
{
  reveal p;
  i
} by method {
  assert problem: i >= 0; // Error: Cannot prove
  assert cando: i >= 0 by {
    reveal p;
  }
  if(i < -2) {
    return -1; // A return reveals the requires for comparison with function so Dafny is OK.
  }

  assert problem2: i >= 0; // Error: Cannot prove
  assert cando2: i >= 0 by {
    reveal p;
  }
  if(i < 0) {
    return -1; // A return reveals the requires for comparison with function so Dafny is OK.
  }
  // Here Dafny knows that i >= 0;
  assert problem3: i >= 0; // Can prove
  assert cando3: i >= 0 by {
    reveal p;
  }
  r := i; // No error here to check if r == F(i) because Boogie only assume .requires(i) before returning.
}