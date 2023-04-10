// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function FunctionAndMethodVerify(i: int): (r: int)
  requires p: i >= 0
  ensures r >= 0
{
  reveal p;
  i
} by method {
  reveal p;
  r := i;
}

function FunctionNotButMethodVerifies(i: int): (r: int) // Error: Could not verify
  requires p: i >= 0
  ensures r >= 0 // Related condition
{
  i
} by method {
  reveal p;
  r := i;
}

function FunctionVerifiesButNotMethod(i: int): (r: int)
  requires p: i >= 0
  ensures r >= 0
{
  reveal p;
  i
} by method { // Error: Could not verify + related
  r := i;
}

function NeitherVerify(i: int): (r: int) // Error: Could not verify
  requires p: i >= 0
  ensures r >= 0  // Error: related
{
  i
} by method { // Error: Could not verify + related
  r := i;
}