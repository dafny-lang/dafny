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

function FunctionNotButMethodVerifies(i: int): (r: int)
  requires p: i >= 0
  ensures r >= 0
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
} by method {
  r := i;
}

function NeitherVerify(i: int): (r: int)
  requires p: i >= 0
  ensures r >= 0
{
  i
} by method {
  r := i;
}