// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --show-hints --isolate-assertions --suggest-proof-refactoring --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Id(i: int): int { i }

function Square(i: int): int { Id(i) * Id(i) }

function Zero(i: int): int { i * 0 }


method ResultIsUnused() returns (r: int)
  ensures true
{
  r := Square(Square(3));
}

method UnusedAssignment() returns (r: int)
  ensures r == 3
{
  r := Zero(Square(3));
  r := r + 3;
}

method ReferencedFunctionsAreUsed() returns (r: int)
  ensures r == 81
{
  if Square(Square(3)) > 9 {
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
  match Zero(Square(3)) {
    case 0 => { r := 0; }
    case _ => {}
  }
}

method HiddenSquare() returns (r: int)
  ensures r == 0
{
  hide Square;
  r := Zero(Square(3));
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
