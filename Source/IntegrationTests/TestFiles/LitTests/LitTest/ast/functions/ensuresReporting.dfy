// RUN: ! %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

function ElseError(x: int): int
  ensures ElseError(x) == 0
{
  if x == 0 then
    0 
  else 
    1 // error
}
function ThenError(x: int): int
  ensures ThenError(x) == 0
{
  if x == 0 then
    1 // error
  else 
    0 
}

function CaseError(x: int): int
  ensures CaseError(x) == 1
{
  match x {
    case 0 => 1
    case 1 => 0 // error
    case _ => 1 
  }
}

function LetError(x: int): int
  ensures LetError(x) == 1
{
  var r := 3;
  r
}