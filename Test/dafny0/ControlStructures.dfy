datatype D = Green | Blue | Red | Purple;

method M0(d: D)
{
  match (d) {  // error: two missing cases: Blue and Purple
    case Green =>
    case Red =>
  }
}

method M1(d: D)
  requires d != #D.Blue;
{
  match (d) {  // error: missing case: Purple
    case Green =>
    case Red =>
  }
}

method M2(d: D)
  requires d != #D.Blue && d != #D.Purple;
{
  match (d) {
    case Green =>
    case Red =>
  }
}

method M3(d: D)
  requires d == #D.Green;
{
  if (d != #D.Green) {
    match (d) {
      // nothing here
    }
  }
}

method M4(d: D)
  requires d == #D.Green || d == #D.Red;
{
  if (d != #D.Green) {
    match (d) {  // error: missing case Red
      // nothing here
    }
  }
}

function F0(d: D): int
{
  match (d)  // error: missing cases Red
  case Purple => 80
  case Green => 0
  case Blue => 2
}

function F1(d: D, x: int): int
  requires x < 100;
  requires d == #D.Red ==> x == 200;  // (an impossibility, given the first precondition, so d != Red)
{
  match (d)
  case Purple => 80
  case Green => 0
  case Blue => 2
}
