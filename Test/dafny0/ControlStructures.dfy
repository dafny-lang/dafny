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

// --------------- alternative statements ---------------------

method A0(x: int) returns (r: int)
  ensures 0 <= r;
{
  if {  // error: missing case (x == 0)
    case x < 0 => r := 12;
    case 0 < x => r := 13;
  }
}

method A1(x: int) returns (r: int)
  ensures 0 <= r;
{
  if {
    case x <= 0 => r := 12;
    case 0 <= x => r := 13;
  }
}

method DutchFlag(A: array<int>, N: int, l: int, r: int) returns (result: int)
  requires A != null && N == A.Length;
  requires 0 <= l && l+2 <= r && r <= N;
  modifies A;
  ensures l <= result && result < r;
  ensures forall k, j :: l <= k && k < result && result <= j && j < r ==> A[k] <= A[j];
  ensures forall k :: l <= k && k < result ==> A[k] <= old(A[l]);
  ensures forall k :: result <= k && k < r ==> old(A[l]) <= A[k];
{
  var pv := A[l];
  var i := l;
  var j := r-1;
  // swap A[l] and A[j]
  var tmp := A[l]; A[l] := A[j]; A[j] := tmp;

  while (i < j)
    invariant l <= i && i <= j && j < r;
    invariant forall k :: l <= k && k < i ==> A[k] <= pv;
    invariant forall k :: j <= k && k < r ==> pv <= A[k];
  {
    if {
      case A[i] <= pv =>
        i := i + 1;
      case pv <= A[j-1] =>
        j := j - 1;
      case A[j-1] < pv && pv < A[i] =>
        // swap A[j-1] and A[i]
        tmp := A[i]; A[i] := A[j-1]; A[j-1] := tmp;
        assert A[i] < pv && pv < A[j-1];
        i := i + 1;
        j := j - 1;
    }
  }
  result := i;
}

// --------------- alternative loop statements  ---------------

method B(x: int) returns (r: int)
  ensures r == 0;
{
  r := x;
  while
    decreases if 0 <= r then r else -r;
  {
    case r < 0 =>
      r := r + 1;
    case 0 < r =>
      r := r - 1;
  }
}
