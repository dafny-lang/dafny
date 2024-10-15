// RUN: ! %verify --progress --cores=1 %s &> %t
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK:Verified 1/3 of Assertion: assertion at line 18, could not prove all assertions
// CHECK:Verified 2/3 of Assertion: assertion at line 26, verified successfully
// CHECK:Verified 3/3 of Assertion: remaining body, verified successfully
// CHECK:Verified 1/3 of Return: return at line 48, could not prove all assertions
// CHECK:Verified 2/3 of Return: return at line 43, could not prove all assertions
// CHECK:Verified 3/3 of Return: remaining body, could not prove all assertions

method Assertion(x: int, y: int) returns (r: int) {
  r := 0;
  if x > 0 
  { 
    r := r + 1;
  } else 
  {
    r := r + 2;
  }
  assert {:isolate} r > 2;
  r := if r == 0 then r else r;
  match y {
    case 0 => 
      r := r + 3;
    case _ =>
      r := r + 4;
  }
  assert {:isolate} r > 4;
}


method Return(x: int, y: int) returns (r: int)
  ensures r > 1
{
  r := 0;
  if x > 0 
  { 
    r := r + 1;
  } else 
  {
    r := r + 2;
  }

  if (y > 0) {
    return {:isolate};
  }

  var i := x;
  while(i > 0) {
    return {:isolate} 1;
    i := i - 1;
  }

  return 1;
}

method Continue() {
  var i := 3;
  var r := 0;
  while(i > 0)
    invariant r < 3 - i + 1
  {
    i := i - 1;
    if (i == 2) {
      r := r + 2;
      continue {:isolate};
    } else {
      r := r + 1;
    }
  }
}