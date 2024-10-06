// RUN: ! %verify --progress --cores=1 %s &> %t
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK:Verified 1/5 of Assertion: assertion at line 28, through \[15,23\], could not prove all assertions
// CHECK:Verified 2/5 of Assertion: assertion at line 28, through \[18,23\], verified successfully
// CHECK:Verified 3/5 of Assertion: assertion at line 28, through \[15,25\], verified successfully
// CHECK:Verified 4/5 of Assertion: assertion at line 28, through \[18,25\], verified successfully
// CHECK:Verified 5/5 of Assertion: remaining body, verified successfully
// CHECK:Verified 1/3 of Return: assertion at line 45, through \[37\], could not prove all assertions
// CHECK:Verified 2/3 of Return: assertion at line 45, through \[40\], verified successfully
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
  r := if r == 0 then r else r;
  match y {
    case 0 => 
      r := r + 3;
    case _ =>
      r := r + 4;
  }
  assert {:isolate "paths"} r > 4;
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
    return {:isolate "paths"};
  }

  return 1;
}
