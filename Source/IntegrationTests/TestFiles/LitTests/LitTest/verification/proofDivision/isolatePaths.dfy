// RUN: ! %verify --progress Batch --cores=1 %s &> %t.raw
// RUN: %sed 's#\(time.*\)#<redacted>#g' %t.raw > %t
// RUN: %diff "%s.expect" "%t"

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
