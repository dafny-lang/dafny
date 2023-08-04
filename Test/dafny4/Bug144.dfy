// RUN: %exits-with 4 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate p(i: int)

method m1()

method m2()
{
  assume exists i :: p(i);
  assert exists i :: p(i);
  m1();
  assert exists i :: p(i); // this once failed, but should succeed
}

class Test
{
  var arr: array<int>

  ghost predicate p(i: int)

  method foo()
    requires arr.Length > 0
    modifies arr
  {
    assume exists i :: p(i);
    arr[0] := 1;
    assert exists i :: p(i); // this once failed, but should succeed
  }
}

ghost predicate R(i: int, test: Test)
  reads test

method m3(test: Test)
{
  assume exists i :: R(i, test);
  assert exists i :: R(i, test);
  m1();
  assert exists i :: R(i, test); // error: assertion failure
}
