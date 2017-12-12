// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate p(i:int)

method m1()

method m2()
{
  assume exists i :: p(i);
  assert exists i :: p(i);
  m1();
  assert exists i :: p(i); // FAILS
}

class Test
{
    var arr : array<int>;
    predicate p(i: int)
    method foo()
        requires arr.Length > 0
        modifies arr
    {
        assume exists i :: p(i);
        arr[0] := 1;
        assert exists i :: p(i);  // FAILS
    }
}
