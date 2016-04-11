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