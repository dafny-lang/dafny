// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Success(value: T) | Failure(error: string)
{
  predicate IsFailure() {
    Failure?
  }
  function PropagateFailure<U>(): Result<U>
    requires Failure?
  {
    Failure(this.error)
  }
  function Extract(): T
    requires Success?
  {
    value
  }
}

method mn() returns (r: Result<int>, out: int)
  ensures r.Failure? && out == -2;
{
  var t, k :- m(1);
  assert t == 1 && k == 2;
  var rr;
  rr, out :- m(-1); // Should exit with failure
  return Success(k), out;
}

method mn1() returns (r: Result<int>, out: int)
  ensures r.Failure? && out == 42
{
  out := 42;
  var k :- m1(1);
  assert k == 1;
  out :- m1(-1); // Should exit with failure
  return Success(k), out;
}


method m(i: int) returns (r: Result<int>, o: int)
  ensures 0 <= i ==> r.Success? && r.Extract() == i && o == i+i;
  ensures i < 0 ==> r.Failure? && o == i+i;
{
  if i < 0 { return Failure("negative"), i+i; }
  return Success(i), i+i;
}

method m1(i: int) returns (r: Result<int>)
  ensures 0 <= i ==> r.Success? && r.Extract() == i;
  ensures i < 0 ==> r.Failure?;
{
  if i < 0 { return Failure("negative"); }
  return Success(i);
}

method Main() {
  var x, out := mn();
  print x.Failure?, " ", out, "\n";
  x, out := mn1();
  print x.Failure?, " ", out, "\n";
  print "End\n";
}

