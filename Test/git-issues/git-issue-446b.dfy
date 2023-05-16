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
}

method mn() returns (r: Result<int>, out: int)
  ensures out == -2 && r.Failure?
{
  var o :- m(1);
  assert o == 3;
  print "OK\n";
  out :- m(-1); // Should exit with failure
  return Success(0), 4;
}

method mn1() returns (r: Result<int>)
  ensures r.Failure?
{
  :- m1(1);
  print "OK\n";
  :- m1(-1); // SHould exit with failure
  return Success(0);
}


method m(i: int) returns (r: Result<int>, o: int)
  ensures 0 <= i ==> r.Success? && r.value == i && o == i+i+i;
  ensures i < 0 ==> r.Failure? && o == i+i;
{
  if i < 0 { return Failure("negative"), i+i; }
  return Success(i), i+i+i;
}

method m1(i: int) returns (r: Result<int>)
  ensures 0 <= i ==> r.Success? && r.value == i;
  ensures i < 0 ==> r.Failure?;
{
  if i < 0 { return Failure("negative"); }
  return Success(i);
}

method mexp() returns (r: Result<int>, k: int)
  ensures r.IsFailure() && k == 100;
{
  k :- Result<int>.Failure("always"), 100;
  k := 101; // Not executed
  return Success(0), k;
}

method mstar() returns (r: Result<int>, k: int)
  ensures r.IsFailure();
{
  k :- Result<int>.Failure("always"), *;
  k := 101; // Not executed
  return Success(0), k;
}


method Main() {
  var x := mn1();
  print x.Failure?, " ";
  var out;
  x, out := mn();
  print x.Failure?, " ", out, "\n";
  x, out := mexp();
  print x.Failure?, " ", out, "\n";
  print "End\n";
}

