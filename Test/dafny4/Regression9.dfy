// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

// Some tests for the type inference that was revamped
// to better support subset types.

method Main()
{
  var f := F;
  var f' := F';
  var f'' := F'';
  var c := InitArray(F);
  var d := InitArray(F');
  var e := InitArray(F'');
  print c, d, e, "\n";
}

function F(x: int): char  // F has type int -> char
{ 'D' }

function F'(x: int): char
  requires true  // the presence of a requires clause makes F' have type int --> char
{ 'D' }

function F''(x: int): char
  reads {}  // the presence of a reads clause makes F' have type int ~> char
{ 'D' }

method InitArray<D>(f: int -> D) returns (a: D)
{
  return f(44);
}
