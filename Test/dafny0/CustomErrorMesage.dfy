// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m(x:int)
{
  assert {:error "m: x must be positive"}  x > 0;
}

ghost function f(x:int):int {
  assert {:error "f: x must be positive"}  x > 0;
  x
}

ghost function f1():int {
  foo(-1)
}

ghost function foo(x:int) : (y:int)
  requires {:error "when calling foo, you must supply a positive x"} x > 0
  ensures  {:error "cannot establish that return value of foo is always negative"} y < 0
{
  x
}

method m2() {
  var y := bar(-1);
}

method bar(x:int) returns (y: int)
  requires {:error "when calling bar, you must supply a positive x"} x > 0
  ensures  {:error "cannot establish that return value of bar is always negative"} y < 0
{
  y := x;
}

method duplicate_array(input: array<int>, len: int) returns (output: array<int>)
  requires len == input.Length;
{
  output := new int[len];
  var i := 0;
  while i < len
    invariant {:error "position variable out of range"} 0 <= i <= len-1;
    invariant {:error "output array doesn't match input arry"} forall j :: 0 <= j < i ==> output[j] == input[j]+1;
  {
    output[i] := input[i];
    i := i + 1;
  }
}
