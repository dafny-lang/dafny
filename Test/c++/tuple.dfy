// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp /unicodeChar:0 ExternDefs.h "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000

method ReturnTuple() returns (x:(uint32,uint32))
{
  return (1, 2);
}

function EmptyTuple() : () {
  ()
}

function GetEmptyTuple() : () {
  EmptyTuple()
}

function Test() : (bool, bool) {
  (false, true)
}

method BoolCallee(a:bool) returns (a0:bool, a1:bool)
{
  return a, a;
}

method BoolCaller(a:bool)
{
  var a0, a1 := BoolCallee(a);
}

method GenericCallee<A>(a:A) returns (a0:A, a1:A)
{
  return a, a;
}

method GenericCaller<A>(a:A)
{
  var a0, a1 := GenericCallee(a);
}

method Main() {
  var x := ReturnTuple();
  var y := x.0;
  print y, "\n";
}
