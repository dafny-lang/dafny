// NONUNIFORM: %testDafnyForEachCompiler doesn't support main arguments :(
// RUN: %run -t:py "%s" Hello > %t
// RUN: %diff "%s.expect" "%t"

method Main(args: seq<string>) 
{
  expect 1 < |args|;
  print Foo(args[1], "World"), "\n";
}

datatype Foo = Foo(t: string, x: string)
