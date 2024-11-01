// RUN: %exits-with 0 %verify "%s"

method Main(args: seq<string>) 
{
  expect 1 < |args|;
  print Foo(args[1], "World"), "\n";
}

datatype Foo = Foo(t: string, x: string)
