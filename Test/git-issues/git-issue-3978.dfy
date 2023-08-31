// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

method Main()
{
  for v := 3 to 18
  {
    if false {
      continue;
    }
    var x := 1;
    print x, "\n";
  }
}