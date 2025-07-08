// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// This method can be used to test compilation.
method Main()
{
  var s := {2, 3};
  var m := map[2 := 20, 3 := 30];
  print (s, m), "\n";
  print (|s|, |m|), "\n";
  print set s | s in m, "\n";
  print forall x :: x in (map[1 := 10, 2 := 20]) ==> x > 0, "\n";
}
