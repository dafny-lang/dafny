// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

datatype d = D(m:seq<int>)

method Main()
{
  assert D([10, 20]) == D([10, 20]); // succeeds
  print [10, 20] == [10, 20], "\n"; // prints True
  print D([10, 20]) == D([10, 20]); // prints False
}
