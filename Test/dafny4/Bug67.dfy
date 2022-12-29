// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype d = D(m:seq<int>)

method Main()
{
  assert D([10, 20]) == D([10, 20]); // succeeds
  print [10, 20] == [10, 20], "\n"; // prints True
  print D([10, 20]) == D([10, 20]); // prints False
}
