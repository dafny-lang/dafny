// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var A := map[0 := 1];
  var B := map x | x in (set y | y in A) :: A[x];
  print A, "\n";
  print B, "\n";
}


