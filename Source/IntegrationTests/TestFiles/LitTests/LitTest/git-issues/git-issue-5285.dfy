// RUN: %testDafnyForEachCompiler "%s"

const someSet :=
  set 
    someString <- {"D"},
    someChar <- 
      set c <- someString :: c
  :: someChar

const someMap := 
  map x | 
       0 < x < 3
    && x in 
      map y : int | 0 <= y <= x :: y
  :: x * x

method Main() {
  print someSet, "\n";
  // Avoid non-determinism in map printing
  print someMap - {2}, "\n";
  print someMap - {1}, "\n";
}