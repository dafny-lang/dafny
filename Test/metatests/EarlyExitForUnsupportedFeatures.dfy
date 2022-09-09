// RUN: %testDafnyForEachCompiler "%s"
// RUN: %dafny_0 -noVerify -compileTarget:cpp -compile:4 "%s" > "%t"
// RUN: %diff "%s.oldway.expect" "%t"

// Newtypes can only compiled to bounded integers in C++, and that causes an immediate exit
newtype positive = i: int | i > 0 witness 1

// This is not supported in C++ either, but it will not cause an error to be printed
predicate method Even(i: int) { i % 2 == 0 }

method Main() {
  print Even(4), "\n";
}
