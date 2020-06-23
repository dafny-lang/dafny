// RUN: %dafny /compileVerbose:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Level1 = Level1(u:int)
datatype Level2 = Level2(u:int, l:Level1)

method TestNestedLet() {
  var x := Level2(5, Level1(3));

  var Level2(u, Level1(v)) := x;
}

