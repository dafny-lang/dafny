// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype SingletonRecord = SingletonRecord(u: int)
datatype GhostOrNot = ghost Ghost(a: int, b: int) | Compiled(x: int)
//datatype GenericGhostOrNot<X> = ghost Ghost(a: int, b: int) | GenericCompiled(x: X)

method Main() {
  TestTargetTypesAndConstructors();
  TestSelect();
//  Tuples();
//  M();
}

method TestTargetTypesAndConstructors() {
  var r := SingletonRecord(62); // type of r should turn into int
  var g := Compiled(63); // type of g should turn into int
  var rst := (2, 5);
  var xyz := (2, ghost 3, 5); // type of xyz should turn into Tuple2
  var abc := (ghost 2, 3, ghost 5); // type of abc should turn into int

  print r, " ", g, " ", rst, " ", xyz, " ", abc, "\n"; // 62 63 (2, 5) (2, 5) 3
}

method TestSelect() {
  var r := SingletonRecord(62); // type of r should turn into int
  var g := Compiled(63); // type of g should turn into int
  var rst := (2, 5);
  var xyz := (2, ghost 3, 5); // type of xyz should turn into Tuple2
  var abc := (ghost 2, 3, ghost 5); // type of abc should turn into int

  print r.u, " "; // 62
  print g.x, " "; // 63
  print rst.1, " "; // 5
  print xyz.2, " "; // 5
  print abc.1, "\n"; // 3
}
