// RUN: %testDafnyForEachCompiler "%s"

datatype Option<T> = None | Some(T)

method Main() {
  var x : Option<(nat, nat)> := Some((2,3));
  var Some((a,b)) := x;
  print a, " ", b, "\n";
}
