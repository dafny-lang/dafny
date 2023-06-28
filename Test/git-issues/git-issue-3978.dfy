// RUN: %testDafnyForEachCompiler "%s"

method Main() returns ()
{
 for v_int_7 := 3 to 18
 {
  if (false) {
    continue;
  }
  var v_int_93 := 1;
  print v_int_93, "\n";
 }
}