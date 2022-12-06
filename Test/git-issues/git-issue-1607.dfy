// RUN: %testDafnyForEachCompiler "%s"

module M {
  datatype D = D_1(a: bool) | D_2(b: bool)

  method DoIt (d: D)
  {
    if (d.D_1?) {
      print "1 ", d.a;
    }
    else {
      print "2 ", d.b;
    }
  }
}

method Main(){
  var x : M.D := M.D_2(true);
  M.DoIt(x);
  print "\n";
}
