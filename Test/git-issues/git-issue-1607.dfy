// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

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