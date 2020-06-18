// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:3 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:3 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method pr<T>(s: seq<T>) {
  print s, "\n";
}

method Main() {
  var a := new char[2];
  a[0] := 'h';
  a[1] := 'i';
  print a[..], "\n";
  print (a[..]), "\n";
  var b := new char[0];
  print b[..], "\n";
  print "", "\n";
  print "HI!", "\n";

  pr(a[..]);
  pr(b[..]);
  pr("HI!");
  pr("");

  var d:= new int[2];
  d[0] := 23;
  d[1] := 45;
  print d[..], "\n";
  pr(d[..]);
}


