// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  var a := new bv8[3];
  print a[1], " ";
  a[0] := 7;
  print a[..], "\n";
  var b := new bv16[2];
  b[0] := 7;
  print b[0], " ", b[1], "\n";
  var c := new bv32[2];
  c[0] := 7;
  print c[0], " ", c[1], "\n";
  var d := new bv64[2];
  d[0] := 7;
  print d[0], " ", d[1], "\n";
  var e := new bv65[2];
  e[0] := 7;
  print e[0], " ", e[1], "\n";
  var f := new (bv8, bv16)[1];
  print f[0].0, " ", f[0].1, "\n";
}
