// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  var a: bv8 := 0xFF;
  var b: bv16 := 0xFFFF;
  var c: bv32 := 0xFFFF_FFFF;
  var d: bv64 := 0xFFFF_FFFF_FFFF_FFFF;
  var e: bv128 := 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF;
  print a as real, " ", b as real, " ", c as real, " ", d as real , " ", e as real, "\n";
  print a as nat, " ", b as nat, " ", c as nat, " ", d as nat, " ", e as nat, "\n";
  print a as ORDINAL, " ", b as ORDINAL, " ", c as ORDINAL, " ", d as ORDINAL, " ", e as ORDINAL, "\n";
}
