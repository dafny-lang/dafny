// RUN: %run "%s" --input "%S/AbstractExtern1.cs" --test-assumptions Externs
// RUN: %exits-with 3 %run "%s" --input "%S/AbstractExtern2.cs" --test-assumptions Externs
abstract module A {
    method {:extern "ExternMethod"} Method() returns (r: int)
      ensures r > 0
}

module M refines A {
}

method Main() {
  var x := M.Method();
  print x, "\n";
}
