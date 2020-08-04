// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

trait Trait<Y> {
  const y: Y
  const k: Y := y
  const l: Y 
}

class ClassB extends Trait<array<bv8>> { 
  var m: array<bv8>
  constructor () { m := new bv8[10]; }
}


method Main() {
  var cb := new ClassB();
  print cb.y.Length, " ", cb.k.Length, " ", cb.l.Length, " ", cb.m.Length, "\n";
}

