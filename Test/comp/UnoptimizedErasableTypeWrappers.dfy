// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --optimize-erasable-datatype-wrapper=false --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --optimize-erasable-datatype-wrapper=false --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --optimize-erasable-datatype-wrapper=false --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --optimize-erasable-datatype-wrapper=false --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --optimize-erasable-datatype-wrapper=false --target=py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype SingletonRecord = SingletonRecord(u: int)
datatype WithGhost = WithGhost(u: int, ghost v: int)

method Main() {
  var s := SingletonRecord(15);
  var w := WithGhost(20, 22);
  var t3a := (ghost 30, ghost 31, ghost 32);
  var t3b := (30, ghost 31, ghost 32);
  var t3c := (ghost 30, 31, ghost 32);
  var t3d := (30, ghost 31, 32);

  print s, " ", w, "\n"; // SingletonRecord(15) WithGhost(20)
  print t3a, " ", t3b, " ", t3c, " ", t3d, "\n"; // () (30) (31) (30, 32)

  print s.u, " ", w.u, "\n"; // 15 20
  print t3b.0, " ", t3c.1, " ", t3d.0, " ", t3d.2, "\n"; // 30 31 30 32
}
