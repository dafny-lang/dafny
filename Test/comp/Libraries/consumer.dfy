// RUN: %dafny /library:"%S/directLibrary.dfy" /library:"%S/secondLibrary.dfy" /compile:0 /spillTargetCode:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck "%s" --file-to-check="%S/consumer.cs"
// CHECK-NOT: namespace GloballyUniqueProducer
// CHECK-NOT: namespace AnotherGloballyUniqueProducer
// CHECK: GloballyUniqueProducer

include "indirectLibrary.dfy"
include "directLibrary.dfy"

module ConsumingModule {
  import A = GloballyUniqueProducer.ExportingModule
  import B = GloballyUniqueProducer.ExportingModule

  const myConstant := A.exportedVariable + A.exportedVariable
}