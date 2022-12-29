// RUN: %baredafny translate cs %args --library:"%S/Inputs/directLibrary.dfy" --library:"%S/Inputs/secondLibrary.dfy" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck "%s" --file-to-check="%S/consumer.cs"
// CHECK-NOT: namespace GloballyUniqueProducer
// CHECK-NOT: namespace AnotherGloballyUniqueProducer
// CHECK: GloballyUniqueProducer

include "Inputs/indirectLibrary.dfy"
include "Inputs/directLibrary.dfy"

module ConsumingModule {
  import A = GloballyUniqueProducer.ExportingModule
  import B = GloballyUniqueProducer.ExportingModule

  const myConstant := A.exportedVariable + B.exportedVariable
}
