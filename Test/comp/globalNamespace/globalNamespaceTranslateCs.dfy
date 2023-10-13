// RUN: %baredafny translate cs %args %s --outer-namespace="my.happy" --output=%S/output/translated.cs
// RUN: %OutputCheck --file-to-check %S/output/translated.cs "%s"
// CHECK: namespace my.happy.SomeModule {
// CHECK: namespace my.happy._module {

include "./source.dfy"