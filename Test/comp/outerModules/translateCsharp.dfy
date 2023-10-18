// RUN: %baredafny translate cs %args %s --outer-module="my.happy" --output=%S/output/translated.cs
// RUN: %OutputCheck --file-to-check %S/output/translated.cs "%s"
// CHECK: namespace my\.happy\.SomeModule {
// CHECK: namespace my\.happy {

include "./source.dfy"