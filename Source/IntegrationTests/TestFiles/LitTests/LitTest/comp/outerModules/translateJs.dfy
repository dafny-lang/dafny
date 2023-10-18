// RUN: %baredafny translate js %args %s --outer-module="my.happy" --output=%S/output/js
// RUN: %OutputCheck --file-to-check %S/output/js.js "%s"
// CHECK: let my_happy_SomeModule
// CHECK: my_happy =

include "./source.dfy"