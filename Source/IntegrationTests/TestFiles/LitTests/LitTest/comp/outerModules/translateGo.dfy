// RUN: %baredafny translate go %args %s --outer-module="my.happy" --output=%S/output/
// RUN: %OutputCheck --file-to-check %S/output/-go/src/.go "%s"
// CHECK: my_happy_SomeModule "my_happy_SomeModule"

include "./source.dfy"