// RUN: %baredafny translate py %args %s --outer-module="my.happy" --output=%S/output/
// RUN: %OutputCheck --file-to-check %S/output/-py/my/happy.py "%s"
// CHECK: import my.happy.SomeModule

include "./source.dfy"