// RUN: %baredafny translate java %args %s --outer-package="my.happy" --output=%S/output/myjava
// RUN: %OutputCheck --file-to-check %S/output/myjava-java/myjava.java "%s"
// CHECK: import my.happy.SomeModule
// CHECK: my.happy._System

include "./source.dfy"