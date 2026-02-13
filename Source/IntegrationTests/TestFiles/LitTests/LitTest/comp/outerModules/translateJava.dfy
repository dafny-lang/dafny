// RUN: %baredafny translate java %args %s --outer-module="my.happy" --output=%S/output/myjava
// RUN: %OutputCheck --file-to-check %S/output/myjava-java/myjava.java "%s"
// CHECK: my\.happy

include "./source.dfy"