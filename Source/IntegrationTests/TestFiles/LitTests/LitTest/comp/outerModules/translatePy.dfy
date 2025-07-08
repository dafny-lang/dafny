// RUN: %baredafny translate py %args %s --outer-module="my.happy" --output=%S/output/
// RUN: %OutputCheck --file-to-check %S/output/-py/my_happy.py "%s"
// We could update PythonCompiler to it puts every module in a separate folder: %OutputCheck --file-to-check %S/output/-py/my/happy.py "%s"
// CHECK: import my_happy_SomeModule

include "./source.dfy"