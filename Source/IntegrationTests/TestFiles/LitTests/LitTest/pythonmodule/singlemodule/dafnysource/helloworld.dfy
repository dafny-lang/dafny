// RUN: %baredafny translate py  --python-module-name=PythonModule1 "%s" --output "%S/PythonModule1"
// RUN: rm -rf "%S/PythonModule1"
// RUN: mv "%S/PythonModule1-py/" "%S/PythonModule1"
// RUN: pip3 install "%S"
// RUN: python3 %S/PythonModule1/ > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule1 {
    
    method Main() {
        print "Hello World";
    }
}