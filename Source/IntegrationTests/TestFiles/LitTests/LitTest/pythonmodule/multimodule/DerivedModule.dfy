// RUN: %baredafny translate py  --python-module-name=PythonModule2 --library="%S/PythonModule1.doo" --translation-record "%S/PythonModule1-py.dtr" --output "%S/PythonModule2" "%s" --include-runtime
// RUN: %exits-with -any %rm -rf "%S/PythonModule2"
// RUN: %mv "%S/PythonModule2-py" "%S/PythonModule2"
// RUN: pip3 install "%S"
// RUN: %S/python3 PythonModule2/ > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule3 {
import DafnyModule1

method Main() {
        DafnyModule1.HelloWorld();
}
}