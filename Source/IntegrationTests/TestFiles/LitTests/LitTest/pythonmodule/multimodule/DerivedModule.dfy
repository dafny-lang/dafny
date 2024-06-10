// RUN: %baredafny translate py  --python-module-name=PythonModule2 --library="%S/PythonModule1.doo" --translation-record "%S/PythonModule1-py.dtr" --output "%S/PythonModule2" "%s"
// RUN: rm -rf "%S/PythonModule2"
// RUN: mv "%S/PythonModule2-py" "%S/PythonModule2"
// RUN: pip3 install "%S"
// RUN: python3 %S/PythonModule2/ > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule3 {
import DafnyModule1

method Main() {
        DafnyModule1.HelloWorld();
}
}