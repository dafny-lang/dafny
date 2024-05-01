// RUN: %baredafny translate go  --module-name=GoModule2 --library="%S/test.doo" --translation-record "%S/test-go.dtr" --output "%S/test3" "%s"
// RUN: cp -r "%S/go.*" "%S/test3-go/"
// RUN: cp -r "%S/../module-libraries/DafnyRuntimeGo" "%S"
// RUN: cp -r "%S/DafnyModule1" "%S/test3-go/"
// RUN: go run -C %S/test3-go/ test3.go > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule3 {
import DafnyModule1

method Main() {
        DafnyModule1.HelloWorld();
}
}