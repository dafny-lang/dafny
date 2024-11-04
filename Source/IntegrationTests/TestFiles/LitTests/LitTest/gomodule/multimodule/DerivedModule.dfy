// RUN: %baredafny translate go  --go-module-name=GoModule2 --library="%S/test.doo" --translation-record "%S/test-go.dtr" --output "%S/test3" "%s"
// RUN: %cp -rf "%S/go.mod" "%S/test3-go/go.mod"
// RUN: %cp -rf "%S/go.sum" "%S/test3-go/go.sum"
// RUN: %cp -rf "%S/../../../../../../../../../DafnyRuntime/DafnyRuntimeGo-gomod" "%S"
// RUN: %cp -rf "%S/DafnyModule1" "%S/test3-go/"
// RUN: go run -C %S/test3-go/ test3.go > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule3 {
import DafnyModule1

method Main() {
        DafnyModule1.HelloWorld();
}
}