// RUN: %baredafny translate go  --go-module-name=GoModule1 "%s" --output "%S/test"
// RUN: %cp -rf "%S/go.mod" "%S/test-go/go.mod"
// RUN: %cp -rf "%S/go.sum" "%S/test-go/go.sum"
// RUN: %cp -rf "%S/../../../../../../../../../../DafnyRuntime/DafnyRuntimeGo-gomod" "%S"
// RUN: go run -C %S/test-go/ test.go > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule1 {

    method Main() {
        print "Hello World";
    }
}