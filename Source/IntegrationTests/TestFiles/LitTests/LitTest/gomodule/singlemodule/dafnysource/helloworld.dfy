// RUN: %baredafny translate go  --module-name=GoModule1 "%s" --output "%S/test"
// RUN: cp -r "%S/go.*" "%S/test-go/"
// RUN: cp -r "%S/../../module-libraries/DafnyRuntimeGo" "%S"
// RUN: go run -C %S/test-go/ test.go > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule1 {

    method Main() {
        print "Hello World";
    }
}