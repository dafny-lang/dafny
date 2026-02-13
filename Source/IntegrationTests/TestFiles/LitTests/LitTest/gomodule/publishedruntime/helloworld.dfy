// This test consciously depends on the published version of the Go runtime
// at https://github.com/dafny-lang/DafnyRuntimeGo/v4,
// to ensure that copy works correctly.
// The other tests use `replace` directives to test against the local copy.
// That means if this test fails at some point because Dafny changes
// its compilation output, it may be necessary to
// publish a new tag on dafny-lang/DafnyRuntimeGo first before
// this test can pass, much less a new version of Dafny released.

// RUN: %baredafny translate go  --go-module-name=GoModule1 "%s" --output "%S/test"
// RUN: %cp -rf "%S/go.mod" "%S/test-go/go.mod"
// RUN: %cp -rf "%S/go.sum" "%S/test-go/go.sum"
// RUN: go run -C %S/test-go/ test.go > %t
// RUN: %diff "%s.expect" "%t"
module DafnyModule1 {

    method Main() {
        print "Hello World";
    }
}