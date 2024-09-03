// RUN: pip3 install "%S"
// RUN: %baredafny translate py --output "%S/SomeTestModule" --library="%S/SomeNestedModule.doo" --translation-record "%S/SomeNestedModule/SomeNestedModule-py.dtr" "%s" --include-runtime
// RUN: %S/python3 SomeTestModule-py/ > %t
// RUN: %diff "%s.expect" "%t"
module SomeTestModule {

    import Other = Some.Nested.Module

    method Main() {
        Other.HelloWorld();
    }
}