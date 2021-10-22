// RUN: %dafny /compile:1 /compileTarget:cs "%s" %S/git-issue-1229-extern.cs > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "MyModule2"} MyModule2 {
    type {:extern "MyType"} MyType(==,!new)
}

module MyModule1 {
    import MyModule2

    datatype MyDatatype = MyDatatype (
        t: MyModule2.MyType
    )
}