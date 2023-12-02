// RUN: %dafny /compile:1 /compileTarget:cs "%s" %S/git-issue-1199-extern.cs > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "Microsoft"} Microsoft {
    module {:extern "Microsoft.Dafny"} Dafny {
        class {:extern "Main"} DafnyMain {}
    }
}

module M {
    import Microsoft

    method Foo() {
        var dafny: Microsoft.Dafny.DafnyMain? := null;
    }
}