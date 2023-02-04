
# TODO: Use a project file to automate this better

# TODO: make work for all platforms
DAFNY = dafny

verify:
	$(DAFNY) verify src/dafnyRuntime.dfy

go: verify
	$(DAFNY) translate go src/dafnyRuntimeGo.dfy --output ../generated
	diff ../generated-go/src/dafny/dafny.go ../DafnyRuntimeGo/DafnyRuntimeFromDafny.go

test:
	$(DAFNY) test test/dafnyRuntimeGoTest.dfy

