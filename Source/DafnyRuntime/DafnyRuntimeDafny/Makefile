
# TODO: Use a project file to automate this better

# TODO: make work for all platforms
DAFNY = dafny

SOURCE_DIR := .
SOURCES := $(shell find $(SOURCE_DIR) -name '*.dfy')

verify:
	$(DAFNY) verify $(SOURCES)

go: verify
	$(DAFNY) translate go src/dafnyRuntimeGo.dfy --output ../generated
	diff ../generated-go/src/dafny/dafny.go ../DafnyRuntimeGo/DafnyRuntimeFromDafny.go

test:
	$(DAFNY) test test/dafnyRuntimeGoTest.dfy

