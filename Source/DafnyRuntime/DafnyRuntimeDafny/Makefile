
# TODO: Use a project file to automate this better

# TODO: make work for all platforms
DAFNY = dafny

SOURCE_DIR := .
SOURCES := $(shell find $(SOURCE_DIR) -name '*.dfy')

verify:
	$(DAFNY) verify $(SOURCES)

build-go: verify
	$(DAFNY) translate go src/dafnyRuntimeGo.dfy --output ../generated

check-go: build-go
	diff ../generated-go/src/dafny/dafny.go ../DafnyRuntimeGo/DafnyRuntimeFromDafny.go

update-go: build-go
	cp ../generated-go/src/dafny/dafny.go ../DafnyRuntimeGo/DafnyRuntimeFromDafny.go

test: verify
	$(DAFNY) test test/dafnyRuntimeGoTest.dfy

