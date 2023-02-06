
# TODO: make work for all platforms
DAFNY = dafny

SOURCE_DIR := .
SOURCES := $(shell find $(SOURCE_DIR) -name '*.dfy')

GENERATED_CODE_GO_SOURCE := dafnyRuntimeGo-go/src/dafny/dafny.go
GENERATED_CODE_GO_TARGET := ../DafnyRuntimeGo/DafnyRuntimeFromDafny.go

verify:
	$(DAFNY) verify $(SOURCES)

build-go: verify
	$(DAFNY) translate go --no-verify src/dafnyRuntimeGo.dfy

check-go: build-go
	diff $(GENERATED_CODE_GO) $(GENERATED_CODE_GO_TARGET)

update-go: build-go
	cp $(GENERATED_CODE_GO) $(GENERATED_CODE_GO_TARGET)

test: check-go
# TODO: find a way to execute tests

