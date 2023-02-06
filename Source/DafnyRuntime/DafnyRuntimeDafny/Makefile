
DAFNY = dotnet run --project ../../DafnyDriver --no-build --

SOURCE_DIR=.
SOURCES=$(shell find $(SOURCE_DIR) -name '*.dfy')

GENERATED_CODE_GO_SOURCE=src/dafnyRuntimeGo-go/src/dafny/dafny.go
GENERATED_CODE_GO_TARGET=../DafnyRuntimeGo/DafnyRuntimeFromDafny.go

verify:
	$(DAFNY) verify $(SOURCES)

build-go: verify
	$(DAFNY) translate go --no-verify --use-basename-for-filename src/dafnyRuntimeGo.dfy

check-go: build-go
	diff $(GENERATED_CODE_GO_SOURCE) $(GENERATED_CODE_GO_TARGET)

update-go: build-go
	cp $(GENERATED_CODE_GO_SOURCE) $(GENERATED_CODE_GO_TARGET)

test: check-go

# TODO: find a way to execute tests

