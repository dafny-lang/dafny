
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

SOURCE_DIR=.
SOURCES=$(shell find $(SOURCE_DIR) -name '*.dfy')

GENERATED_CODE_GO_SOURCE=src/dafnyRuntimeGo-go/src/dafny/dafny.go
GENERATED_CODE_GO_TARGET=../DafnyRuntimeGo/DafnyRuntimeFromDafny.go

verify:
	$(DAFNY) verify $(SOURCES)

build-go: verify
	$(DAFNY) translate go --unicode-char:false --no-verify --use-basename-for-filename --bootstrapping src/dafnyRuntimeGo.dfy

check-go: build-go
	diff $(GENERATED_CODE_GO_SOURCE) $(GENERATED_CODE_GO_TARGET)

update-go: build-go
	cp $(GENERATED_CODE_GO_SOURCE) $(GENERATED_CODE_GO_TARGET)

test: check-go

format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

# TODO: find a way to execute tests

