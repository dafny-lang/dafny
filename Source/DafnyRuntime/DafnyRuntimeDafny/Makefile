
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --
VERIFY_OPTIONS = --type-system-refresh=true --general-traits=datatype --general-newtypes=true

SOURCE_DIR=.
SOURCES=$(shell find $(SOURCE_DIR) -name '*.dfy')

GENERATED_CODE_GO_SOURCE=src/dafnyRuntimeGo-go/src/dafny/dafny.go
GENERATED_CODE_GO_TARGET=../DafnyRuntimeGo/dafny/dafnyFromDafny.go

all: test check-format

verify:
	$(DAFNY) verify $(VERIFY_OPTIONS) $(SOURCES)

build-go: verify
	$(DAFNY) translate go --unicode-char:false --no-verify --use-basename-for-filename --bootstrapping src/dafnyRuntimeGo.dfy

check-go: build-go
	diff $(GENERATED_CODE_GO_SOURCE) $(GENERATED_CODE_GO_TARGET)

update-go: build-go
	cp $(GENERATED_CODE_GO_SOURCE) $(GENERATED_CODE_GO_TARGET)

test: check-go

format:
	$(DAFNY) format $(VERIFY_OPTIONS) .

check-format:
	$(DAFNY) format $(VERIFY_OPTIONS) . --check

# TODO: find a way to execute tests
