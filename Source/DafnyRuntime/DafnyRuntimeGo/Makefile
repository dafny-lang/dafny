
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=build
GENERATED_SYSTEM_MODULE_TARGET=output

all: check-system-module test

test:
	cd dafny &&	GO111MODULE=auto go test

build-system-module:
	rm -r -f build
	make -C ../DafnyRuntimeDafny update-go
	$(DAFNY) translate go --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules dfyconfig.toml --output:build/generated
	mv build/generated-go/src/* build/
	rm build/generated.go
	rm -r build/generated-go
	cp -r input/ build/

check-system-module: build-system-module
	diff -r $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	rm -r $(GENERATED_SYSTEM_MODULE_TARGET)
	cp -r $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
