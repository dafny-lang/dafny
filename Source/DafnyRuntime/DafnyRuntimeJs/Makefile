
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator.js
GENERATED_SYSTEM_MODULE_TARGET=DafnyRuntimeSystemModule.js

all: check-system-module

build-system-module:
	rm -rf output
	$(DAFNY) translate js --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules dfyconfig.toml --output:build/runtime
	cp -r input/ build

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp -r build output
