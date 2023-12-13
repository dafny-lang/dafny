
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-go/src
GENERATED_SYSTEM_MODULE_TARGET=output/

all: check-system-module test

test:
	cd dafny &&	GO111MODULE=auto go test

build-system-module:
	rm -r $(GENERATED_SYSTEM_MODULE_SOURCE)
	$(DAFNY) translate go --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules dfyconfig.toml --output:../obj/systemModulePopulator
	rm $(GENERATED_SYSTEM_MODULE_SOURCE)/systemModulePopulator.go

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp -r $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	cp -r input/ $(GENERATED_SYSTEM_MODULE_TARGET)
