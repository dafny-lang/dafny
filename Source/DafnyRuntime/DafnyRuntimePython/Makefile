
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-py/
GENERATED_SYSTEM_MODULE_TARGET=output

all: check-system-module

build-system-module:
	rm -rf $(GENERATED_SYSTEM_MODULE_SOURCE)
	$(DAFNY) translate py --use-basename-for-filename --system-module:OmitAllOtherModules dfyconfig.toml --output:../obj/systemModulePopulator
	rm $(GENERATED_SYSTEM_MODULE_SOURCE)/__main__.py
	cp -r input/ $(GENERATED_SYSTEM_MODULE_TARGET)

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp -r $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
