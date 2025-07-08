
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-java/_System
GENERATED_SYSTEM_MODULE_TARGET=src/main/dafny-generated/_System

GENERATED_DAFNY_MODULE_SOURCE=../obj/systemModulePopulator-java/dafny
GENERATED_DAFNY_MODULE_TARGET=src/main/dafny-generated/dafny

all: check-system-module test

test:
	./gradlew test

# TODO: Add --optimize-erasable-datatype-wrapper:false elsewhere too
build-system-module:
	$(DAFNY) translate java --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	diff $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)

update-system-module: build-system-module
	rm -rf $(GENERATED_SYSTEM_MODULE_TARGET)
	cp -r $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	rm -rf $(GENERATED_DAFNY_MODULE_TARGET)
	cp -r $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)
