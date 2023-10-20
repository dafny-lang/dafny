
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=systemModulePopulator-java/_System
GENERATED_SYSTEM_MODULE_TARGET=src/main/dafny-generated/_System

GENERATED_DAFNY_MODULE_SOURCE=systemModulePopulator-java/dafny
GENERATED_DAFNY_MODULE_TARGET=src/main/dafny-generated/dafny

all: check-system-module test

test:
	./gradlew test

build-system-module:
	$(DAFNY) translate java --no-verify --use-basename-for-filename --include-system-module ../systemModulePopulator.dfy --output:systemModulePopulator
# _System.__default is the default module folded into _System so ignore it
	rm systemModulePopulator-java/_System/__default.java

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	diff $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)

update-system-module: build-system-module
	rm -rf $(GENERATED_SYSTEM_MODULE_TARGET)
	cp -r $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	rm -rf $(GENERATED_DAFNY_MODULE_TARGET)
	cp -r $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)
