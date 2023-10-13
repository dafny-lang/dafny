
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=systemModulePopulator-java/_System
GENERATED_SYSTEM_MODULE_TARGET=src/main/java/_System

GENERATED_DAFNY_MODULE_SOURCE=systemModulePopulator-java/dafny
GENERATED_DAFNY_MODULE_TARGET=src/main/java/dafny

build-system-module:
	$(DAFNY) translate java --no-verify --use-basename-for-filename --include-system-module ../systemModulePopulator.dfy --output:systemModulePopulator
# Java compilation annoyingly merges the default module into the _System module
	rm $(GENERATED_SYSTEM_MODULE_SOURCE)/__default.java

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	diff $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	cp $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)
