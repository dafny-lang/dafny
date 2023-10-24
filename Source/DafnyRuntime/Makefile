
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=obj/systemModulePopulator.cs
GENERATED_SYSTEM_MODULE_TARGET=DafnyRuntimeSystemModule.cs

build-system-module:
	$(DAFNY) translate cs --no-verify --use-basename-for-filename --system-module:Populate systemModulePopulator.dfy --output:obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	