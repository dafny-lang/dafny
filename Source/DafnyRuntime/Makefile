
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=obj/systemModulePopulator.cs
GENERATED_SYSTEM_MODULE_TARGET=DafnyRuntimeSystemModule.cs

GENERATED_SYSTEM_MODULE_SOURCE_RS=obj/systemModulePopulator-rust/src/systemModulePopulator.rs
GENERATED_SYSTEM_MODULE_TARGET_RS=DafnyRuntimeRust/src/system/mod.rs

all: check-system-module

build-system-module:
	$(DAFNY) translate cs --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false --system-module:OmitAllOtherModules systemModulePopulator.dfy --output:obj/systemModulePopulator

build-system-module-rs:
	$(DAFNY) translate rs --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false --system-module:OmitAllOtherModules systemModulePopulator.dfy --output:obj/systemModulePopulator
	python -c "import sys; data = sys.stdin.read(); sys.stdout.write(data.replace('::dafny_runtime', 'crate'))" < $(GENERATED_SYSTEM_MODULE_SOURCE_RS) > $(GENERATED_SYSTEM_MODULE_SOURCE_RS).tmp && mv $(GENERATED_SYSTEM_MODULE_SOURCE_RS).tmp $(GENERATED_SYSTEM_MODULE_SOURCE_RS)

check-system-module: build-system-module build-system-module-rs
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	diff $(GENERATED_SYSTEM_MODULE_SOURCE_RS) $(GENERATED_SYSTEM_MODULE_TARGET_RS)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module-rs: build-system-module-rs
	cp $(GENERATED_SYSTEM_MODULE_SOURCE_RS) $(GENERATED_SYSTEM_MODULE_TARGET_RS)
