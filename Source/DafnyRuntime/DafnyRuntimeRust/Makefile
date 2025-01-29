
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-rust/src/systemModulePopulator.rs
GENERATED_SYSTEM_MODULE_TARGET=src/system/mod.rs

all: check-system-module test

build-system-module:
	$(DAFNY) translate rs --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator
	python -c "import sys; data = sys.stdin.read(); sys.stdout.write(data.replace('::dafny_runtime', 'crate').replace('pub use ::std::rc::Rc;', '#[cfg(feature = \"sync\")] pub use ::std::sync::{Arc as Rc}; #[cfg(not(feature = \"sync\"))] pub use ::std::rc::Rc;'))" < $(GENERATED_SYSTEM_MODULE_SOURCE) > $(GENERATED_SYSTEM_MODULE_SOURCE).tmp && mv $(GENERATED_SYSTEM_MODULE_SOURCE).tmp $(GENERATED_SYSTEM_MODULE_SOURCE)

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

test:
	cargo test
	cargo test --features sync
	(cd ../../DafnyRuntime.Tests/DafnyRuntimeRustTest; cargo test)