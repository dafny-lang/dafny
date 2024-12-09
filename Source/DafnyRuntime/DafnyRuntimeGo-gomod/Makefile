
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-go/System_/System_.go
GENERATED_SYSTEM_MODULE_TARGET=System_/System_.go

all: check-system-module test

test:
	cd dafny &&	GO111MODULE=auto go test

build-system-module:
	$(DAFNY) translate go --go-module-name System --no-verify --allow-warnings --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
