
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-go/System_/System_.go
GENERATED_SYSTEM_MODULE_TARGET=System_/System_.go

GENERATED_FROM_DAFNY_SOURCE=../obj/dafnyRuntime-gomod-go/src/dafny/dafny.go
GENERATED_FROM_DAFNY_TARGET=dafny/dafnyFromDafny.go

all: check-system-module check-from-dafny test

test:
	cd dafny &&	GO111MODULE=auto go test

build-system-module:
	$(DAFNY) translate go --go-module-name System --no-verify --allow-warnings --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

build-from-dafny:
	$(DAFNY) translate go --unicode-char:false --no-verify --use-basename-for-filename --bootstrapping ../DafnyRuntimeDafny/src/dafnyRuntimeGo.dfy --output:../obj/dafnyRuntime-gomod

check-from-dafny: build-from-dafny
	diff $(GENERATED_FROM_DAFNY_SOURCE) $(GENERATED_FROM_DAFNY_TARGET)

update-from-dafny: build-from-dafny
	cp $(GENERATED_FROM_DAFNY_SOURCE) $(GENERATED_FROM_DAFNY_TARGET)
