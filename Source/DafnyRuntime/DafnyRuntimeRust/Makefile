
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_DAFNY_MODULE_SOURCE=dfybuild
GENERATED_DAFNY_MODULE_TARGET=src

all: check-system-module test

test:
	./gradlew test

# translate rs currently fails because the Rust compiler is missing support for some features used in the standard library
build-system-module:
	$(DAFNY) translate rs --use-basename-for-filename --system-module:OmitAllOtherModules dfyconfig.toml --output:dfybuild
	rm ${GENERATED_DAFNY_MODULE_SOURCE}/generated.java

check-system-module: build-system-module
	diff -r $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)

update-system-module: build-system-module
	rm -rf $(GENERATED_DAFNY_MODULE_TARGET)
	cp -r $(GENERATED_DAFNY_MODULE_SOURCE) $(GENERATED_DAFNY_MODULE_TARGET)
