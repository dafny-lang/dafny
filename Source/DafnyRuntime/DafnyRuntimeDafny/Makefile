
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --
VERIFY_OPTIONS = --type-system-refresh=true --general-traits=datatype --general-newtypes=true

SOURCE_DIR=.
SOURCES=$(shell find $(SOURCE_DIR) -name '*.dfy')

all: verify check-format

verify:
	$(DAFNY) verify $(VERIFY_OPTIONS) $(SOURCES)

format:
	$(DAFNY) format $(VERIFY_OPTIONS) .

check-format:
	$(DAFNY) format $(VERIFY_OPTIONS) . --check

# TODO: find a way to execute tests
