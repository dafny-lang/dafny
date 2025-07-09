
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --roll-forward LatestMajor --

NO_VERIFY := false # Use make update-binary NO_VERIFY=true to generate the binaries without verification
DOO_FILE_SOURCE=build/DafnyStandardLibraries.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries.doo

all: check-binary test check-format check-examples

verify:
	$(DAFNY) verify src/Std/dfyconfig.toml
	make -C src/Std/TargetSpecific verify-all

build-binary:
	$(DAFNY) build -t:lib --hidden-no-verify=$(NO_VERIFY) src/Std/dfyconfig.toml --output:${DOO_FILE_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/previous
	diff build/previous build/current
# Explicitly check for --hidden-no-verify since Dafny itself doesn't
	grep "hidden-no-verify = false" build/current/manifest.toml || \
		(echo "ERROR: doo file built with --hidden-no-verify, rebuild without this option" && exit 1)
	make -C src/Std/TargetSpecific check-binary-all

update-binary: build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}
	make -C src/Std/TargetSpecific update-binary-all
# Rebuild Dafny to pick up the new embedded assets
	dotnet build ../Dafny.sln

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.

test-cs:
	$(DAFNY) test $(VERIFY_OPTIONS) -t:cs examples/dfyconfig.toml examples/BoundedInts/NonDefault.cs --output:build/stdlibexamples --coverage-report:build/testcoverage
	$(DAFNY) test $(VERIFY_OPTIONS) -t:cs examples/nondeterministic/dfyconfig.toml --output:build/stdlibexamples_nondeterministic --coverage-report:build/nondeterministic_testcoverage
	TARGETLANG=cs make -C src/Std/TargetSpecific test

test-java:
	$(DAFNY) test $(VERIFY_OPTIONS) -t:java examples/dfyconfig.toml examples/BoundedInts/Externs/NonDefault.java --output:build/stdlibexamples
# Iterators aren't supported on Java so we can't test the nondeterministic examples
	TARGETLANG=java make -C src/Std/TargetSpecific test

test-go:
	$(DAFNY) test $(VERIFY_OPTIONS) -t:go examples/dfyconfig.toml examples/BoundedInts/NonDefault.go --output:build/stdlibexamples
	$(DAFNY) test $(VERIFY_OPTIONS) -t:go examples/nondeterministic/dfyconfig.toml --output:build/stdlibexamples_nondeterministic
	TARGETLANG=go make -C src/Std/TargetSpecific test

test-py:
	$(DAFNY) test $(VERIFY_OPTIONS) -t:py examples/dfyconfig.toml examples/BoundedInts/NonDefault.py --output:build/stdlibexamples
	$(DAFNY) test $(VERIFY_OPTIONS) -t:py examples/nondeterministic/dfyconfig.toml --output:build/stdlibexamples_nondeterministic
	TARGETLANG=py make -C src/Std/TargetSpecific test

test-js:
	$(DAFNY) test $(VERIFY_OPTIONS) -t:js examples/dfyconfig.toml examples/BoundedInts/NonDefault.js --output:build/stdlibexamples
	$(DAFNY) test $(VERIFY_OPTIONS) -t:js examples/nondeterministic/dfyconfig.toml --output:build/stdlibexamples_nondeterministic
	TARGETLANG=js make -C src/Std/TargetSpecific test

test: test-cs test-java test-go test-py test-js

# We only generate coverage from the C# tests
coverage: test-cs

format:
	$(DAFNY) format $(VERIFY_OPTIONS) .

check-format:
	$(DAFNY) format $(VERIFY_OPTIONS) . --check

check-examples:
	cd build && ../scripts/check-examples `find .. -name '*.md'`

clean:
	rm -rf build
