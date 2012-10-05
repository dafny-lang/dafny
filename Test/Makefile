TESTS_FILE = alltests.txt
LONG = $(shell awk '{ if (tolower($$2) ~ /^long$$/) print $$1 }' $(TESTS_FILE))
NORMAL = $(shell awk '{ if (tolower($$2) ~ /^use$$/) print $$1 }' $(TESTS_FILE))
TESTS = $(NORMAL)

all: dafny

dafny: $(addprefix rundfy-, $(TESTS))

show:
	@echo $(TESTS)

long:
	$(MAKE) TESTS="$(NORMAL) $(LONG)" all

rundfy-%:
	@if ls -f $*/*.dfy >/dev/null 2>&1 ; then cmd /c "runtest.bat $* $(FLAGS)" ; fi || :
