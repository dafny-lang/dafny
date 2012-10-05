TESTS_FILE = alltests.txt
LONG = $(shell awk '{ if (tolower($$2) ~ /^long$$/) print $$1 }' $(TESTS_FILE))
NORMAL = $(shell awk '{ if (tolower($$2) ~ /^use$$/) print $$1 }' $(TESTS_FILE))
TESTS = $(NORMAL)

all: dafny

dafny: $(addprefix rundfy-, $(TESTS))

rundfy-%:
	@cmd /c "runtest.bat $* $(FLAGS)" || :

long:
	$(MAKE) TESTS="$(NORMAL) $(LONG)" all

show:
	@echo $(TESTS)
