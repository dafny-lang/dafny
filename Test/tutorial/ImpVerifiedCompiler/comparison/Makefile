default: all

VERIFY ?= ../../../../Scripts/dafny /compile:1

DEPS = \
	Sequences.dfy \
	IMP.dfy \
	Compil.dfy \

OBJS = $(DEPS:.dfy=.dll)

Sequences.dll: \
	Sequences.dfy

IMP.dll: \
	Sequences.dll \
	IMP.dfy

Compil.dll: \
	Sequences.dll \
	IMP.dll \
	Compil.dfy

%.dll: %.dfy
	$(VERIFY) $<

all: $(OBJS)

report:
	wc -l $(DEPS)
	grep 'axiom' *.dfy

clean:
	rm -f *.dll 
	rm -f *.runtimeconfig.json 
