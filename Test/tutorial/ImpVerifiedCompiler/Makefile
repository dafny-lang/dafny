default: all

VERIFY ?= ../../../Scripts/dafny /compile:0

DEPS = $(wildcard *.dfy)
OBJS = $(DEPS:.dfy=.dll)

%.dll: %.dfy
	$(VERIFY) $<

all: $(OBJS)

clean:
	rm $(OBJS)
