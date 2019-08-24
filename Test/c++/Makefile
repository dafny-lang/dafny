
SRCS=$(wildcard *.cpp)
EXECS=$(subst .cpp,,$(SRCS))
DAFNY=../../Binaries/dafny

#all=$(TARGETS)
all:hello integers

%.cpp: %.dfy $(DAFNY)
	$(DAFNY) /compile:0 /spillTargetCode:3 /compileTarget:cpp $<

$(EXECS): % : %.cpp ../../Binaries/DafnyRuntime.h
	$(CXX) -o $@ $<

clean:
	rm *.cpp $(EXECS)
