
DAFNYS=$(wildcard *.dfy)
CPPS=$(subst .dfy,.cpp,$(DAFNYS))
EXECS=$(subst .dfy,,$(DAFNYS))
DAFNY=../../Binaries/dafny
DAFNY_RUNTIME_DIR=../../Binaries
DAFNY_RUNTIME_CPP=$(DAFNY_RUNTIME_DIR)/DafnyRuntime.h
DAFNY_DEPS=$(DANFY) ../../Binaries/Dafny.exe ../../Binaries/DafnyPipeline.dll $(DAFNY_RUNTIME_CPP)


CXXFLAGS += -Wno-c++11-extensions -I$(DAFNY_RUNTIME_DIR)

.SECONDARY: $(CPPS)

all:$(EXECS)
#all:hello ints

vars:
	echo $(DAFNYS)
	echo $(CPPS)
	echo $(EXECS)

%.cpp: %.dfy $(DAFNY) $(DAFNY_DEPS)
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cpp $<

%.cs: %.dfy $(DAFNY) $(DAFNY_DEPS)
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cs $<

$(EXECS): % : %.cpp ../../Binaries/DafnyRuntime.h
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -f *.cpp $(EXECS)
