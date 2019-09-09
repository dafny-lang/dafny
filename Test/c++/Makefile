
DAFNYS=$(wildcard *.dfy)
CPPS=$(subst .dfy,.cpp,$(DAFNYS))
EXECS=$(subst .dfy,,$(DAFNYS))
DAFNY=../../Binaries/dafny

CXXFLAGS += -Wno-c++11-extensions

.SECONDARY: $(CPPS)

all:$(EXECS)
#all:hello ints

vars:
	echo $(DAFNYS)
	echo $(CPPS)
	echo $(EXECS)

%.cpp: %.dfy $(DAFNY)
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cpp $<

%.cs: %.dfy $(DAFNY)
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cs $<

$(EXECS): % : %.cpp ../../Binaries/DafnyRuntime.h
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -f *.cpp $(EXECS)
