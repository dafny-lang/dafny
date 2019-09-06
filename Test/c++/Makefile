
SRCS=$(wildcard *.cpp)
EXECS=$(subst .cpp,,$(SRCS))
DAFNY=../../Binaries/dafny

CXXFLAGS += -Wno-c++11-extensions

#all=$(TARGETS)
all:hello integers

%.cpp: %.dfy $(DAFNY)
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cpp $<

%.cs: %.dfy $(DAFNY)
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cs $<

$(EXECS): % : %.cpp ../../Binaries/DafnyRuntime.h
	$(CXX) -o $@ $<

clean:
	rm *.cpp $(EXECS)
