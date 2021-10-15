
DAFNYS=$(wildcard *.dfy)
CPPS=$(subst .dfy,.cpp,$(DAFNYS))
DOT_H_S=$(subst .dfy,.h,$(DAFNYS))
EXECS=$(subst .dfy,,$(DAFNYS))
DAFNY_DIR=../..
DAFNY=$(DAFNY_DIR)/Binaries/dafny
DAFNY_RUNTIME_DIR=$(DAFNY_DIR)/Binaries
DAFNY_RUNTIME_CPP=$(DAFNY_RUNTIME_DIR)/DafnyRuntime.h
DAFNY_DEPS=$(DAFNY) $(DAFNY_RUNTIME_DIR)/Dafny.exe $(DAFNY_RUNTIME_DIR)/DafnyPipeline.dll $(DAFNY_RUNTIME_CPP)
TEST_LOG=tests.log

CXXFLAGS += -g -Wall -Wextra -Wpedantic -std=c++17 -I$(DAFNY_RUNTIME_DIR)

.SECONDARY: $(CPPS)

all:$(EXECS)

vars:
	echo $(DAFNYS)
	echo $(CPPS)
	echo $(EXECS)

%.cpp: %.dfy $(DAFNY) $(DAFNY_DEPS)
	$(DAFNY) /timeLimit:10 /compile:0 /spillTargetCode:3 /compileTarget:cpp ExternDefs.h $<

%.cs: %.dfy $(DAFNY) $(DAFNY_DEPS)
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /compileTarget:cs $<

$(EXECS): % : %.cpp $(DAFNY_RUNTIME_CPP)
	$(CXX) $(CXXFLAGS) -o $@ $<

test: $(EXECS)
	python run_cpp_tests.py $(EXECS)

clean:
	rm -f *.cpp *cs $(DOT_H_S) $(EXECS) $(TEST_LOG)
