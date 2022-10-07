default: all

VERIFY ?= ../../../Scripts/dafny /compile:1

DEPS = \
	SyntaxCommon.dfy \
	Imp.dfy \
	Mach.dfy \
	Semantics.dfy \
	SemanticsProperties.dfy \
	ImpNaturalSem.dfy \
	MachSemantics.dfy \
	Compiler.dfy \
	SimulationRelation.dfy \
	CompileAexpCorrect.dfy \
	CompileBexpCorrect.dfy \
	CompileComCorrect.dfy \
	CompileProgramCorrect.dfy \
	ImpReductionSem.dfy \
	ImpReductionContSem.dfy \
	SimulationRelationCont.dfy \
	Proof.dfy \
	Proof2.dfy

OBJS = $(DEPS:.dfy=.dll)

SyntaxCommon.dll: \
	SyntaxCommon.dfy
Imp.dll: \
	SyntaxCommon.dll \
	Imp.dfy
Mach.dll: \
	SyntaxCommon.dll \
	Mach.dfy
Semantics.dll: \
	Semantics.dfy
SemanticsProperties.dll: \
	Semantics.dll \
	SemanticsProperties.dfy
ImpNaturalSem.dll: \
	Imp.dll \
	SemanticsCommon.dll \
	ImpNaturalSem.dfy
MachSemantics.dll: \
	Imp.dll \
	SemanticsCommon.dll \
	Semantics.dll \
	MachSemantics.dfy
Compiler.dll: \
	Imp.dll \
	Mach.dll \
	Compiler.dfy
SimulationRelation.dll: \
	Mach.dll \
	SimulationRelation.dfy
CompileAexpCorrect.dll: \
	Imp.dll \
	Mach.dll \
	ImpNaturalSem.dll \
	MachSemantics.dll \
	SemanticsProperties.dll \
	Compiler.dll \
	SimulationRelation.dll \
	CompileAexpCorrect.dfy
CompileBexpCorrect.dll: \
	Imp.dll \
	Mach.dll \
	ImpNaturalSem.dll \
	MachSemantics.dll \
	SemanticsProperties.dll \
	Compiler.dll \
	SimulationRelation.dll \
	CompileAexpCorrect.dll \
	CompileBexpCorrect.dfy
CompileComCorrect.dll: \
	Imp.dll \
	Mach.dll \
	ImpNaturalSem.dll \
	MachSemantics.dll \
	SemanticsProperties.dll \
	Compiler.dll \
	SimulationRelation.dll \
	CompileAexpCorrect.dll \
	CompileBexpCorrect.dll \
	CompileComCorrect.dfy
CompileProgramCorrect.dll: \
	Imp.dll \
	Mach.dll \
	ImpNaturalSem.dll \
	MachSemantics.dll \
	SemanticsProperties.dll \
	Compiler.dll \
	SimulationRelation.dll \
	CompileComCorrect.dll \
	CompileProgramCorrect.dfy
ImpReductionSem.dll: \
	Imp.dll \
	SemanticsCommon.dll \
	ImpNaturalSem.dll \
	ImpReductionSem.dfy
ImpReductionContSem.dll: \
	Imp.dll \
	SemanticsCommon.dll \
	ImpNaturalSem.dll \
	ImpReductionContSem.dfy
SimulationRelationCont.dll: \
	SimulationRelation.dll \
	ImpReductionContSem.dll \
	SimulationRelationCont.dfy
Proof.dll: \
	SimulationRelationCont.dll \
	ImpReductionContSem.dll \
	MachSemantics.dll \
	SemanticsProperties.dll \
	CompileAexpCorrect.dll \
	CompileBexpCorrect.dll \
	Proof.dfy
Proof2.dll: \
	Proof.dll \
	Proof2.dfy

%.dll: %.dfy
	$(VERIFY) $<

all: $(OBJS)

clean:
	rm -f *.dll 
	rm -f *.runtimeconfig.json 
