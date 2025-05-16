DAFNY=../../../Scripts/dafny
DAFNY_OPTIONS=--type-system-refresh --general-traits=datatype --general-newtypes
OUTPUT=Output
GENERATED_PRELUDE=$(OUTPUT)/DafnyPrelude.bpl
TARGET_PRELUDE=../DafnyPrelude.bpl
CORE=$(OUTPUT)/PreludeCore.bpl

ifeq ($(shell uname),Darwin)  # MacOS
    SED_INPLACE = sed -i ""
else  # Linux and Windows
    SED_INPLACE = sed -i
endif

all: $(GENERATED_PRELUDE)

clean:
	rm -r $(OUTPUT)

$(GENERATED_PRELUDE): $(CORE) $(OUTPUT)/Sequences.bpl $(OUTPUT)/Math.bpl $(OUTPUT)/Sets.bpl $(OUTPUT)/Multisets.bpl
	# Extract Boogie from the model verified in Dafny
	./expand.sh $(CORE) $(GENERATED_PRELUDE)

$(OUTPUT)/Sequences.bpl $(OUTPUT)/Math.bpl $(OUTPUT)/Sets.bpl $(OUTPUT)/Multisets.bpl: $(OUTPUT) Lists.dfy Boxes.dfy Sequences.dfy Math.dfy Sets.dfy Multisets.dfy
	# Verify model files and extract Boogie declarations from them
	$(DAFNY) extract $(DAFNY_OPTIONS) Sequences $(OUTPUT)/Sequences.bpl Boxes.dfy Lists.dfy Sequences.dfy
	$(DAFNY) extract $(DAFNY_OPTIONS) Sets $(OUTPUT)/Sets.bpl Boxes.dfy Lists.dfy Sets.dfy
	$(DAFNY) extract $(DAFNY_OPTIONS) Math $(OUTPUT)/Math.bpl Math.dfy
	$(DAFNY) extract $(DAFNY_OPTIONS) Multisets $(OUTPUT)/Multisets.bpl Boxes.dfy Lists.dfy Math.dfy Sequences.dfy Sets.dfy Multisets.dfy
	# Remove trailing spaces that the Boogie pretty printer emits
	$(SED_INPLACE) -e "s| *$$||" $(OUTPUT)/Sequences.bpl $(OUTPUT)/Math.bpl $(OUTPUT)/Sets.bpl $(OUTPUT)/Multisets.bpl

$(CORE): $(OUTPUT) PreludeCore.bpl
	cp PreludeCore.bpl $(CORE)

$(OUTPUT):
	mkdir $(OUTPUT)

update: $(GENERATED_PRELUDE)
	cp $(GENERATED_PRELUDE) $(TARGET_PRELUDE)

check: $(GENERATED_PRELUDE)
	diff $(TARGET_PRELUDE) $(GENERATED_PRELUDE)
