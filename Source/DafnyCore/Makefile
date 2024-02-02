# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
GENERATED_FROM_DAFNY=GeneratedFromDafny
REGENERATED_FROM_DAFNY=GeneratedFromDafnyRegenerated

all: Parser.cs

Parser.cs: Coco/Scanner.frame Coco/Parser.frame Dafny.atg
	dotnet tool run coco Dafny.atg -namespace Microsoft.Dafny -frames Coco

clean:
	rm -f Scanner.cs Scanner.cs.old Parser.cs Parser.cs.old

build-regenerated-from-dafny:
	chmod u+x DafnyGeneratedFromDafny.sh
	./DafnyGeneratedFromDafny.sh $(REGENERATED_FROM_DAFNY)

test: build-regenerated-from-dafny
	(diff $(GENERATED_FROM_DAFNY).cs $(REGENERATED_FROM_DAFNY).cs && (echo 'Consider running ./DafnyGeneratedFromDafny.sh GeneratedFromDafny'))

check-format:
	../../Scripts/dafny format . --check
