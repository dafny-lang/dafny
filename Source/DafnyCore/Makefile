# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
GENERATED_FROM_DAFNY=GeneratedFromDafny
REGENERATED_FROM_DAFNY=GeneratedFromDafnyRegenerated
DAFNY = dotnet run --project ../Dafny --no-build --roll-forward LatestMajor --

all: Parser.cs

Parser.cs: Coco/Scanner.frame Coco/Parser.frame Coco/Copyright.frame Dafny.atg
	dotnet tool run coco Dafny.atg -namespace Microsoft.Dafny -frames Coco

clean:
	rm -f Scanner.cs Scanner.cs.old Parser.cs Parser.cs.old

build-regenerated-from-dafny:
	chmod u+x DafnyGeneratedFromDafny.sh
	./DafnyGeneratedFromDafny.sh $(REGENERATED_FROM_DAFNY)

test: build-regenerated-from-dafny
	(diff $(GENERATED_FROM_DAFNY) $(REGENERATED_FROM_DAFNY) || (echo 'Consider running `make dfy-to-cs`'; exit 1; ))
	(diff ../DafnyCore.Test/$(GENERATED_FROM_DAFNY) ../DafnyCore.Test/$(REGENERATED_FROM_DAFNY) || (echo 'Consider running `make dfy-to-cs`'; exit 1; ))
	rm -rf $(REGENERATED_FROM_DAFNY)
	rm -rf ../DafnyCore.Test/$(REGENERATED_FROM_DAFNY)

format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

extract:
	(cd Prelude; make update; cd ..)

check-extract:
	(cd Prelude; make check; cd ..)
