# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
all: Parser.cs

Parser.cs: Coco/Scanner.frame Coco/Parser.frame Dafny.atg
	dotnet tool run coco Dafny.atg -namespace Microsoft.Dafny -frames Coco

clean:
	rm -f Scanner.cs Scanner.cs.old Parser.cs Parser.cs.old
