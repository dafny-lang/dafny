# ###############################################################################
# The frame files are no longer in this directory. They must be downloaded
# from http://boogiepartners.codeplex.com/. Update the FRAME_DIR variable to
# point to whatever directory you install that into.
# ###############################################################################
FRAME_DIR = ..\..\third_party\Coco\src

# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
all: Parser.cs

Parser.cs: $(FRAME_DIR)\scanner.frame $(FRAME_DIR)\parser.frame Dafny.atg
	dotnet tool run coco Dafny.atg -namespace Microsoft.Dafny -frames $(FRAME_DIR)

clean:
	if exist Scanner.cs del Scanner.cs
	if exist Scanner.cs.old del Scanner.cs.old
	if exist Parser.cs del Parser.cs
	if exist Parser.cs.old del Parser.cs.old
