COCO = ..\..\Binaries\Coco.exe

# ###############################################################################
# The frame files are no longer in this directory. They must be downloaded
# from http://boogiepartners.codeplex.com/ and then copied into this directory.
# ###############################################################################
FRAME_DIR = c:\boogiepartners\Dafny\Source

# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
all: Parser.ssc 

Parser.ssc: $(FRAME_DIR)\Scanner.frame $(FRAME_DIR)\Parser.frame Dafny.atg
	$(COCO) Dafny.atg -namespace Microsoft.Dafny -frames $(FRAME_DIR)
	copy Parser.cs Parser.ssc
	copy Scanner.cs Scanner.ssc

clean:
	if exist Scanner.ssc del Scanner.ssc
	if exist Scanner.cs del Scanner.cs
	if exist Scanner.cs.old del Scanner.cs.old
	if exist Parser.ssc del Parser.ssc
	if exist Parser.cs del Parser.cs
	if exist Parser.cs.old del Parser.cs.old
