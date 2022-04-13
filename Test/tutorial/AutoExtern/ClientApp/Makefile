ROOT ?= ../../../../
AutoExtern := $(ROOT)/Source/AutoExtern/AutoExtern.csproj

ifeq (,$(wildcard $(AutoExtern)))
default: dotnet-run
else
default: skip
endif

LibraryProjectFile := ../Library/Library.csproj
LibrarySourceFile := ../Library/Library.cs
LibraryRootNamespace := Library

LibraryTemplateFile := LibraryModel.dfy.template
LibraryModelFile := LibraryModel.dfy

AppCSharpFile := Main.cs
AppDafnyFile := GroceryListPrinter.dfy
ExpectFile := $(AppDafnyFile).expect

$(LibraryModelFile): $(LibraryProjectFile) $(LibrarySourceFile) $(LibraryTemplateFile)
	dotnet run --project $(AutoExtern) -- \
		$(LibraryProjectFile) $(LibrarySourceFile) $(LibraryRootNamespace) $(LibraryTemplateFile) \
		> $(LibraryModelFile)

dotnet-run: $(LibraryModelFile) $(AppCSharpFile) $(AppDafnyFile)
	@dotnet run

skip:
	@echo "$(AutoExtern) not found; skipping this test."
	@echo "You must build Dafny from source to use AutoExtern."

clean:
	rm -f $(LibraryModelFile)
