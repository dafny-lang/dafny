AutoExtern := ../../../../Source/AutoExtern/AutoExtern.csproj

LibraryProjectFile := ../Library/Library.csproj
LibrarySourceFile := ../Library/Library.cs
LibraryRootNamespace := Library

LibraryTemplateFile := LibraryModel.dfy.template
LibraryModelFile := LibraryModel.dfy

AppCSharpFile := Main.cs
AppDafnyFile := GroceryListPrinter.dfy
ExpectFile := $(AppDafnyFile).expect

default: $(ExpectFile)

$(LibraryModelFile): $(LibraryProjectFile) $(LibrarySourceFile) $(LibraryTemplateFile)
	dotnet run --project $(AutoExtern) -- \
		$(LibraryProjectFile) $(LibrarySourceFile) $(LibraryRootNamespace) $(LibraryTemplateFile) \
		> $(LibraryModelFile)

$(ExpectFile): $(LibraryModelFile) $(AppCSharpFile) $(AppDafnyFile)
	dotnet run > $(ExpectFile)

clean:
	rm -f $(LibraryModelFile)
