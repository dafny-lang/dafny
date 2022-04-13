AutoExtern := ../../../../Source/AutoExtern/AutoExtern.csproj

LibraryProjectFile := ../Library/Library.csproj
LibrarySourceFile := ../Library/Library.cs
LibraryRootNamespace := Library

LibraryTemplateFile := LibraryModel.dfy.template
LibraryModelFile := LibraryModel.dfy

AppCSharpFile := Main.cs
AppDafnyFile := GroceryListPrinter.dfy
ExpectFile := $(AppDafnyFile).expect

default: dotnet-run

$(LibraryModelFile): $(LibraryProjectFile) $(LibrarySourceFile) $(LibraryTemplateFile)
	dotnet run --project $(AutoExtern) -- \
		$(LibraryProjectFile) $(LibrarySourceFile) $(LibraryRootNamespace) $(LibraryTemplateFile) \
		> $(LibraryModelFile)

dotnet-run: $(LibraryModelFile) $(AppCSharpFile) $(AppDafnyFile)
	@dotnet run

clean:
	rm -f $(LibraryModelFile)
