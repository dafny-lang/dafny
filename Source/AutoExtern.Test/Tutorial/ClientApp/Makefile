AutoExtern ?= dotnet run --project ../../../AutoExtern/AutoExtern.csproj --
Dafny ?= dotnet run --project ../../../DafnyDriver/DafnyDriver.csproj --

LibraryProjectFile := ../Library/Library.csproj
LibrarySourceFile := ../Library/Library.cs
LibraryRootNamespace := Library

LibraryTemplateFile := LibraryModel.dfy.template
LibraryModelFile := LibraryModel.dfy
CSharpModelFile := CSharpModel.dfy

AppCSharpFile := Main.cs
AppDafnyFile := GroceryListPrinter.dfy
AppDafnyCSharpFile := GroceryListPrinter.cs
ExpectFile := $(AppDafnyFile).expect

default: dotnet-run

$(LibraryModelFile): $(LibraryProjectFile) $(LibrarySourceFile) $(LibraryTemplateFile)
	$(AutoExtern) \
		$(LibraryProjectFile) \
		$(LibrarySourceFile) \
		$(LibraryRootNamespace) \
		$(LibraryTemplateFile) \
		$(CSharpModelFile) \
		$(LibraryModelFile)

$(AppDafnyCSharpFile): $(AppDafnyFile)
	$(Dafny) -compile:0 -noVerify -spillTargetCode:3 "$<"

dotnet-run: $(LibraryModelFile) $(AppCSharpFile) $(AppDafnyCSharpFile)
	dotnet run

clean:
	rm -fr obj bin
	rm -f $(LibraryModelFile) $(CSharpModelFile) $(AppDafnyCSharpFile)
