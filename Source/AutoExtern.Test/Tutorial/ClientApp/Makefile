AutoExtern ?= dotnet run --project ../../../AutoExtern/AutoExtern.csproj --
Dafny ?= dotnet run --project ../../../DafnyDriver/DafnyDriver.csproj --

LibraryProjectFile := ../Library/Library.csproj
LibrarySourceFile1 := ../Library/Library1.cs
LibrarySourceFile2 := ../Library/Library2.cs
LibraryRootNamespace := Library

LibraryTemplateFile := LibraryModel.dfy.template
LibraryModelFile := LibraryModel.dfy
CSharpModelFile := CSharpModel.dfy

AppCSharpFile := Main.cs
AppDafnyFile := GroceryListPrinter.dfy
AppDafnyCSharpFile := GroceryListPrinter.cs
ExpectFile := $(AppDafnyFile).expect

default: dotnet-run

$(LibraryModelFile): $(LibraryProjectFile) $(LibrarySourceFile1) $(LibrarySourceFile2) $(LibraryTemplateFile)
	$(AutoExtern) \
		$(LibraryProjectFile) \
		$(LibraryRootNamespace) \
		$(LibraryTemplateFile) \
		$(CSharpModelFile) \
		$(LibraryModelFile) \
		$(LibrarySourceFile1) \
		$(LibrarySourceFile2)

$(AppDafnyCSharpFile): $(AppDafnyFile)
	$(Dafny) -compile:0 -noVerify -spillTargetCode:3 "$<"

dotnet-run: $(LibraryModelFile) $(AppCSharpFile) $(AppDafnyCSharpFile)
	dotnet run

clean:
	rm -fr obj bin
	rm -f $(LibraryModelFile) $(CSharpModelFile) $(AppDafnyCSharpFile)
