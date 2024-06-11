AutoExtern ?= dotnet run --project ../../../AutoExtern/AutoExtern.csproj --
Dafny ?= dotnet run --project ../../../Dafny/Dafny.csproj --

LibraryProjectFile := ../Library/Library.csproj
AutoExternSources := ../Library/GroceryLists.cs ../Library/LinkedLists.cs
ManuallyTranslatedSources :=  ../Library/ExactArithmetic.cs
LibraryRootNamespace := App.Library
LibraryRewrites := --rewrite App.ExactArithmetic.:ExactArithmetic.

LibraryTemplateFile := LibraryModel.dfy.template
LibraryModelFile := LibraryModel.dfy
CSharpModelFile := CSharpModel.dfy

AppCSharpFile := Main.cs
AppDafnyFile := GroceryListPrinter.dfy
AppDafnyCSharpFile := GroceryListPrinter.cs
ExpectFile := $(AppDafnyFile).expect

default: dotnet-run

$(LibraryModelFile): $(LibraryProjectFile) $(AutoExternSources) $(ManuallyTranslatedSources)  $(LibraryTemplateFile)
	$(AutoExtern) \
		$(LibraryProjectFile) \
		$(LibraryRootNamespace) \
		$(LibraryTemplateFile) \
		$(CSharpModelFile) \
		$(LibraryModelFile) \
		$(LibraryRewrites) \
		$(AutoExternSources)

$(AppDafnyCSharpFile): $(AppDafnyFile)
	$(Dafny) -compile:0 -noVerify -spillTargetCode:3 "$<"

dotnet-run: $(LibraryModelFile) $(AppCSharpFile) $(AppDafnyCSharpFile)
	dotnet run

clean:
	rm -fr obj bin
	rm -f $(LibraryModelFile) $(CSharpModelFile) $(AppDafnyCSharpFile)
