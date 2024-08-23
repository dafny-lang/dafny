using Microsoft.Dafny;

namespace DafnyCore.Test.Languages;

public class JavaPrinterTest {

  [Fact]
  public void ParseAndPrint() {
    var input = @"
class Div {
  int Foo(int x)
    requires x != 0
  {
    return 3 / x;
  }
}".TrimStart();
    var grammarBuilder = new JavaGrammar(new Uri(Directory.GetCurrentDirectory()), DafnyOptions.Default);
    var grammar = grammarBuilder.GetFinalGrammar();
    var parser = grammar.ToParser();
    var printer = grammar.ToPrinter();

    var parsed = parser.Parse(input).Success!.Value;
    var output = printer.Print(parsed).ForceSuccess.RenderAsString();
    Assert.Equal(input, output);
  }
}