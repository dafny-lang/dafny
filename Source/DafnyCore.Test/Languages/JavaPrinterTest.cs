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
    var grammarBuilder = new JavaGrammar(new Uri(Directory.GetCurrentDirectory()));
    var grammar = grammarBuilder.GetFinalGrammar();
    var parser = grammar.ToParser();
    var printer = grammar.ToPrinter();

    var parsed = parser.Parse(input).Success!.Value;
    var outputWriter = new StringWriter();
    printer.Print(parsed)!.Render(outputWriter);

    var output = outputWriter.ToString();
    Assert.Equal(input, output);
  }
}