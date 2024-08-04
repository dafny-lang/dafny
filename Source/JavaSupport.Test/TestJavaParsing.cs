using Microsoft.VisualStudio.TestPlatform.Utilities;

namespace JavaSupport.Test;

public class TestJavaParsing {
  [Fact]
  public void TestFirstExample() {
    var input = @"
class Div {
  int Foo(int x) {
    return 3 / x;
  }
}";
    var jg = new JavaGrammar(new Uri(Directory.GetCurrentDirectory()));
    var programGrammar = jg.GetFinalGrammar();
    var parser = programGrammar.ToParser();
    var parseResult = parser.Parse(input);
    Assert.NotNull(parseResult.ForceSuccess.Value);
  }
}