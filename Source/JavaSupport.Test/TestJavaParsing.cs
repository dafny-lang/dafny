using Microsoft.Dafny;
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
  
  
  [Fact]
  public void TestSecondExample() {
    var input = @"
class Fib {
  static int FibonacciSpec(int n) {
    return n < 2 ? n : FibonacciSpec(n - 1) + FibonacciSpec(n - 2);
  }

  static int Fibonacci(int n)
    // ensures result == FibonacciSpec(n)
  {
    if (n == 0) {
      return 0;
    }

    int iMinMinResult = 0;
    int iResult = 1;
    int i = 1;
    while(i < n)
      // invariant iResult == FibonacciSpec(i)
      // invariant iMinMinResult == FibonacciSpec(i - 1)
      // invariant i <= n
    {
      i = i + 1;
      int temp = iResult + iMinMinResult;
      iMinMinResult = iResult;
      iResult = temp;
    }
    return iResult;
  }
}";
    var jg = new JavaGrammar(new Uri(Directory.GetCurrentDirectory()));
    var programGrammar = jg.GetFinalGrammar();
    var parser = programGrammar.ToParser();
    var parseResult = parser.Parse(input);
    Assert.NotNull(parseResult.ForceSuccess.Value);
  }
}