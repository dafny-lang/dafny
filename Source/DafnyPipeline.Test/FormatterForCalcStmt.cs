using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForCalcStmt")]
public class FormatterForCalcStmt : FormatterBaseTest {
  [Fact]
  public void FormatterWorksForHintsInCalcStatements() {
    FormatterWorksFor(@"
class Test {
  ghost constructor CalcInInitializationPhase() {
    var c0 := new Cell; // fine here
    var g0 := new G(5); // fine here
    calc {
      5;
    ==  { var c1 := new Cell; // error: cannot allocate inside calc hint
          var g1 := new G(5); // error: cannot allocate inside calc hint
        }
      2 + 3;
    }
    assert true by {
      var c2 := new Cell; // error: cannot allocate inside assert-by
      var g2 := new G(5); // error: cannot allocate inside assert-by
    }
    new;
  }
}
");
  }

  public FormatterForCalcStmt([NotNull] ITestOutputHelper output) : base(output)
  {
  }
}
