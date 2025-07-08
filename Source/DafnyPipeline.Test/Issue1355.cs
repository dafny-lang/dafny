using System.IO;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test {
  // Main.Resolve has static shared state (TypeConstraint.ErrorsToBeReported for example)
  // so we can't execute tests that use it in parallel.
  [Collection("Singleton Test Collection - Resolution")]
  public class Issue1355 {
    private readonly TextWriter output;

    public Issue1355(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
    }

    [Fact]
    public async Task Test() {
      var options = DafnyOptions.CreateUsingOldParser(output);
      options.DafnyPrelude = "../../../../../Binaries/DafnyPrelude.bpl";

      var programString = @"trait Trait<A, B> { }";
      var dafnyProgram = await Utils.Parse(new BatchErrorReporter(options), programString, false);
      DafnyMain.Resolve(dafnyProgram);
      foreach (var prog in BoogieGenerator.Translate(dafnyProgram, dafnyProgram.Reporter)) {
        var writer = new StringWriter();
        var tokenWriter = new Bpl.TokenTextWriter("virtual", writer, true, options);
        prog.Item2.Emit(tokenWriter);
        var parseErrorCount = Bpl.Parser.Parse(writer.ToString(), "virtualBoogie", out var boogieProgram);
        Assert.Equal(0, parseErrorCount);
      }
    }
  }
}
