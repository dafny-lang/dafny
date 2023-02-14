using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test {
  // Main.Resolve has static shared state (TypeConstraint.ErrorsToBeReported for example)
  // so we can't execute tests that use it in parallel.
  [Collection("Singleton Test Collection - Resolution")]
  public class Issue1355 {
    [Fact]
    public void Test() {
      ErrorReporter reporter = new ConsoleErrorReporter();
      var options = DafnyOptions.Create();
      options.DafnyPrelude = "../../../../../Binaries/DafnyPrelude.bpl";
      DafnyOptions.Install(options);

      var programString = @"trait Trait<A, B> { }";
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      Microsoft.Dafny.Type.ResetScopes();
      BuiltIns builtIns = new BuiltIns();
      Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
      var dafnyProgram = new Program("programName", module, builtIns, reporter, options);
      Main.Resolve(dafnyProgram, reporter);
      foreach (var prog in Translator.Translate(dafnyProgram, dafnyProgram.Reporter)) {
        var writer = new StringWriter();
        var tokenWriter = new Bpl.TokenTextWriter("virtual", writer, true, options);
        prog.Item2.Emit(tokenWriter);
        var parseErrorCount = Bpl.Parser.Parse(writer.ToString(), "virtualBoogie", out var boogieProgram);
        Assert.Equal(0, parseErrorCount);
      }
    }
  }
}
