using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.IntegrationTest;
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
    public void Test() {
      var options = DafnyOptions.Create(output);
      ErrorReporter reporter = new ConsoleErrorReporter(options);
      options.DafnyPrelude = "../../../../../Binaries/DafnyPrelude.bpl";

      var programString = @"trait Trait<A, B> { }";
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDefinition(), null);
      Microsoft.Dafny.Type.ResetScopes();
      BuiltIns builtIns = new BuiltIns(options);
      Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
      var dafnyProgram = new Program("programName", module, builtIns, reporter);
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
