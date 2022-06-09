// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

// This is an experimental API for using Dafny as a library.
// We expect it to change from version to version as we discover which features are needed by clients.

using System.Runtime.Versioning;

namespace Microsoft.Dafny {
  public class DafnyEngine {
    public DafnyOptions Options { get; }
    public ErrorReporter Reporter { get; private set; }
    public Boogie.ExecutionEngine BoogieEngine { get; }

    private static DafnyEngine? _singleton;

    public static DafnyEngine Init(ErrorReporter reporter, string[] commandLineOptions) {
      _singleton ??= new DafnyEngine();
      _singleton.Reporter = reporter;
      _singleton.Options.Parse(commandLineOptions);
      return _singleton;
    }

    private DafnyEngine() {
      Options = DafnyOptions.Create();
      Reporter = new ErrorReporterSink();
      BoogieEngine = Boogie.ExecutionEngine.CreateWithoutSharedCache(Options);
      DafnyOptions.Install(Options);
    }

    public DafnyInput CreateDafnyInput(string fname, string source) {
      return new DafnyInput(this, fname, source);
    }
  }

  public class DafnyInput {
    private readonly DafnyEngine engine;
    public string FileName { get; init; }
    public string Source { get; init; }

    internal DafnyInput(DafnyEngine engine, string fname, string source) {
      this.engine = engine;
      FileName = fname;
      Source = source;
    }

    public bool Verify() {
      return Translate() is { } boogieModules && VerifyBoogieModules(boogieModules);
    }

    public Program? Parse() {
      var module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var builtIns = new BuiltIns();
      var errors = new Errors(engine.Reporter);
      if (Parser.Parse(Source, FileName, FileName, null, module, builtIns, errors) == 0 &&
          Main.ParseIncludes(module, builtIns, new List<string>(), errors) == null) {
        return new Program(FileName, module, builtIns, engine.Reporter);
      }

      return null;
    }

    public Program? Resolve() {
      return Parse() is { } parsedProgram ? Resolve(parsedProgram) : null;
    }

    private Program? Resolve(Program parsedProgram) {
      new Resolver(parsedProgram).ResolveProgram(parsedProgram);
      return engine.Reporter.Count(ErrorLevel.Error) == 0 ? parsedProgram : null;
    }

    private List<Tuple<string, Boogie.Program>>? Translate(Program resolvedProgram) {
      var flags = new Translator.TranslatorFlags {InsertChecksums = true, UniqueIdPrefix = FileName};
      return Translator.Translate(resolvedProgram, engine.Reporter, flags).ToList();
    }

    public List<Tuple<string, Boogie.Program>>? Translate() {
      return (Resolve() is { } resolvedProgram) ? Translate(resolvedProgram) : null;
    }

    public bool VerifyBoogieModule(string moduleName, Microsoft.Boogie.Program boogieProgram) {
      if (boogieProgram.Resolve(engine.Options) == 0 && boogieProgram.Typecheck(engine.Options) == 0) {
        engine.BoogieEngine.EliminateDeadVariables(boogieProgram);
        engine.BoogieEngine.CollectModSets(boogieProgram);
        engine.BoogieEngine.CoalesceBlocks(boogieProgram);
        engine.BoogieEngine.Inline(boogieProgram);

        // FIXME: Use reporter
        switch (engine.BoogieEngine.InferAndVerify(Console.Out, boogieProgram, new Boogie.PipelineStatistics(),
                  "ServerProgram_" + moduleName, null, DateTime.UtcNow.Ticks.ToString()).Result) {
          case Boogie.PipelineOutcome.Done:
          case Boogie.PipelineOutcome.VerificationCompleted:
            return true;
        }
      }

      return false;
    }

    public bool VerifyBoogieModules(List<Tuple<string, Boogie.Program>> boogieModules) {
      foreach (var (moduleName, boogieProgram) in boogieModules) {
        if (!VerifyBoogieModule(moduleName, boogieProgram)) {
          return false;
        }
      }

      return true;
    }
  }
}
