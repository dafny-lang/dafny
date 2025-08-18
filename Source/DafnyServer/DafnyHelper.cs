// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Runtime.Serialization.Json;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using DafnyServer;
using Microsoft.Extensions.Logging.Abstractions;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  class DafnyHelper {
    private string fname;
    private string source;
    private readonly DafnyOptions options;
    private readonly ExecutionEngine engine;
    private string[] args;

    private ErrorReporter reporter;
    private Program dafnyProgram;
    private IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms;
    private readonly CounterExampleProvider counterExampleProvider = new();

    public DafnyHelper(DafnyOptions options, ExecutionEngine engine, string[] args, string fname, string source) {
      this.options = options;
      this.engine = engine;
      this.args = args;
      this.fname = fname;
      this.source = source;
    }

    public async Task<bool> Verify() {
      ServerUtils.ApplyArgs(args, options);
      return await Parse() && Resolve() && Translate() && Boogie();
    }

    private async Task<bool> Parse() {
      var uri = new Uri("transcript:///" + fname);
      reporter = new ConsoleErrorReporter(options);
      var fs = new InMemoryFileSystem(ImmutableDictionary<Uri, string>.Empty.Add(uri, source));
      var file = DafnyFile.HandleDafnyFile(fs, reporter, reporter.Options, uri, Token.NoToken, false);
      var parseResult = await new ProgramParser(NullLogger<ProgramParser>.Instance, OnDiskFileSystem.Instance).ParseFiles(fname, new[] { file },
        reporter, CancellationToken.None);

      var success = !reporter.HasErrors;
      if (success) {
        dafnyProgram = parseResult.Program;
      }
      return success;
    }

    private bool Resolve() {
      var resolver = new ProgramResolver(dafnyProgram);
#pragma warning disable VSTHRD002
      resolver.Resolve(CancellationToken.None).Wait();
#pragma warning restore VSTHRD002
      return reporter.Count(ErrorLevel.Error) == 0;
    }

    private bool Translate() {
      boogiePrograms = BoogieGenerator.Translate(dafnyProgram, reporter,
          new BoogieGenerator.TranslatorFlags(options) { InsertChecksums = true, UniqueIdPrefix = fname }).ToList(); // FIXME how are translation errors reported?
      return true;
    }

    private bool BoogieOnce(string moduleName, Bpl.Program boogieProgram) {
      if (boogieProgram.Resolve(options) == 0 && boogieProgram.Typecheck(options) == 0) { //FIXME ResolveAndTypecheck?
        engine.EliminateDeadVariables(boogieProgram);
        engine.CollectModifies(boogieProgram);
        engine.CoalesceBlocks(boogieProgram);
        engine.Inline(boogieProgram);

        //NOTE: We could capture errors instead of printing them (pass a delegate instead of null)
        switch (engine.InferAndVerify(options.BaseOutputWriter, boogieProgram, new PipelineStatistics(),
#pragma warning disable VSTHRD002
                  "ServerProgram_" + moduleName, null, DateTime.UtcNow.Ticks.ToString()).Result) {
#pragma warning restore VSTHRD002
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            return true;
        }
      }

      return false;
    }

    private bool Boogie() {
      var isVerified = true;
      foreach (var boogieProgram in boogiePrograms) {
        isVerified = isVerified && BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);
      }
      return isVerified;
    }

    public async Task Symbols() {
      ServerUtils.ApplyArgs(args, options);
      if (await Parse() && Resolve()) {
        var symbolTable = new SuperLegacySymbolTable(dafnyProgram);
        var symbols = symbolTable.CalculateSymbols();
        await options.BaseOutputWriter.WriteLineAsync("SYMBOLS_START " + ConvertToJson(symbols) + " SYMBOLS_END");
      } else {
        await options.BaseOutputWriter.WriteLineAsync("SYMBOLS_START [] SYMBOLS_END");
      }
    }

    public async Task CounterExample() {
      var listArgs = args.ToList();
      listArgs.Add("/mv:" + counterExampleProvider.ModelBvd);
      ServerUtils.ApplyArgs(listArgs.ToArray(), options);
      try {
        if (await Parse() && Resolve() && Translate()) {
          foreach (var boogieProgram in boogiePrograms) {
            RemoveExistingModel();
            BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);
            var model = counterExampleProvider.LoadCounterModel(options);
            await options.BaseOutputWriter.WriteLineAsync("COUNTEREXAMPLE_START " + ConvertToJson(model) + " COUNTEREXAMPLE_END");
          }
        }
      } catch (Exception e) {
        await options.BaseOutputWriter.WriteLineAsync("Error collection models: " + e.Message);
      }
    }

    private void RemoveExistingModel() {
      if (File.Exists(counterExampleProvider.ModelBvd)) {
        File.Delete(counterExampleProvider.ModelBvd);
      }
    }

    public async Task DotGraph() {
      ServerUtils.ApplyArgs(args, options);

      if (await Parse() && Resolve() && Translate()) {
        foreach (var boogieProgram in boogiePrograms) {
          BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);

          foreach (var impl in boogieProgram.Item2.Implementations) {
            await using var sw = new StreamWriter(fname + impl.Name + ".dot");
            await sw.WriteAsync(boogieProgram.Item2.ProcessLoops(engine.Options, impl).ToDot());
          }
        }
      }
    }

    private static string ConvertToJson<T>(T data) {
      var serializer = new DataContractJsonSerializer(typeof(T));
      using (var ms = new MemoryStream()) {
        serializer.WriteObject(ms, data);
        return Encoding.Default.GetString(ms.ToArray());
      }
    }
  }
}
