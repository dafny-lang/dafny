// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Serialization.Json;
using System.Text;
using System.Threading;
using Microsoft.Boogie;
using DafnyServer;
using Microsoft.Extensions.Logging;
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

    public bool Verify() {
      ServerUtils.ApplyArgs(args, options);
      return Parse() && Resolve() && Translate() && Boogie();
    }

    private bool Parse() {
      var uri = new Uri("transcript:///" + fname);
      reporter = new ConsoleErrorReporter(options);
      var program = new ProgramParser().ParseFiles(fname, new DafnyFile[] { new(reporter.Options, uri, new StringReader(source)) },
        reporter, CancellationToken.None);

      var success = reporter.ErrorCount == 0;
      if (success) {
        dafnyProgram = program;
      }
      return success;
    }

    private bool Resolve() {
      var resolver = new ProgramResolver(dafnyProgram);
      resolver.Resolve(CancellationToken.None);
      return reporter.Count(ErrorLevel.Error) == 0;
    }

    private bool Translate() {
      boogiePrograms = Translator.Translate(dafnyProgram, reporter,
          new Translator.TranslatorFlags(options) { InsertChecksums = true, UniqueIdPrefix = fname }).ToList(); // FIXME how are translation errors reported?
      return true;
    }

    private bool BoogieOnce(string moduleName, Bpl.Program boogieProgram) {
      if (boogieProgram.Resolve(options) == 0 && boogieProgram.Typecheck(options) == 0) { //FIXME ResolveAndTypecheck?
        engine.EliminateDeadVariables(boogieProgram);
        engine.CollectModSets(boogieProgram);
        engine.CoalesceBlocks(boogieProgram);
        engine.Inline(boogieProgram);

        //NOTE: We could capture errors instead of printing them (pass a delegate instead of null)
        switch (engine.InferAndVerify(options.OutputWriter, boogieProgram, new PipelineStatistics(),
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

    public void Symbols() {
      ServerUtils.ApplyArgs(args, options);
      if (Parse() && Resolve()) {
        var symbolTable = new LegacySymbolTable(dafnyProgram);
        var symbols = symbolTable.CalculateSymbols();
        Console.WriteLine("SYMBOLS_START " + ConvertToJson(symbols) + " SYMBOLS_END");
      } else {
        Console.WriteLine("SYMBOLS_START [] SYMBOLS_END");
      }
    }

    public void CounterExample() {
      var listArgs = args.ToList();
      listArgs.Add("/mv:" + counterExampleProvider.ModelBvd);
      ServerUtils.ApplyArgs(listArgs.ToArray(), options);
      try {
        if (Parse() && Resolve() && Translate()) {
          foreach (var boogieProgram in boogiePrograms) {
            RemoveExistingModel();
            BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);
            var model = counterExampleProvider.LoadCounterModel(options);
            Console.WriteLine("COUNTEREXAMPLE_START " + ConvertToJson(model) + " COUNTEREXAMPLE_END");
          }
        }
      } catch (Exception e) {
        Console.WriteLine("Error collection models: " + e.Message);
      }
    }

    private void RemoveExistingModel() {
      if (File.Exists(counterExampleProvider.ModelBvd)) {
        File.Delete(counterExampleProvider.ModelBvd);
      }
    }

    public void DotGraph() {
      ServerUtils.ApplyArgs(args, options);

      if (Parse() && Resolve() && Translate()) {
        foreach (var boogieProgram in boogiePrograms) {
          BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);

          foreach (var impl in boogieProgram.Item2.Implementations) {
            using (StreamWriter sw = new StreamWriter(fname + impl.Name + ".dot")) {
              sw.Write(boogieProgram.Item2.ProcessLoops(engine.Options, impl).ToDot());
            }
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
