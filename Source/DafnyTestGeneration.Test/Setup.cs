// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit;
using Program = Microsoft.Dafny.Program;
using Token = Microsoft.Dafny.Token;

// These tests are frequently hanging and timing out for reasons unknown.
// It seems to be much harder to reproduce locally if tests are run sequentially
// (as they are in debugging mode by default)
// so as a stop gap we're trying disabling parallel execution
// in the hopes it at least reduces the frequency of hanging.
// See https://github.com/dafny-lang/dafny/issues/5488.
[assembly: CollectionBehavior(DisableTestParallelization = true)]

namespace DafnyTestGeneration.Test {

  public class Setup {
    private readonly CancellationTokenSource cancellationTokenSource = new();

    public Setup() {
      cancellationTokenSource.CancelAfter(TimeSpan.FromSeconds(50));
    }

    public CancellationToken CancellationToken => cancellationTokenSource.Token;

    protected static DafnyOptions GetDafnyOptions(List<Action<DafnyOptions>> optionSettings, TextWriter writer, params string[] arguments) {
      var options = DafnyOptions.CreateUsingOldParser(writer, TextReader.Null, arguments ?? []);
      options.DefiniteAssignmentLevel = 3;
      options.WarnShadowing = true;
      options.VerifyAllModules = true;
      options.TestGenOptions.SeqLengthLimit = 3;
      options.TestGenOptions.Mode = TestGenerationOptions.Modes.Block;
      options.TestGenOptions.WarnDeadCode = false;
      options.TestGenOptions.IgnoreWarnings = false;
      options.TimeLimit = 10;
      foreach (var optionSetting in optionSettings) {
        optionSetting(options);
      }
      return options;
    }

    public static TheoryData<List<Action<DafnyOptions>>> OptionSettings() {
      var optionSettings = new TheoryData<List<Action<DafnyOptions>>>();
      optionSettings.Add([options => options.TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates]);
      return optionSettings;
    }

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public Task<Program> /*?*/ Parse(ErrorReporter reporter, string source, bool resolve = true, Uri uri = null) {
      return Utils.Parse(reporter, source, resolve, uri, cancellationToken: CancellationToken);
    }

    protected Task<List<TestMethod>> GetTestMethodsForProgram(Program program) {
      return TestGenerator.GetTestMethodsForProgram(program).ToListAsync(CancellationToken).AsTask().WaitAsync(CancellationToken);
    }
  }
}
