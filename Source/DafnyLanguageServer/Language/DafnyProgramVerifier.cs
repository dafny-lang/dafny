using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using VC;
using Microsoft.Dafny.LanguageServer.Workspace;
using VCGeneration;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// dafny-lang based implementation of the program verifier. Since it makes use of static members,
  /// any access is synchronized. Moreover, it ensures that exactly one instance exists over the whole
  /// application lifetime.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this verifier serializes all invocations.
  /// </remarks>
  public class DafnyProgramVerifier : IProgramVerifier {
    private static readonly object InitializationSyncObject = new();
    private static bool initialized;

    private readonly ILogger logger;
    private readonly VerifierOptions options;
    private readonly VerificationResultCache cache = new();

    DafnyOptions Options => DafnyOptions.O;

    private DafnyProgramVerifier(
      ILogger<DafnyProgramVerifier> logger,
      VerifierOptions options
      ) {
      this.logger = logger;
      this.options = options;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the verifier. It ensures that global/static
    /// settings are set exactly ones.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this verifier instance.</param>
    /// <param name="options">Settings for the verifier.</param>
    /// <returns>A safely created dafny verifier instance.</returns>
    public static DafnyProgramVerifier Create(
      ILogger<DafnyProgramVerifier> logger, IOptions<VerifierOptions> options) {
      lock (InitializationSyncObject) {
        if (!initialized) {
          // TODO This may be subject to change. See Microsoft.Boogie.Counterexample
          //      A dash means write to the textwriter instead of a file.
          // https://github.com/boogie-org/boogie/blob/b03dd2e4d5170757006eef94cbb07739ba50dddb/Source/VCGeneration/Couterexample.cs#L217
          DafnyOptions.O.ModelViewFile = "-";
          DafnyOptions.O.VerifySnapshots = (int)options.Value.VerifySnapshots;
          initialized = true;
          logger.LogTrace("Initialized the boogie verifier with " +
                          "VerifySnapshots={VerifySnapshots}.",
                          DafnyOptions.O.VerifySnapshots);
        }
        return new DafnyProgramVerifier(logger, options.Value);
      }
    }

    private static int GetConfiguredCoreCount(VerifierOptions options) {
      return options.VcsCores == 0
        ? Math.Max(1, Environment.ProcessorCount / 2)
        : Convert.ToInt32(options.VcsCores);
    }


    private const int TranslatorMaxStackSize = 0x10000000; // 256MB
    static readonly ThreadTaskScheduler TranslatorScheduler = new(TranslatorMaxStackSize);

    public IReadOnlyList<IImplementationTask> Verify(DafnyDocument document,
      IVerificationProgressReporter progressReporter) {
      var program = document.Program;
      var errorReporter = (DiagnosticErrorReporter)program.Reporter;
      if (options.GutterStatus) {
        progressReporter.RecomputeVerificationTree();
        progressReporter.ReportRealtimeDiagnostics(false, document);
      }

      var printer = new ModelCapturingOutputPrinter(logger, progressReporter, options.GutterStatus);
      // Do not set these settings within the object's construction. It will break some tests within
      // VerificationNotificationTest and DiagnosticsTest that rely on updating these settings.
      DafnyOptions.O.TimeLimit = options.TimeLimit;
      DafnyOptions.O.VcsCores = GetConfiguredCoreCount(options);
      DafnyOptions.O.Printer = printer;

      var executionEngine = new ExecutionEngine(DafnyOptions.O, cache);
#pragma warning disable VSTHRD002
      var translated = Task.Factory.StartNew(() => Translator.Translate(program, errorReporter, new Translator.TranslatorFlags {
        InsertChecksums = true,
        ReportRanges = true
      }).ToList(), CancellationToken.None, TaskCreationOptions.None, TranslatorScheduler).Result;
#pragma warning restore VSTHRD002
      return translated.SelectMany(t => {
        var (_, boogieProgram) = t;
        var results = executionEngine.GetImplementationTasks(boogieProgram);
        return results;
      }).ToList();
    }

    private class ModelCapturingOutputPrinter : OutputPrinter {
      private readonly ILogger logger;
      private readonly IVerificationProgressReporter progressReporter;
      private readonly bool reportVerificationDiagnostics;

      public ModelCapturingOutputPrinter(
          ILogger logger,
          IVerificationProgressReporter progressReporter,
          bool reportVerificationDiagnostics) {
        this.logger = logger;
        this.progressReporter = progressReporter;
        this.reportVerificationDiagnostics = reportVerificationDiagnostics;
      }

      public void AdvisoryWriteLine(TextWriter writer, string format, params object[] args) {
      }

      public ExecutionEngineOptions? Options { get; set; }

      public void ErrorWriteLine(TextWriter tw, string s) {
        logger.LogError(s);
      }

      public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
        logger.LogError(format, args);
      }

      public void Inform(string s, TextWriter tw) {
        logger.LogInformation(s);
      }

      public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, [AllowNull] string category) {
        logger.LogError(message);
      }

      public void ReportImplementationsBeforeVerification(Implementation[] implementations) {
        if (reportVerificationDiagnostics) {
          progressReporter.ReportImplementationsBeforeVerification(implementations);
        }
      }

      public void ReportStartVerifyImplementation(Implementation implementation) {
        if (reportVerificationDiagnostics) {
          progressReporter.ReportStartVerifyImplementation(implementation);
        }
      }

      public void ReportEndVerifyImplementation(Implementation implementation, Boogie.VerificationResult result) {
        if (reportVerificationDiagnostics) {
          progressReporter.ReportEndVerifyImplementation(implementation, result);
        }
      }

      public void ReportSplitResult(Split split, VCResult vcResult) {
        if (reportVerificationDiagnostics) {
          progressReporter.ReportAssertionBatchResult(split, vcResult);
        }
      }

      public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace) {
      }

      public void WriteTrailer(TextWriter writer, PipelineStatistics stats) {
      }
    }
  }
}
