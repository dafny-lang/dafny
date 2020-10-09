using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using System;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Language {
  /// <summary>
  /// dafny-lang based implementation of the program verifier. Since it makes use of static members,
  /// any access is synchronized. Moreover, it ensures that exactly one instance exists over the whole
  /// application lifetime.
  /// </summary>
  internal class DafnyProgramVerifier : IProgramVerifier {
    private static readonly object _initializationSyncObject = new object();
    private static bool _initialized;

    private readonly ILogger _logger;
    private readonly SemaphoreSlim _mutex = new SemaphoreSlim(1);

    private DafnyProgramVerifier(ILogger<DafnyProgramVerifier> logger) {
      _logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the verifier. It may only be invoked
    /// once per application lifetime.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this verifier instance.</param>
    /// <returns>A safely created dafny verifier instance.</returns>
    /// <exception cref="InvalidOperationException">Thrown in case of multiple invocations of this factory method.</exception>
    public static DafnyProgramVerifier Create(ILogger<DafnyProgramVerifier> logger) {
      lock(_initializationSyncObject) {
        if(_initialized) {
          throw new InvalidOperationException($"{nameof(DafnyProgramVerifier)} may only be initialized once");
        }
        _initialized = true;
        ExecutionEngine.printer = new VerifierOutputPrinter(logger);
        logger.LogTrace("initialized the boogie verifier...");
        return new DafnyProgramVerifier(logger);
      }
    }

    public async Task VerifyAsync(Microsoft.Dafny.Program program, CancellationToken cancellationToken) {
      await _mutex.WaitAsync(cancellationToken);
      try {
        var translated = Translator.Translate(program, program.reporter, new Translator.TranslatorFlags { InsertChecksums = true });
        foreach(var (_, boogieProgram) in translated) {
          cancellationToken.ThrowIfCancellationRequested();
          VerifyWithBoogie(boogieProgram, program.reporter);
        }
      } finally {
        _mutex.Release();
      }
    }

    private void VerifyWithBoogie(Microsoft.Boogie.Program program, ErrorReporter reporter) {
      program.Resolve();
      program.Typecheck();

      ExecutionEngine.EliminateDeadVariables(program);
      ExecutionEngine.CollectModSets(program);
      ExecutionEngine.CoalesceBlocks(program);
      ExecutionEngine.Inline(program);
      // TODO Are the programId and requestId of any relevance?
      var uniqueId = Guid.NewGuid().ToString();
      // TODO any use of the verification state?
      ExecutionEngine.InferAndVerify(program, new PipelineStatistics(), uniqueId, error => CaptureVerificationError(reporter, error), uniqueId);
    }

    private void CaptureVerificationError(ErrorReporter reporter, ErrorInformation error) {
      // TODO custom error tracking
      reporter.Error(MessageSource.Other, error.Tok, error.Msg);
    }

    private class VerifierOutputPrinter : OutputPrinter {
      private ILogger _logger;

      public VerifierOutputPrinter(ILogger logger) {
        _logger = logger;
      }

      public void AdvisoryWriteLine(string format, params object[] args) {
      }

      public void ErrorWriteLine(TextWriter tw, string s) {
        _logger.LogError(s);
      }

      public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
        _logger.LogError(format, args);
      }

      public void Inform(string s, TextWriter tw) {
        _logger.LogInformation(s);
      }

      public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, [AllowNull] string category = null) {
        _logger.LogError(message);
      }

      public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
      }

      public void WriteTrailer(PipelineStatistics stats) {
      }
    }
  }
}
