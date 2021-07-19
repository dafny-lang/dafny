using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using System;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

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
    private static readonly object _initializationSyncObject = new();
    private static readonly MessageSource VerifierMessageSource = MessageSource.Other;
    private static bool _initialized;

    private readonly ILogger _logger;
    private readonly SemaphoreSlim _mutex = new(1);

    private DafnyProgramVerifier(ILogger<DafnyProgramVerifier> logger) {
      _logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the verifier. It ensures that global/static
    /// settings are set exactly ones.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this verifier instance.</param>
    /// <returns>A safely created dafny verifier instance.</returns>
    public static DafnyProgramVerifier Create(ILogger<DafnyProgramVerifier> logger) {
      lock(_initializationSyncObject) {
        if(!_initialized) {
          // TODO This may be subject to change. See Microsoft.Boogie.Counterexample
          //      A dash means write to the textwriter instead of a file.
          // https://github.com/boogie-org/boogie/blob/b03dd2e4d5170757006eef94cbb07739ba50dddb/Source/VCGeneration/Couterexample.cs#L217
          DafnyOptions.O.ModelViewFile = "-";
          _initialized = true;
          logger.LogTrace("initialized the boogie verifier...");
        }
        return new DafnyProgramVerifier(logger);
      }
    }

    public async Task<VerificationResult> VerifyAsync(Dafny.Program program, CancellationToken cancellationToken) {
      await _mutex.WaitAsync(cancellationToken);
      try {
        // The printer is responsible for two things: It logs boogie errors and captures the counter example model.
        var errorReporter = program.reporter;
        var printer = new ModelCapturingOutputPrinter(_logger, errorReporter);
        ExecutionEngine.printer = printer;
        var translated = Translator.Translate(program, errorReporter, new Translator.TranslatorFlags { InsertChecksums = true });
        foreach(var (_, boogieProgram) in translated) {
          cancellationToken.ThrowIfCancellationRequested();
          VerifyWithBoogie(boogieProgram, cancellationToken);
        }
        return new VerificationResult(
          Verified: printer.SerializedCounterExamples == null,
          SerializedCounterExamples: printer.SerializedCounterExamples
        );
      } finally {
        _mutex.Release();
      }
    }

    private void VerifyWithBoogie(Boogie.Program program, CancellationToken cancellationToken) {
      program.Resolve();
      program.Typecheck();

      ExecutionEngine.EliminateDeadVariables(program);
      ExecutionEngine.CollectModSets(program);
      ExecutionEngine.CoalesceBlocks(program);
      ExecutionEngine.Inline(program);
      // TODO Is the programId of any relevance? The requestId is used to cancel a verification.
      //      However, the cancelling a verification is currently not possible since it blocks a text document
      //      synchronization event which are serialized. Thus, no event is processed until the pending
      //      synchronization is completed.
      var uniqueId = Guid.NewGuid().ToString();
      using(cancellationToken.Register(() => CancelVerification(uniqueId))) {
        // TODO any use of the verification state?
        ExecutionEngine.InferAndVerify(program, new PipelineStatistics(), uniqueId, error => { }, uniqueId);
      }
    }

    private void CancelVerification(string requestId) {
      _logger.LogDebug("requesting verification cancellation of {RequestId}", requestId);
      ExecutionEngine.CancelRequest(requestId);
    }

    private class ModelCapturingOutputPrinter : OutputPrinter {
      private readonly ILogger _logger;
      private readonly ErrorReporter _errorReporter;
      private StringBuilder? _serializedCounterExamples;

      public string? SerializedCounterExamples => _serializedCounterExamples?.ToString();

      public ModelCapturingOutputPrinter(ILogger logger, ErrorReporter errorReporter) {
        _logger = logger;
        _errorReporter = errorReporter;
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

      public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, [AllowNull] string category) {
        _logger.LogError(message);
      }

      public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace) {
        CaptureCounterExamples(errorInfo);
        CaptureViolatedPostconditions(errorInfo);
      }

      private void CaptureCounterExamples(ErrorInformation errorInfo) {
        if(errorInfo.Model is StringWriter modelString) {
          // We do not know a-priori how many errors we'll receive. Therefore we capture all models
          // in a custom stringbuilder and reset the original one to not duplicate the outputs.
          _serializedCounterExamples ??= new StringBuilder();
          _serializedCounterExamples.Append(modelString.ToString());
          modelString.GetStringBuilder().Clear();
        }
      }

      private void CaptureViolatedPostconditions(ErrorInformation errorInfo) {
        _errorReporter.Error(VerifierMessageSource, errorInfo.Tok, errorInfo.Msg);
        foreach(var auxiliaryErrorInfo in errorInfo.Aux) {
          // The execution trace is an additional auxiliary which identifies itself with
          // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
          // the execution trace message appears to not have any interesting information.
          if(auxiliaryErrorInfo.Tok.line > 0) {
            _errorReporter.Info(VerifierMessageSource, auxiliaryErrorInfo.Tok, auxiliaryErrorInfo.Msg);
          }
        }
      }

      public void WriteTrailer(PipelineStatistics stats) {
      }
    }
  }
}
