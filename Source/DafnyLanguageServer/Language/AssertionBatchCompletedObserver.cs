using System;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Reactive.Subjects;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using VC;
using VCGeneration;

namespace Microsoft.Dafny.LanguageServer.Language;

public class AssertionBatchCompletedObserver : OutputPrinter {
  private readonly ILogger logger;
  private readonly bool reportCompletedBatches;
  private readonly Subject<AssertionBatchResult> completedBatches = new();

  public AssertionBatchCompletedObserver(
    ILogger logger,
    bool reportCompletedBatches
    ) {
    this.logger = logger;
    this.reportCompletedBatches = reportCompletedBatches;
  }

  public IObservable<AssertionBatchResult> CompletedBatches => completedBatches;

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

  public void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, [AllowNull] string category) {
    logger.LogError(message);
  }

  public void ReportImplementationsBeforeVerification(Implementation[] implementations) {
  }

  public void ReportStartVerifyImplementation(Implementation implementation) {
  }

  public void ReportEndVerifyImplementation(Implementation implementation, Boogie.VerificationResult result) {
  }

  public void ReportSplitResult(Split split, VCResult vcResult) {
    if (reportCompletedBatches) {
      completedBatches.OnNext(new AssertionBatchResult(split.Implementation, vcResult));
    }
  }

  public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace) {
  }

  public void WriteTrailer(TextWriter writer, PipelineStatistics stats) {
  }
}
