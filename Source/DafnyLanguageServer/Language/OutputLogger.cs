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

  public AssertionBatchCompletedObserver(ILogger logger) {
    this.logger = logger;
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

  public void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, [AllowNull] string category) {
    logger.LogError(message);
  }

  public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace) {
  }

  public void WriteTrailer(TextWriter writer, PipelineStatistics stats) {
  }
}
