using System.Diagnostics.CodeAnalysis;
using System.IO;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using VCGeneration;

namespace Microsoft.Dafny.LanguageServer.Language;

public class OutputLogger : OutputPrinter {
  private readonly ILogger logger;

  public OutputLogger(ILogger logger) {
    this.logger = logger;
  }

  public void AdvisoryWriteLine(TextWriter writer, string format, params object[] args) {
  }

  public void ReportEndVerifyImplementation(Implementation implementation, VerificationResult result) {
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
