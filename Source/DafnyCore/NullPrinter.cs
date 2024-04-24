using System.IO;
using Microsoft.Boogie;
using VCGeneration;

namespace Microsoft.Dafny;

public class NullPrinter : OutputPrinter {
  public void ErrorWriteLine(TextWriter tw, string s) {
  }

  public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
  }

  public void AdvisoryWriteLine(TextWriter output, string format, params object[] args) {
  }

  public void Inform(string s, TextWriter tw) {
  }

  public void WriteTrailer(TextWriter textWriter, Boogie.PipelineStatistics stats) {
  }

  public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
  }

  public void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string category = null) {
  }

  public void ReportEndVerifyImplementation(Boogie.Implementation implementation, Boogie.ImplementationRunResult result) {
  }

  public Boogie.ExecutionEngineOptions Options { get; set; }
}