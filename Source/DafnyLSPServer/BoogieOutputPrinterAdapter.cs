using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Dafny.LSPServer
{
  abstract class BoogieOutputPrinterAdapter : OutputPrinter
  {
    public abstract void AdvisoryWriteLine(string format, params object[] args);
    public abstract void ErrorWriteLine(TextWriter tw, string s);
    public void ErrorWriteLine(TextWriter tw, string format, params object[] args)
    {
      Contract.Requires(format != null);
      string s = string.Format(format, args);
      ErrorWriteLine(tw, s);
    }

    public void Inform(string s, TextWriter tw)
    {
      if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.TraceProofObligations)
      {
        tw.WriteLine(s);
      }
    }

    public abstract void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null);

    public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
    {
      Contract.Requires(errorInfo != null);

      ReportBplError(errorInfo.Tok, errorInfo.FullMsg, true, tw);

      // TODO investigate whether this is RelatedInformation for the above diagnostics.
      foreach (var e in errorInfo.Aux)
      {
        if (!(skipExecutionTrace && e.Category != null && e.Category.Contains("Execution trace")))
        {
          ReportBplError(e.Tok, e.FullMsg, false, tw);
        }
      }

      tw.Write(errorInfo.Out.ToString());
      tw.Write(errorInfo.Model.ToString());
      tw.Flush();
    }

    public abstract void WriteTrailer(PipelineStatistics stats);
  }
}
