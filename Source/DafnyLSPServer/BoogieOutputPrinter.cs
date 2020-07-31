using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using System.Collections.Generic;
using System.IO;

namespace Microsoft.Dafny.LSPServer
{

  class BoogieOutputPrinter : BoogieOutputPrinterAdapter
  {
    readonly DiagnosticErrorReporter parent;

    public BoogieOutputPrinter(DiagnosticErrorReporter parent)
    {
      this.parent = parent;
    }


    public override void ReportBplError(IToken token, string message, bool error, TextWriter tw, string category = null)
    {
      // Commenting this out because it was causing duplicate errors, but leaving it in since it has 'related information' logic which should prove useful.
      //var item = new Diagnostic
      //{
      //  Severity = error ? DiagnosticSeverity.Error : DiagnosticSeverity.Information,
      //  Message = message,
      //  // Dafny has 0-indexed columns, but Boogie counts from 1
      //  Range = BoogieToLspPosition(token).ToSingleLengthRange()
      //};

      //if (token is NestedToken nestedToken)
      //{
      //  var relatedInformation = new List<DiagnosticRelatedInformation>();
      //  item.RelatedInformation = relatedInformation;
      //  relatedInformation.Add(new DiagnosticRelatedInformation()
      //  {
      //    Message = "Related location",
      //    Location = new Location()
      //    {
      //      Range = BoogieToLspPosition(nestedToken.Inner).ToSingleLengthRange(),
      //      Uri = nestedToken.Inner.filename
      //    }
      //  });
      //}

      //parent.AddDiagnosticForFile(item, token.filename);
    }

    public override void ErrorWriteLine(TextWriter tw, string s)
    {
      throw new NotImplementedException();
    }

    public override void AdvisoryWriteLine(string format, params object[] args)
    {
      throw new NotImplementedException();
    }

    public override void WriteTrailer(PipelineStatistics stats)
    {
      throw new NotImplementedException();
    }

  }
}
