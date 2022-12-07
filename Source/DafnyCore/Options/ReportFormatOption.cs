using System;

namespace Microsoft.Dafny;

public class ReportFormatOption : StringOption {
  public static readonly ReportFormatOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "report-format";
  public override string ArgumentName => "format";

  public override string Description => @"
Specify the file format to use for the audit report. Supported options include:
plain text in the format of warnings ('txt', 'text'); standalone HTML ('html');
a Markdown table ('md', 'markdown', 'md-table', 'markdown-table'); or
an IETF-language document in Markdown format ('md-ietf', 'markdown-ietf').
With no option given, the format will be inferred from the filename extension.
With no filename or format given, the report will consist of standard Dafny
warnings.";

  public override string PostProcess(DafnyOptions options) {
    string formatName = Get(options);
    options.AuditReportFormat = formatName switch {
      "text" => DafnyOptions.ReportFormat.Text,
      "txt" => DafnyOptions.ReportFormat.Text,
      "html" => DafnyOptions.ReportFormat.HTML,
      "md" => DafnyOptions.ReportFormat.MarkdownTable,
      "markdown" => DafnyOptions.ReportFormat.MarkdownTable,
      "markdown-table" => DafnyOptions.ReportFormat.MarkdownTable,
      "md-table" => DafnyOptions.ReportFormat.MarkdownTable,
      "markdown-ietf" => DafnyOptions.ReportFormat.MarkdownIETF,
      "md-ietf" => DafnyOptions.ReportFormat.MarkdownIETF,
      _ => throw new ArgumentException("TODO")
    };
    return null;
  }
}