using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class AuditCommand : ICommandSpec {
  public static readonly Option<string> ReportFileOption = new("--report-file",
    "Specify a path to store the audit report file. Without this, the report will take the form of standard warnings.");
  public static readonly Option<bool> CompareReportOption = new("--compare-report",
    "Compare the report that would have been generated with the existing file given by --report-file, and fail if they differ.");

  public static string SupportedReportFormats = "plain text in the format of warnings ('txt', 'text'); standalone HTML ('html'); a Markdown table ('md', 'markdown', 'md-table', 'markdown-table'); or an IETF-language document in Markdown format ('md-ietf', 'markdown-ietf')";

  public static readonly Option<Auditor.ReportFormat?> ReportFormatOption = new("--report-format",
    arg => {
      if (arg.Tokens.Any()) {
        switch (arg.Tokens[0].Value) {
          case "md":
          case "md-table":
          case "markdown":
          case "markdown-table":
            return Auditor.ReportFormat.MarkdownTable;
          case "md-ietf":
          case "markdown-ietf":
            return Auditor.ReportFormat.MarkdownIETF;
          case "html":
            return Auditor.ReportFormat.HTML;
          case "text":
          case "txt":
            return Auditor.ReportFormat.Text;
          default:
            arg.ErrorMessage =
              $"Unsupported report format. Supported formats are: {SupportedReportFormats}";
            return null;
        }
      }

      return null;
    },
    false,
    $"Specify the file format to use for the audit report. Supported options include: {SupportedReportFormats}. With no option given, the format will be inferred from the filename extension. With no filename or format given, the report will consist of standard Dafny warnings.");

  public IEnumerable<Option> Options => new Option[] {
    ReportFileOption,
    ReportFormatOption,
    CompareReportOption
  }.Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("audit", "Audit the program, optionally creating a report document.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    dafnyOptions.Verify = false;
    dafnyOptions.AuditProgram = true;
    dafnyOptions.AuditorReportFile = dafnyOptions.Get(ReportFileOption);
    dafnyOptions.AuditReportFormat = dafnyOptions.Get(ReportFormatOption);
    dafnyOptions.CompareAuditReport = dafnyOptions.Get(CompareReportOption);
  }
}
