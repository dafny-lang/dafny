#nullable enable
using System;
using System.IO;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Text.RegularExpressions;
using DafnyCore;

namespace Microsoft.Dafny.Auditor;

/// <summary>
/// A rewriter pass that produces an AuditReport and writes it to either
/// standard output or a file, in one of several formats. If neither a file
/// or a format is provided, it reports all assumptions as warnings.
/// </summary>
public class Auditor : IRewriter {
  public enum ReportFormat { HTML, MarkdownTable, MarkdownIETF, Text }

  public static readonly Option<string> ReportFileOption = new("--report-file",
    "Specify a path to store the audit report file. Without this, the report will take the form of standard warnings.");
  public static readonly Option<bool> CompareReportOption = new("--compare-report",
    "Compare the report that would have been generated with the existing file given by --report-file, and fail if they differ.");

  public static string SupportedReportFormats = "plain text in the format of warnings ('txt', 'text'); standalone HTML ('html'); a Markdown table ('md', 'markdown', 'md-table', 'markdown-table'); or an IETF-language document in Markdown format ('md-ietf', 'markdown-ietf')";

  public static Option<ReportFormat?> ReportFormatOption =
    new("--report-format",
      arg => {
        if (arg.Tokens.Any()) {
          switch (arg.Tokens[0].Value) {
            case "md":
            case "md-table":
            case "markdown":
            case "markdown-table":
              return ReportFormat.MarkdownTable;
            case "md-ietf":
            case "markdown-ietf":
              return ReportFormat.MarkdownIETF;
            case "html":
              return ReportFormat.HTML;
            case "text":
            case "txt":
              return ReportFormat.Text;
            default:
              arg.ErrorMessage =
                $"Unsupported report format. Supported formats are: {SupportedReportFormats}";
              return null;
          }
        }

        return null;
      },
      false,
      $"Specify the file format to use for the audit report. Supported options include: {SupportedReportFormats}. " +
               "With no option given, the format will be inferred from the filename extension. " +
               "With no filename or format given, the report will consist of standard Dafny warnings.") { ArgumentHelpName = "format" };

  private readonly string? reportFileName;
  private readonly ReportFormat? reportFormat;
  private readonly bool compareReport;

  static Auditor() {
    ReportFormatOption.FromAmong("html",
                                 "md", "markdown", "md-table", "markdown-table",
                                 "md-ietf", "markdown-ietf",
                                 "txt");

    DooFile.RegisterNoChecksNeeded(
      ReportFileOption,
      ReportFormatOption,
      CompareReportOption
    );
  }

  /// <summary>
  /// Construct an auditor to write to or compare to the given file in the
  /// given format.
  /// </summary>
  /// <param name="reporter">
  /// the reporter to use to emit errors and warnings
  /// </param>
  public Auditor(ErrorReporter reporter) : base(reporter) {
    reportFileName = reporter.Options.Get(ReportFileOption);
    compareReport = reporter.Options.Get(CompareReportOption);
    var format = reporter.Options.Get(ReportFormatOption);
    if (format is null) {
      if (reportFileName is null) {
        return;
      }

      if (reportFileName.EndsWith(".html")) {
        reportFormat = ReportFormat.HTML;
      } else if (reportFileName.EndsWith(".md")) {
        reportFormat = ReportFormat.MarkdownTable;
      } else if (reportFileName.EndsWith(".txt")) {
        reportFormat = ReportFormat.Text;
      } else {
        Reporter.Error(MessageSource.Verifier, Token.NoToken,
          $"Unsupported extension on report filename: {reportFileName}, using plain text. " +
               "Supported extensions are: .html, .md, .txt");
      }
    } else {
      reportFormat = format;
    }
  }

  private static Regex TableRegex = new Regex(@"\{\{TABLE\}\}\r?\n");

  private string GenerateHTMLReport(AuditReport report) {
    var table = report.RenderHTMLTable();
    var assembly = System.Reflection.Assembly.GetCallingAssembly();
    var templateStream = assembly.GetManifestResourceStream("audit_template.html");
    if (templateStream is null) {
      Reporter.Warning(MessageSource.Verifier, ErrorRegistry.NoneId, Token.NoToken, "Embedded HTML template not found. Returning raw HTML.");
      return table;
    }
    var templateText = new StreamReader(templateStream).ReadToEnd();
    return TableRegex.Replace(templateText, table);
  }

  internal override void PostResolve(Program program) {
    var report = AuditReport.BuildReport(program);

    if (reportFileName is null && reportFormat is null) {
      foreach (var (decl, assumptions) in report.AllAssumptions()) {
        foreach (var assumption in assumptions) {
          Reporter.Warning(MessageSource.Verifier, ErrorRegistry.NoneId, assumption.tok, assumption.Warning());
        }
      }
    } else {
      var text = reportFormat switch {
        ReportFormat.HTML => GenerateHTMLReport(report),
        ReportFormat.MarkdownTable => report.RenderMarkdownTable(),
        ReportFormat.MarkdownIETF => report.RenderMarkdownIETF(),
        ReportFormat.Text => report.RenderText(),
        _ => $"Internal error: unknown format {reportFormat}"
      };
      if (reportFileName is null) {
        Console.Write(text);
      } else {
        if (compareReport) {
          try {
            var matches = File.ReadAllText(reportFileName).Equals(text);
            if (!matches) {
              Reporter.Error(MessageSource.Verifier, Token.NoToken,
                $"Given report file ({reportFileName}) does not match text generated (and saved in {reportFileName}.expect).");
              File.WriteAllText(reportFileName + ".expect", text);
            }
          } catch (IOException ioe) {
            Reporter.Error(MessageSource.Verifier, Token.NoToken, $"I/O exception trying to read {reportFileName} ({ioe.Message}).");
          }
        } else {
          File.WriteAllText(reportFileName, text);
        }
      }
    }
  }
}
