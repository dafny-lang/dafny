#nullable enable
using System;
using System.IO;
using System.Collections.Generic;

namespace Microsoft.Dafny.Auditor;


/// <summary>
/// A rewriter pass that produces an AuditReport and writes it to either
/// standard output or a file, in one of several formats.
/// </summary>
public class Auditor : IRewriter {
  private readonly string? reportFileName;
  private readonly DafnyOptions.ReportFormat? reportFormat;
  private readonly bool compareReport;

  /// <summary>
  /// Construct an auditor to write to or compare to the given file in the
  /// given format.
  /// </summary>
  /// <param name="reporter">
  /// the reporter to use to emit errors and warnings
  /// </param>
  /// <param name="reportFileName">
  /// the file to write the report to (standard output if null)
  /// </param>
  /// <param name="format">
  /// the format of report to produce (derived from the file name, if null,
  /// or defaults to standard warnings if the file name is also null)
  /// </param>
  /// <param name="compareReport">
  /// if true, compare the generated report to an existing file instead
  /// of creating a file
  /// </param>
  public Auditor(ErrorReporter reporter, string? reportFileName, DafnyOptions.ReportFormat? format, bool compareReport) : base(reporter) {
    this.reportFileName = reportFileName;
    this.compareReport = compareReport;
    if (format is null) {
      if (reportFileName is null) {
        return;
      }

      if (reportFileName.EndsWith(".html")) {
        reportFormat = DafnyOptions.ReportFormat.HTML;
      } else if (reportFileName.EndsWith(".md")) {
        reportFormat = DafnyOptions.ReportFormat.MarkdownTable;
      } else if (reportFileName.EndsWith(".txt")) {
        reportFormat = DafnyOptions.ReportFormat.Text;
      } else {
        Reporter.Error(MessageSource.Resolver, Token.NoToken,
          $"Unsupported extension on report filename: {reportFileName}, using plain text. " +
               "Supported extensions are: .html, .md, .txt");
      }
    } else {
      reportFormat = format;
    }
  }

  private string GenerateHTMLReport(AuditReport report) {
    var table = report.RenderHTMLTable();
    var assembly = System.Reflection.Assembly.GetCallingAssembly();
    var templateStream = assembly.GetManifestResourceStream("audit_template.html");
    if (templateStream is null) {
      Reporter.Warning(MessageSource.Resolver, Token.NoToken, "Embedded HTML template not found. Returning raw HTML.");
      return table;
    }
    var templateText = new StreamReader(templateStream).ReadToEnd();
    return templateText.Replace("{{TABLE}}", table.ToString());
  }

  internal override void PostResolve(Program program) {
    var report = ReportBuilder.BuildReport(program);

    if (reportFileName is null && reportFormat is null) {
      foreach (var assumption in report.AllAssumptions()) {
        foreach (var warning in assumption.Warnings()) {
          Reporter.Warning(MessageSource.Resolver, assumption.decl.tok, warning);
        }
      }
    } else {
      var text = reportFormat switch {
        DafnyOptions.ReportFormat.HTML => GenerateHTMLReport(report),
        DafnyOptions.ReportFormat.MarkdownTable => report.RenderMarkdownTable(),
        DafnyOptions.ReportFormat.MarkdownIETF => report.RenderMarkdownSections(),
        DafnyOptions.ReportFormat.Text => report.RenderText(),
        _ => $"Internal error: unknown format {reportFormat}"
      };
      if (reportFileName is null) {
        Console.Write(text);
      } else {
        if (compareReport) {
          var matches = File.ReadAllText(reportFileName).Equals(text);
          if (!matches) {
            Reporter.Error(MessageSource.Resolver, Token.NoToken,
              $"Given report file ({reportFileName}) does not match text generated (and saved in {reportFileName}.expect)");
            File.WriteAllText(reportFileName + ".expect", text);
          }
        } else {
          File.WriteAllText(reportFileName, text);
        }
      }
    }
  }
}
