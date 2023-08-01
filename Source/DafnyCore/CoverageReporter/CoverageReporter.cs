using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyCore.CoverageReporter; 

public class CoverageReporter {

  private static readonly Regex LabeledCodeRegex = new(@"\{\{LABELED_CODE\}\}\r?\n");
  private static readonly Regex PathToRootRegex = new(@"\{\{PATH_TO_ROOT\}\}");
  private static readonly Regex FileNameRegex = new(@"\{\{FILENAME\}\}");
  private static readonly Regex TitleRegexInverse = new(@"<title>([^\n]*)</title>");
  private static readonly Regex UnitsRegexInverse = new("<td class=\"ctr2\">(.*) not covered</td>");
  private static readonly Regex UriRegex = new(@"\{\{URI\}\}");
  internal static readonly Regex UriRegexInversed = new(@"<h1 hidden>([^\n]*)</h1>");
  private static readonly Regex IndexLinkRegex = new(@"\{\{INDEX_LINK\}\}");
  private static readonly Regex LinksToOtherReportsRegex = new(@"\{\{LINKS_TO_OTHER_REPORTS\}\}");
  private static readonly Regex TableHeaderRegex = new(@"\{\{TABLE_HEADER\}\}");
  private static readonly Regex TableFooterRegex = new(@"\{\{TABLE_FOOTER\}\}");
  private static readonly Regex TableBodyRegex = new(@"\{\{TABLE_BODY\}\}");
  private const string CoverageReportTemplatePath = "coverage_report_template.html";
  private const string CoverageReportIndexTemplatePath = "coverage_report_index_template.html";
  private const string CoverageReportSupportingFilesPath = ".resources";

  private readonly ErrorReporter reporter;

  public CoverageReporter(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  public void Merge(DafnyOptions options) {
    // assume only one report in directory for now
    List<CoverageReport> reports = new();
    foreach (var reportDir in options.CoverageReportsToMerge) {
      var indexFileName = Path.Combine(reportDir, "index.html");
      if (!File.Exists(indexFileName)) {
        reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
          $"Could not locate the index file for coverage report at {reportDir}");
        continue;
      }
      var index = new StreamReader(indexFileName).ReadToEnd();
      var name = TitleRegexInverse.Match(index)?.Groups?[1]?.Value ?? "";
      var units = UnitsRegexInverse.Match(index)?.Groups?[1]?.Value ?? "";
      reports.Add(new CoverageReport(reportDir, name, units));
    }
    GenerateCoverageReportFiles(reports, options.CoverageReportOutDir);
  }

  /// <summary> Serialize a single coverage report to disk </summary>
  public void GenerateCoverageReportFiles(CoverageReport report, string directory) {
    GenerateCoverageReportFiles(new List<CoverageReport> { report }, directory);
  }

  /// <summary>
  /// Create a directory with HTML files to display a set of coverage reports for the same program. The reports
  /// will have links to each other to make comparison easier
  /// </summary>
  private void GenerateCoverageReportFiles(List<CoverageReport> reports, string reportsDirectory) {
    var sessionName = DateTime.Now.ToString("yyyy-dd-M--HH-mm-ss-fff");
    var sessionDirectory = Path.Combine(reportsDirectory, sessionName);
    Directory.CreateDirectory(sessionDirectory);
    HashSet<string> allFiles = new();
    reports.ForEach(report => allFiles.UnionWith(report.AllFiles()));
    if (allFiles.Count == 0) {
      reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
        "No coverage data found in the reports.");
      return;
    }
    CopyStyleFiles(sessionDirectory);
    var prefixLength = new string(
      allFiles.First()[..allFiles.Min(s => Path.GetDirectoryName(s)?.Length ?? 0)]
        .TakeWhile((c, i) => allFiles.All(s => s[i] == c)).ToArray()).Length;
    Dictionary<string, string> sourceFileToCoverageReport = new Dictionary<string, string>();
    foreach (var fileName in allFiles) {
      var directoryForFile = Path.Combine(sessionDirectory, Path.GetDirectoryName(fileName)?[prefixLength..] ?? "");
      var pathToRoot = Path.GetRelativePath(directoryForFile, sessionDirectory);
      Directory.CreateDirectory(directoryForFile);
      for (int i = 0; i < reports.Count; i++) {
        var linksToOtherReports = GetHtmlLinksToOtherReports(reports[i], Path.GetFileName(fileName), reports);
        var reportForFile = HtmlReportForFile(reports[i], fileName, pathToRoot, linksToOtherReports);
        sourceFileToCoverageReport[fileName] = Path.Combine(directoryForFile, Path.GetFileName(fileName));
        File.WriteAllText(Path.Combine(directoryForFile, Path.GetFileName(fileName)) + $"{reports[i].UniqueId}html", reportForFile);
      }
    }

    foreach (var report in reports) {
      var linksToOtherReports = GetHtmlLinksToOtherReports(report, "index", reports);
      CreateIndexFile(report, sourceFileToCoverageReport, sessionDirectory, linksToOtherReports);
    }
  }

  private string MakeIndexFileTableRow(List<object> row) {
    var result = new StringBuilder("<tr>\n");
    foreach (var cell in row) {
      result.Append($"\t<td class=\"ctr2\">{cell}</td>\n");
    }
    result.Append("</tr>\n");
    return result.ToString();
  }

  /// <summary>
  /// Creates an index file with program-wide statistics for a particular report
  /// </summary>
  private void CreateIndexFile(CoverageReport report, Dictionary<string, string> sourceFileToCoverageReportFile, string baseDirectory, string linksToOtherReports) {
    var assembly = System.Reflection.Assembly.GetCallingAssembly();
    var templateStream = assembly.GetManifestResourceStream(CoverageReportIndexTemplatePath);
    if (templateStream is null) {
      reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
        "Embedded HTML template for coverage report index file not found. Index file will not be created.");
      return;
    }
    var coverageLabels = Enum.GetValues(typeof(CoverageLabel)).Cast<CoverageLabel>().ToList();
    List<object> header = new() { "File" };
    header.AddRange(coverageLabels.Select(label => $"{report.Units} {CoverageLabelExtension.ToString(label)}"));

    List<List<object>> body = new();
    foreach (var sourceFile in sourceFileToCoverageReportFile.Keys) {
      var relativePath = Path.GetRelativePath(baseDirectory, sourceFileToCoverageReportFile[sourceFile]);
      body.Add(new() {
        $"<a href = \"{relativePath}{report.UniqueId}html\"" +
        $"class = \"el_package\">{relativePath}</a>"
      });
      body.Last().AddRange(coverageLabels.Select(label =>
        report.CoverageSpansForFile(sourceFile).Count(span => span.Label == label)).OfType<object>());
    }

    List<object> footer = new() { "Total" };
    footer.AddRange(coverageLabels.Select(label =>
      report.AllFiles().Select(sourceFile =>
        report.CoverageSpansForFile(sourceFile).Count(span => span.Label == label)).Sum()).OfType<object>());

    var templateText = new StreamReader(templateStream).ReadToEnd();
    templateText = LinksToOtherReportsRegex.Replace(templateText, linksToOtherReports);
    templateText = FileNameRegex.Replace(templateText, report.Name);
    templateText = TableHeaderRegex.Replace(templateText, MakeIndexFileTableRow(header));
    templateText = TableFooterRegex.Replace(templateText, MakeIndexFileTableRow(footer));
    File.WriteAllText(Path.Combine(baseDirectory, $"index{report.UniqueId}html"),
      TableBodyRegex.Replace(templateText, string.Join("\n", body.Select(MakeIndexFileTableRow))));
  }

  /// <summary>
  /// Creates a set of links to be inserted in <param name="thisReport"></param> that point to corresponding
  /// report files for the same <param name="sourceFileName"></param>
  /// </summary>
  private static string GetHtmlLinksToOtherReports(CoverageReport thisReport, string sourceFileName, List<CoverageReport> allReports) {
    var result = new StringBuilder();
    foreach (var report in allReports) {
      if (report == thisReport) {
        continue;
      }
      result.Append($"<a href=\"{sourceFileName}{report.UniqueId}html\" class=\"el_report\">{report.Name}</a>");
    }
    return result.ToString();
  }


  /// <summary>
  /// Copy all .css style files from Source/DafnyCore/assets/.resources (which are packaged with the assembly)
  /// into the base directory of the coverage report being created
  /// </summary>
  /// <param name="baseDirectory"></param>
  private void CopyStyleFiles(string baseDirectory) {
    var resourceDirectory = Path.Combine(baseDirectory, ".resources");
    Directory.CreateDirectory(resourceDirectory);
    var assembly = System.Reflection.Assembly.GetCallingAssembly();
    string folderName = $"{assembly.GetName().Name}.assets.{CoverageReportSupportingFilesPath}.";
    var styleFiles = assembly
      .GetManifestResourceNames()
      .Where(r => r.StartsWith(folderName)).ToList();
    if (styleFiles.Count == 0) {
      reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken, "Embedded style files not found.");
      return;
    }
    foreach (var styleFile in styleFiles) {
      var styleFileStream = assembly.GetManifestResourceStream(styleFile);
      if (styleFileStream == null) {
        reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
          $"Embedded coverage report style file {styleFile} not found.");
        continue;
      }
      File.WriteAllText(Path.Combine(resourceDirectory, styleFile[folderName.Length..]),
        new StreamReader(styleFileStream).ReadToEnd());
    }
  }

  private string HtmlReportForFile(CoverageReport report, string pathToSourceFile, string baseDirectory, string linksToOtherReports) {
    var source = new StreamReader(pathToSourceFile).ReadToEnd();
    var lines = source.Split("\n");
    IToken lastToken = new Token(0, 0);
    var labeledCodeBuilder = new StringBuilder(source.Length);
    foreach (var span in report.CoverageSpansForFile(pathToSourceFile)) {
      AppendCodeBetweenTokens(labeledCodeBuilder, lines, lastToken, span.Span.StartToken);
      labeledCodeBuilder.Append(span.OpenHtmlTag());
      AppendCodeBetweenTokens(labeledCodeBuilder, lines, span.Span.StartToken, span.Span.EndToken);
      labeledCodeBuilder.Append(span.CloseHtmlTag());
      lastToken = span.Span.EndToken;
    }
    AppendCodeBetweenTokens(labeledCodeBuilder, lines, lastToken, null);
    var assembly = System.Reflection.Assembly.GetCallingAssembly();
    var templateStream = assembly.GetManifestResourceStream(CoverageReportTemplatePath);
    var labeledCode = labeledCodeBuilder.ToString();
    if (templateStream is null) {
      reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
        "Embedded HTML template for coverage report not found. Returning raw HTML.");
      return labeledCode;
    }
    var templateText = new StreamReader(templateStream).ReadToEnd();
    templateText = PathToRootRegex.Replace(templateText, baseDirectory);
    templateText = LinksToOtherReportsRegex.Replace(templateText, linksToOtherReports);
    templateText = IndexLinkRegex.Replace(templateText, $"index{report.UniqueId}html");
    templateText = FileNameRegex.Replace(templateText, $"{Path.GetFileName(pathToSourceFile)} ({report.Name})");
    templateText = UriRegex.Replace(templateText, pathToSourceFile);
    return LabeledCodeRegex.Replace(templateText, labeledCode);
  }

  /// <summary>
  /// Append code from <param name="lines"></param> that lies between <param name="start"></param> and
  /// <param name="end"></param> tokens to the <param name="stringBuilder"></param>
  /// </summary>
  private static void AppendCodeBetweenTokens(StringBuilder stringBuilder, string[] lines, IToken start, IToken end) {
    var currToken = new Token(start.line, start.col);
    while (currToken.line < lines.Length && (end == null || currToken.line < end.line)) {
      stringBuilder.Append(lines[currToken.line][currToken.col..] + "\n");
      currToken.line += 1;
    }
    if (end != null && currToken.line < lines.Length) {
      stringBuilder.Append(lines[currToken.line][currToken.col..end.col]);
    }
  }
}