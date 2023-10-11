using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Microsoft.Extensions.Primitives;

namespace Microsoft.Dafny; 

public class CoverageReporter {

  private static readonly Regex LabeledCodeRegex = new(@"\{\{LABELED_CODE\}\}\r?\n");
  private static readonly Regex PathToRootRegex = new(@"\{\{PATH_TO_ROOT\}\}");
  private static readonly Regex FileNameRegex = new(@"\{\{FILENAME\}\}");
  private static readonly Regex TitleRegexInverse = new(@"<title>([^\n]*)</title>");
  private static readonly Regex UnitsRegexInverse = new("<td class=\"ctr2\">(.*) not covered</td>");
  private static readonly Regex UriRegex = new(@"\{\{URI\}\}");
  private static readonly Regex UriRegexInversed = new(@"<h1 hidden>([^\n]*)</h1>");
  private static readonly Regex IndexLinkRegex = new(@"\{\{INDEX_LINK\}\}");
  private static readonly Regex LinksToOtherReportsRegex = new(@"\{\{LINKS_TO_OTHER_REPORTS\}\}");
  private static readonly Regex TableHeaderRegex = new(@"\{\{TABLE_HEADER\}\}");
  private static readonly Regex TableFooterRegex = new(@"\{\{TABLE_FOOTER\}\}");
  private static readonly Regex TableBodyRegex = new(@"\{\{TABLE_BODY\}\}");
  private static readonly Regex IndexFileNameRegex = new(@"index(.*)\.html");
  private static readonly Regex PosRegexInverse = new("class=\"([a-z]+)\" id=\"pos([0-9]+)\">");
  private const string CoverageReportTemplatePath = "coverage_report_template.html";
  private const string CoverageReportIndexTemplatePath = "coverage_report_index_template.html";
  private const string CoverageReportSupportingFilesPath = ".resources";

  private readonly ErrorReporter reporter;
  private readonly DafnyOptions options;

  public CoverageReporter(DafnyOptions options) {
    reporter = options.DiagnosticsFormat switch {
      DafnyOptions.DiagnosticsFormats.PlainText => new ConsoleErrorReporter(options),
      DafnyOptions.DiagnosticsFormats.JSON => new JsonConsoleErrorReporter(options),
      _ => throw new ArgumentOutOfRangeException()
    };
    this.options = options;
  }


  public void SerializeVerificationCoverageReport(ProofDependencyManager depManager, Program dafnyProgram, IEnumerable<TrackedNodeComponent> usedComponents, string coverageReportDir) {
    var usedDependencies =
      usedComponents.Select(depManager.GetFullIdDependency).ToHashSet();
    var allDependencies =
      depManager
        .GetAllPotentialDependencies()
        .OrderBy(dep => dep.Range.StartToken);
    var coverageReport = new CoverageReport("Verification coverage", "Lines", "_verification", dafnyProgram);
    foreach (var dep in allDependencies) {
      if (dep is FunctionDefinitionDependency) {
        continue;
      }
      coverageReport.LabelCode(dep.Range,
        usedDependencies.Contains(dep)
          ? CoverageLabel.FullyCovered
          : CoverageLabel.NotCovered);
    }

    SerializeCoverageReports(coverageReport, coverageReportDir);
  }

  public void Merge(List<string> coverageReportsToMerge, string coverageReportOutDir) {
    // assume only one report in directory for now
    List<CoverageReport> reports = new();
    foreach (var reportDir in coverageReportsToMerge) {
      if (!Directory.Exists(reportDir)) {
        reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
          $"Could not locate the directory {reportDir} with a coverage report");
        continue;
      }
      foreach (var pathToIndexFile in Directory.EnumerateFiles(reportDir, "*.html", SearchOption.TopDirectoryOnly)) {
        var indexFileName = Path.GetFileName(pathToIndexFile);
        var indexFileMatch = IndexFileNameRegex.Match(indexFileName);
        if (!indexFileMatch.Success) {
          reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
            $"Directory {reportDir} contains file {indexFileName} which is not part of a coverage report");
        }
        var suffix = indexFileMatch.Groups[1].Value;
        var index = new StreamReader(pathToIndexFile).ReadToEnd();
        var name = TitleRegexInverse.Match(index)?.Groups?[1]?.Value ?? "";
        var units = UnitsRegexInverse.Match(index)?.Groups?[1]?.Value ?? "";
        reports.Add(ParseCoverageReport(reportDir, $"{name} ({Path.GetFileName(reportDir)})", units, suffix));
      }
    }
    SerializeCoverageReports(reports, coverageReportOutDir);
  }

  /// <summary>
  /// Parse a report previously serialized to disk in the <param name="reportDir"></param> directory.
  /// <param name="name"></param> is the title of the coverage report displayed in HTML files,
  /// <param name="units"></param> are the units of coverage this report uses (to be displayed in the index HTML file),
  /// <param name="suffix"></param> is the suffix to add to files that are part of this coverage report. 
  /// </summary>
  private static CoverageReport ParseCoverageReport(string reportDir, string name, string units, string suffix) {
    var report = new CoverageReport(name: name, units: units, suffix: suffix, null);
    foreach (string fileName in Directory.EnumerateFiles(reportDir, $"*{suffix}.html", SearchOption.AllDirectories)) {
      var source = new StreamReader(fileName).ReadToEnd();
      var uriMatch = UriRegexInversed.Match(source);
      if (!uriMatch.Success) {
        continue;
      }
      var uri = new Uri(uriMatch.Groups[1].Value);
      var lastEndToken = new Token(1, 1);
      report.RegisterFile(uri);
      foreach (var span in PosRegexInverse.Matches(source).Where(match => match.Success)) {
        if (int.TryParse(span.Groups[2].Value, out var pos)) {
          var startToken = new Token(1, 1);
          startToken.Uri = uri;
          startToken.pos = pos;
          lastEndToken.pos = pos;
          var endToken = new Token(1, 1);
          endToken.Uri = uri;
          lastEndToken = endToken;
          var rangeToken = new RangeToken(startToken, endToken);
          rangeToken.Uri = uri;
          report.LabelCode(rangeToken, FromHtmlClass(span.Groups[1].Value));
        }
      }
    }
    return report;
  }

  /// <summary> Serialize a single coverage report to disk </summary>
  public void SerializeCoverageReports(CoverageReport report, string directory) {
    SerializeCoverageReports(new List<CoverageReport> { report }, directory);
  }

  /// <summary>
  /// Create a directory with HTML files to display a set of coverage reports for the same program. The reports
  /// will have links to each other to make comparison easier
  /// </summary>
  private void SerializeCoverageReports(List<CoverageReport> reports, string reportsDirectory) {
    var sessionName = DateTime.Now.ToString("yyyy-dd-M--HH-mm-ss");
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
      var directoryForFile = Path.Combine(sessionDirectory, Path.GetDirectoryName(fileName)?[prefixLength..].TrimStart('/') ?? "");
      var pathToRoot = Path.GetRelativePath(directoryForFile, sessionDirectory);
      Directory.CreateDirectory(directoryForFile);
      for (int i = 0; i < reports.Count; i++) {
        var linksToOtherReports = GetHtmlLinksToOtherReports(reports[i], Path.GetFileName(fileName), reports);
        var reportForFile = HtmlReportForFile(reports[i], fileName, pathToRoot, linksToOtherReports);
        sourceFileToCoverageReport[fileName] = Path.Combine(directoryForFile, Path.GetFileName(fileName));
        File.WriteAllText(Path.Combine(directoryForFile, Path.GetFileName(fileName)) + $"{reports[i].UniqueSuffix}.html", reportForFile);
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
        $"<a href = \"{relativePath}{report.UniqueSuffix}.html\"" +
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
    File.WriteAllText(Path.Combine(baseDirectory, $"index{report.UniqueSuffix}.html"),
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
      result.Append($"<a href=\"{sourceFileName}{report.UniqueSuffix}.html\" class=\"el_report\">{report.Name}</a>");
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
    var characterLabels = new CoverageLabel[source.Length];
    Array.Fill(characterLabels, CoverageLabel.None);
    IToken lastToken = new Token(1, 1);
    var labeledCodeBuilder = new StringBuilder(source.Length);
    foreach (var span in report.CoverageSpansForFile(pathToSourceFile)) {
      for (var pos = span.Span.StartToken.pos; pos <= span.Span.EndToken.pos; pos++) {
        characterLabels[pos] = CoverageLabelExtension.Combine(characterLabels[pos], span.Label);
      }
    }

    CoverageLabel lastLabel = CoverageLabel.None;
    labeledCodeBuilder.Append(OpenHtmlTag(0, CoverageLabel.None));
    for (var pos = 0; pos < source.Length; pos++) {
      var thisLabel = characterLabels[pos];
      if (thisLabel != lastLabel) {
        labeledCodeBuilder.Append(CloseHtmlTag());
        labeledCodeBuilder.Append(OpenHtmlTag(pos, thisLabel));
      }

      labeledCodeBuilder.Append(source[pos]);

      lastLabel = thisLabel;
    }
    labeledCodeBuilder.Append(CloseHtmlTag());

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
    templateText = IndexLinkRegex.Replace(templateText, $"index{report.UniqueSuffix}.html");
    templateText = FileNameRegex.Replace(templateText, $"{Path.GetFileName(pathToSourceFile)}, {report.Name}");
    templateText = UriRegex.Replace(templateText, pathToSourceFile);
    return LabeledCodeRegex.Replace(templateText, labeledCode);
  }

  /// <summary>
  /// Return HTML class used to highlight lines in different colors depending on the coverage.
  /// Look at assets/.resources/coverage.css for the styles corresponding to these classes
  /// </summary>
  private static string ToHtmlClass(CoverageLabel label) {
    return label switch {
      CoverageLabel.FullyCovered => "fc",
      CoverageLabel.NotCovered => "nc",
      CoverageLabel.PartiallyCovered => "pc",
      CoverageLabel.None => "none",
      _ => ""
    };
  }

  /// <summary> Inverse of ToHtmlClass </summary>
  private static CoverageLabel FromHtmlClass(string htmlClass) {
    foreach (var label in Enum.GetValues(typeof(CoverageLabel)).Cast<CoverageLabel>()) {
      if (ToHtmlClass(label) == htmlClass) {
        return label;
      }
    }
    return CoverageLabel.NotCovered; // this is a fallback in case the HTML has invalid classes
  }

  private string OpenHtmlTag(int pos, CoverageLabel label) {
    var id = $"id=\"pos{pos}\"";
    var classLabel = ToHtmlClass(label);
    return $"<span class=\"{classLabel}\" {id}>";
  }

  private string CloseHtmlTag() {
    return "</span>";
  }
}