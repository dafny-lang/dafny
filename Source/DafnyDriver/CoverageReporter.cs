using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Verifier;
using Microsoft.Boogie;

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
  private static readonly Regex PosRegexInverse = new("class=\"([a-z]+)\" id=\"([0-9]+):([0-9]+)\"");
  private const string CoverageReportTemplatePath = "coverage_report_template.html";
  private const string CoverageReportIndexTemplatePath = "coverage_report_index_template.html";
  private const string CoverageReportSupportingFilesPath = ".resources";

  private readonly ErrorReporter reporter;
  private readonly DafnyOptions options;
  private readonly Dictionary<(CoverageReport, string), string> paths = new();

  public string GetPath(CoverageReport report, string desiredPath) {
    return paths.GetOrCreate((report, desiredPath), () => {
      var index = 0;
      var extension = Path.GetExtension(desiredPath);
      var withoutExtension = Path.GetFileNameWithoutExtension(desiredPath);
      var actualPath = desiredPath;
      while (File.Exists(actualPath)) {
        actualPath = withoutExtension + "_" + index + extension;
        index++;
      }

      return actualPath;
    });
  }
  public CoverageReporter(DafnyOptions options) {
    reporter = options.DiagnosticsFormat switch {
      DafnyOptions.DiagnosticsFormats.PlainText => new ConsoleErrorReporter(options),
      DafnyOptions.DiagnosticsFormats.JSON => new JsonConsoleErrorReporter(options),
      _ => throw new ArgumentOutOfRangeException()
    };
    this.options = options;
  }


  public async Task SerializeVerificationCoverageReport(ProofDependencyManager depManager, Program dafnyProgram, IEnumerable<TrackedNodeComponent> usedComponents, string coverageReportDir) {
    var usedDependencies =
      usedComponents.Select(depManager.GetFullIdDependency).ToHashSet();
    var allDependencies =
      depManager
        .GetAllPotentialDependencies()
        .OrderBy(dep => dep.Range.StartToken);
    var coverageReport = new CoverageReport("Verification coverage", "Proof Dependencies", "_verification", dafnyProgram);
    foreach (var proofDependency in allDependencies) {
      if (proofDependency is FunctionDefinitionDependency) {
        continue;
      }
      coverageReport.LabelCode(proofDependency.Range,
        usedDependencies.Contains(proofDependency)
          ? CoverageLabel.FullyCovered
          : CoverageLabel.NotCovered);
    }

    await SerializeCoverageReports(coverageReport, coverageReportDir);
  }

  public async Task Merge(List<string> coverageReportsToMerge, string coverageReportOutDir) {
    List<CoverageReport> reports = new();
    var mergedReport = new CoverageReport("Combined Coverage Report", "Locations", "_combined", null);
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
          continue;
        }
        var suffix = indexFileMatch.Groups[1].Value;
        var index = await new StreamReader(pathToIndexFile).ReadToEndAsync();
        var name = TitleRegexInverse.Match(index)?.Groups?[1]?.Value ?? "";
        var units = UnitsRegexInverse.Match(index)?.Groups?[1]?.Value ?? "";
        reports.Add(ParseCoverageReport(reportDir, $"{name} ({Path.GetFileName(reportDir)})", units, suffix));
      }
    }

    var onlyLabel = options.Get(CoverageReportCommand.OnlyLabelOption);
    foreach (var report in reports) {
      foreach (var fileName in report.AllFiles()) {
        foreach (var span in report.CoverageSpansForFile(fileName)) {
          mergedReport.RegisterFile(span.Span.Uri);
          if ((onlyLabel ?? span.Label) == span.Label) {
            mergedReport.LabelCode(span.Span, span.Label);
          }
        }
      }
    }
    reports.Add(mergedReport);
    await SerializeCoverageReports(reports, coverageReportOutDir);
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
      lastEndToken.Uri = uri;
      var lastLabel = CoverageLabel.NotApplicable;
      report.RegisterFile(uri);
      foreach (var span in PosRegexInverse.Matches(source).Where(match => match.Success)) {
        if (int.TryParse(span.Groups[2].Value, out var line) &&
            int.TryParse(span.Groups[3].Value, out var col)) {
          var nextToken = new Token(line, col);
          nextToken.Uri = uri;
          var precedingToken = new Token(line, col - 1);
          precedingToken.Uri = uri;
          var rangeToken = new SourceOrigin(lastEndToken, precedingToken);
          rangeToken.Uri = uri;
          report.LabelCode(rangeToken, lastLabel);
          lastLabel = FromHtmlClass(span.Groups[1].Value);
          lastEndToken = nextToken;
        }
      }

      var lastToken = new Token(source.Count(c => c == '\n') + 2, 0);
      lastToken.Uri = uri;
      var lastRangeToken = new SourceOrigin(lastEndToken, lastToken);
      report.LabelCode(lastRangeToken, lastLabel);
    }
    return report;
  }

  /// <summary> Serialize a single coverage report to disk </summary>
  public Task SerializeCoverageReports(CoverageReport report, string directory) {
    return SerializeCoverageReports(new List<CoverageReport> { report }, directory);
  }

  /// <summary>
  /// Create a directory with HTML files to display a set of coverage reports for the same program. The reports
  /// will have links to each other to make comparison easier
  /// </summary>
  private async Task SerializeCoverageReports(List<CoverageReport> reports, string reportsDirectory) {
    var sessionDirectory = reportsDirectory;
    if (!options.Get(CommonOptionBag.NoTimeStampForCoverageReport)) {
      var sessionName = DateTime.Now.ToString("yyyy-dd-M--HH-mm-ss");
      sessionDirectory = Path.Combine(reportsDirectory, sessionName);
    }
    Directory.CreateDirectory(sessionDirectory);
    HashSet<Uri> allUris = new();
    reports.ForEach(report => allUris.UnionWith(report.AllFiles()));
    if (allUris.Count == 0) {
      reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
        "No coverage data found in the reports.");
      return;
    }
    CopyStyleFiles(sessionDirectory);
    // TODO: Handle arbitrary Uris better
    var allFiles = allUris.Select(uri => uri.ToString());
    var prefixLength = new string(
      allFiles.First()[..allFiles.Min(s => Path.GetDirectoryName(s)?.Length ?? 0)]
        .TakeWhile((c, i) => allFiles.All(s => s[i] == c)).ToArray()).Length;
    var sourceFileToCoverageReport = new Dictionary<Uri, string>();
    foreach (var uri in allUris) {
      // TODO: Handle arbitrary Uris better
      var fileName = uri.ToString();
      var directoryForFile = Path.Combine(sessionDirectory, Path.GetDirectoryName(fileName)?[prefixLength..].TrimStart('/') ?? "");
      sourceFileToCoverageReport[uri] = Path.Combine(directoryForFile, Path.GetFileName(fileName));
      var pathToRoot = Path.GetRelativePath(directoryForFile, sessionDirectory);
      Directory.CreateDirectory(directoryForFile);
      foreach (var report in reports) {
        var linksToOtherReports = GetHtmlLinksToOtherReports(report, fileName, reports);
        var reportForFile = await HtmlReportForFile(report, uri, pathToRoot, linksToOtherReports);
        var desiredPath = Path.Combine(directoryForFile, Path.GetFileName(fileName)) + $"{report.Suffix}.html";
        await File.WriteAllTextAsync(GetPath(report, desiredPath), reportForFile);
      }
    }

    foreach (var report in reports) {
      var linksToOtherReports = GetHtmlLinksToOtherReports(report, Path.Combine(sessionDirectory, "index"), reports);
      CreateIndexFile(report, sourceFileToCoverageReport, sessionDirectory, linksToOtherReports);
    }
  }

  private string MakeIndexFileTableRow(List<object> row) {
    var result = new StringBuilder("<tr>\n");
    foreach (var cell in row.Take(2)) {
      result.Append($"\t<td class=\"name\">{cell}</td>\n");
    }
    foreach (var cell in row.Skip(2)) {
      result.Append($"\t<td class=\"ctr2\">{cell}</td>\n");
    }
    result.Append("</tr>\n");
    return result.ToString();
  }

  /// <summary>
  /// Creates an index file with program-wide statistics for a particular report
  /// </summary>
  private void CreateIndexFile(CoverageReport report, Dictionary<Uri, string> sourceFileToCoverageReportFile, string baseDirectory, string linksToOtherReports) {
    var assembly = System.Reflection.Assembly.GetCallingAssembly();
    var templateStream = assembly.GetManifestResourceStream(CoverageReportIndexTemplatePath);
    if (templateStream is null) {
      reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
        "Embedded HTML template for coverage report index file not found. Index file will not be created.");
      return;
    }
    var coverageLabels = Enum.GetValues(typeof(CoverageLabel)).Cast<CoverageLabel>().ToList();
    List<object> header = new() { "File", "Module" };
    header.AddRange(coverageLabels
      .Where(label => label != CoverageLabel.None && label != CoverageLabel.NotApplicable)
      .Select(label => $"{report.Units} {CoverageLabelExtension.ToString(label)}"));

    List<List<object>> body = new();
    foreach (var sourceFile in sourceFileToCoverageReportFile.Keys) {
      var desiredPath = sourceFileToCoverageReportFile[sourceFile] + $"{report.Suffix}.html";
      var relativePath = Path.GetRelativePath(baseDirectory, GetPath(report, desiredPath));
      var linkName = Path.GetRelativePath(baseDirectory, sourceFileToCoverageReportFile[sourceFile]);

      body.Add(new() {
        $"<a href = \"{relativePath}\"" +
        $"class = \"el_package\">{linkName}</a>",
        "All modules"
      });

      body.Last().AddRange(coverageLabels
        .Where(label => label != CoverageLabel.None && label != CoverageLabel.NotApplicable)
        .Select(label => report.CoverageSpansForFile(sourceFile)
                               .Count(span => span.Label == label)).OfType<object>());

      foreach (var module in report.ModulesInFile(sourceFile).OrderBy(m => m.FullName)) {
        body.Add(new() {
          "",
          module.FullName
        });

        var moduleRange = module.Origin.ToDafnyRange();
        body.Last().AddRange(coverageLabels
          .Where(label => label != CoverageLabel.None && label != CoverageLabel.NotApplicable)
          .Select(label => report.CoverageSpansForFile(sourceFile)
                                 // span.Span.Intersects(module.RangeToken) would be cleaner,
                                 // but unfortunately coverage span tokens don't currently always
                                 // have Token.pos set correctly. :(
                                 .Where(span => moduleRange.Contains(span.Span.ToDafnyRange().Start))
                                 .Count(span => span.Label == label)).OfType<object>());
      }
    }

    List<object> footer = new() { "Total", "" };
    footer.AddRange(coverageLabels
      .Where(label => label != CoverageLabel.None && label != CoverageLabel.NotApplicable)
      .Select(label => report.AllFiles().Select(sourceFile =>
        report.CoverageSpansForFile(sourceFile).Count(span => span.Label == label)).Sum()).OfType<object>());

    var templateText = new StreamReader(templateStream).ReadToEnd();
    templateText = LinksToOtherReportsRegex.Replace(templateText, linksToOtherReports);
    templateText = FileNameRegex.Replace(templateText, report.Name);
    templateText = TableHeaderRegex.Replace(templateText, MakeIndexFileTableRow(header));
    templateText = TableFooterRegex.Replace(templateText, MakeIndexFileTableRow(footer));
    templateText = TableBodyRegex.Replace(templateText, string.Join("\n", body.Select(MakeIndexFileTableRow)));
    File.WriteAllText(GetPath(report, Path.Combine(baseDirectory, $"index{report.Suffix}.html")), templateText);
  }

  /// <summary>
  /// Creates a set of links to be inserted in <param name="thisReport"></param> that point to corresponding
  /// report files for the same <param name="reportAgnosticPath"></param>
  /// </summary>
  private string GetHtmlLinksToOtherReports(CoverageReport thisReport, string reportAgnosticPath, List<CoverageReport> allReports) {
    var result = new StringBuilder();
    foreach (var report in allReports) {
      if (report == thisReport) {
        continue;
      }
      result.Append($"<a href=\"{Path.GetFileName(GetPath(thisReport, reportAgnosticPath + $"{report.Suffix}.html"))}\" class=\"el_report\">{report.Name}</a>");
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

  private async Task<string> HtmlReportForFile(CoverageReport report, Uri uri, string baseDirectory, string linksToOtherReports) {
    var files = await DafnyFile.CreateAndValidate(OnDiskFileSystem.Instance,
        new ConsoleErrorReporter(options), options, uri, Token.Cli).ToListAsync();
    var dafnyFile = files[0];
    var source = await dafnyFile.GetContent().Reader.ReadToEndAsync();
    var lines = source.Split(new[] { Environment.NewLine }, StringSplitOptions.None);
    var characterLabels = new CoverageLabel[lines.Length][];
    for (int i = 0; i < lines.Length; i++) {
      characterLabels[i] = new CoverageLabel[lines[i].Length];
      Array.Fill(characterLabels[i], CoverageLabel.None);
    }
    var labeledCodeBuilder = new StringBuilder(source.Length);
    foreach (var span in report.CoverageSpansForFile(uri)) {
      var line = span.Span.StartToken.line - 1;
      var column = span.Span.StartToken.col - 1;
      while (true) {
        if (characterLabels[line].Length <= column) {
          do { line++; }
          while (line < characterLabels.Length && characterLabels[line].Length == 0);
          column = 0;
          if (characterLabels.Length == line) {
            break;
          }
        }
        if (line > span.Span.EndToken.line - 1 || (line == span.Span.EndToken.line - 1 && column > span.Span.EndToken.col - 1)) {
          break;
        }
        characterLabels[line][column] = CoverageLabelExtension.Combine(characterLabels[line][column], span.Label);
        column++;
      }
    }

    var lastLabel = CoverageLabel.NotApplicable;
    labeledCodeBuilder.Append(OpenHtmlTag(1, 1, CoverageLabel.NotApplicable));
    for (var line = 0; line < lines.Length; line++) {
      for (var col = 0; col < lines[line].Length; col++) {
        var thisLabel = characterLabels[line][col] == CoverageLabel.None ? CoverageLabel.NotApplicable : characterLabels[line][col];
        if (thisLabel != lastLabel) {
          labeledCodeBuilder.Append(CloseHtmlTag());
          labeledCodeBuilder.Append(OpenHtmlTag(line + 1, col + 1, thisLabel));
        }
        labeledCodeBuilder.Append(lines[line][col]);
        lastLabel = thisLabel;
      }
      labeledCodeBuilder.Append(Environment.NewLine);
    }
    labeledCodeBuilder.Append(CloseHtmlTag());

    var assembly = System.Reflection.Assembly.GetAssembly(typeof(CoverageReporter))!;
    var templateStream = assembly.GetManifestResourceStream(CoverageReportTemplatePath);
    var labeledCode = labeledCodeBuilder.ToString();
    if (templateStream is null) {
      reporter.Warning(MessageSource.Documentation, ErrorRegistry.NoneId, Token.NoToken,
        "Embedded HTML template for coverage report not found. Returning raw HTML.");
      return labeledCode;
    }
    var templateText = await new StreamReader(templateStream).ReadToEndAsync();
    templateText = PathToRootRegex.Replace(templateText, baseDirectory);
    templateText = LinksToOtherReportsRegex.Replace(templateText, linksToOtherReports);
    templateText = IndexLinkRegex.Replace(templateText, Path.GetFileName(GetPath(report, Path.Combine(baseDirectory, $"index{report.Suffix}.html"))));
    templateText = FileNameRegex.Replace(templateText, $"{Path.GetFileName(uri.LocalPath)}, {report.Name}");
    templateText = UriRegex.Replace(templateText, uri.ToString());
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
      CoverageLabel.NotApplicable => "na",
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

  private string OpenHtmlTag(int line, int col, CoverageLabel label) {
    var id = $"id=\"{line}:{col}\"";
    var classLabel = ToHtmlClass(label);
    return $"<span class=\"{classLabel}\" {id}>";
  }

  private string CloseHtmlTag() {
    return "</span>";
  }
}