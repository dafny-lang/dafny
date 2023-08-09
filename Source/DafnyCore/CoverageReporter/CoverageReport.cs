using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyCore.CoverageReporter; 

public class CoverageReport {

  private static int nextUniqueId = 0;

  // INVARIANT: CoverageSpans are sorted within each list by the position of the StartToken
  private readonly Dictionary<string, List<CoverageSpan>> labelsByFile;
  public readonly string Name; // the name to assign to this coverage report
  public readonly string Units; // the units of coverage (plural). This will be written in the coverage report table.
  private readonly int uniqueId = nextUniqueId++;
  public string UniqueId => "." + (uniqueId == 0 ? "" : (uniqueId + ".")); // to add as postfix to files

  /// <summary>
  /// Generate a new empty coverage report for a given program.
  /// Scan the program for the list of files it consists of an pre-populate the labelsByFile dictionary accordingly.
  /// </summary>
  public CoverageReport(Program program, string name, string units) {
    Name = name;
    Units = units;
    labelsByFile = new();
    HashSet<string> fileNames = new();
    FindAllFiles(program.DefaultModuleDef, fileNames);
    foreach (var fileName in fileNames) {
      labelsByFile[fileName] = new();
    }
  }

  /// <summary>
  /// Parse a report previously serialized to disk in the <param name="reportDir"></param> directory
  /// </summary>
  public CoverageReport(string reportDir, string name, string units) {
    Name = name;
    Units = units;
    labelsByFile = new();
    foreach (string fileName in Directory.EnumerateFiles(reportDir, "*.html", SearchOption.AllDirectories)) {
      var source = new StreamReader(fileName).ReadToEnd();
      var uriMatch = CoverageReporter.UriRegexInversed.Match(source);
      if (!uriMatch.Success) {
        continue;
      }
      var uri = new Uri(uriMatch.Groups[1].Value);
      labelsByFile[uri.LocalPath] = new();
      foreach (var span in CoverageSpan.SpanRegexInverse.Matches(source).Where(match => match.Success)) {
        if (int.TryParse(span.Groups[2].Value, out var startLine) &&
            int.TryParse(span.Groups[3].Value, out var startCol) &&
            int.TryParse(span.Groups[4].Value, out var endLine) &&
            int.TryParse(span.Groups[5].Value, out var endCol)) {
          var startToken = new Token(startLine, startCol);
          startToken.Uri = uri;
          var endToken = new Token(endLine, endCol);
          startToken.Uri = uri;
          var rangeToken = new RangeToken(startToken, endToken);
          rangeToken.Uri = uri;
          LabelCode(rangeToken, CoverageLabelExtension.FromHtmlClass(span.Groups[1].Value));
        }
      }
    }
  }

  /// <summary>
  /// Assign a coverage label to the code indicated by the <param name="span"></param> range token.
  /// If the span intersects with existing coverage information, it will be merged according to
  /// CoverageLabelExtension.Combine. 
  /// </summary>
  public void LabelCode(RangeToken span, CoverageLabel label) {
    Contract.Assert(labelsByFile.ContainsKey(span.ActualFilename));
    if (span.StartToken.CompareTo(span.EndToken) == 0) {
      return;
    }
    var labeledFile = labelsByFile[span.ActualFilename];
    var coverageSpan = new CoverageSpan(span, label);
    int index = labeledFile.BinarySearch(0, labeledFile.Count, coverageSpan, null);
    if (index < 0) {
      labeledFile.Insert(~index, coverageSpan);
      return;
    }
    var overlappingSpan = labeledFile[index];
    labeledFile.RemoveAt(index);
    var combinedLabel = CoverageLabelExtension.Combine(label, overlappingSpan.Label);
    switch (overlappingSpan.Span.EndToken.CompareTo(span.EndToken)) {
      case 0:
        labeledFile.Insert(index, new CoverageSpan(span, combinedLabel));
        break;
      case > 0:
        labeledFile.Insert(index, new CoverageSpan(span, combinedLabel));
        labeledFile.Insert(index + 1, new CoverageSpan(new RangeToken(span.EndToken, overlappingSpan.Span.EndToken), overlappingSpan.Label));
        break;
      default:
        labeledFile.Insert(index, new CoverageSpan(overlappingSpan.Span, combinedLabel));
        LabelCode(new RangeToken(overlappingSpan.Span.EndToken, span.EndToken), label);
        break;
    }
  }

  public IEnumerable<CoverageSpan> CoverageSpansForFile(string fileName) {
    return labelsByFile.GetOrDefault(fileName, () => new List<CoverageSpan>());
  }

  public IEnumerable<string> AllFiles() {
    return labelsByFile.Keys;
  }

  private static void FindAllFiles(Node astNode, HashSet<string> filesFound) {
    if (astNode.StartToken.ActualFilename != null) {
      filesFound.Add(astNode.StartToken.ActualFilename);
    }
    foreach (var declaration in astNode.Children.OfType<LiteralModuleDecl>()) {
      FindAllFiles(declaration, filesFound);
    }
  }
}