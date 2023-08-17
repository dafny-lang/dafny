#nullable disable
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny; 

public class CoverageReport {

  private static int nextUniqueId = 0;

  // INVARIANT: CoverageSpans are sorted within each list by the position of the StartToken
  private readonly Dictionary<string, List<CoverageSpan>> labelsByFile;
  public readonly string Name; // the name to assign to this coverage report
  public readonly string Units; // the units of coverage (plural). This will be written in the coverage report table.
  private readonly string suffix; // user-provided suffix to add to filenames that are part of this report
  private readonly int uniqueId = Interlocked.Increment(ref nextUniqueId);
  public string UniqueSuffix => suffix + (uniqueId == 1 ? "" : ("_" + uniqueId));


  /// <summary>
  /// Generate a new empty coverage report for a given program.
  /// If not null, scan the <param name="program"></param> for the list of files it consists of and populate the
  /// labelsByFile dictionary. <param name="name"></param> is the title of the coverage report displayed in HTML files,
  /// <param name="units"></param> are the units of coverage this report uses (to be displayed in the index HTML file),
  /// <param name="suffix"></param> is the suffix to add to files that are part of this coverage report. 
  /// </summary>
  public CoverageReport(string name, string units, string suffix, Program program) {
    Name = name;
    Units = units;
    this.suffix = suffix;
    labelsByFile = new();
    if (program != null) {
      RegisterFiles(program);
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

  public void RegisterFiles(Program program) {
    RegisterFiles(program.DefaultModuleDef);
  }

  public void RegisterFile(Uri uri) {
    labelsByFile[uri.LocalPath] = new List<CoverageSpan>();
  }

  private void RegisterFiles(Node astNode) {
    if (astNode.StartToken.ActualFilename != null) {
      labelsByFile[astNode.StartToken.ActualFilename] = new();
    }
    foreach (var declaration in astNode.Children.OfType<LiteralModuleDecl>()) {
      RegisterFiles(declaration);
    }
  }
}