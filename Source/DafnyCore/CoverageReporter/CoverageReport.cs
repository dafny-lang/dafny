using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyCore.CoverageReporter; 

public class CoverageReport {

  private static int nextUniqueId = 0;

  // INVARIANT: CoverageSpans are sorted within each list by the position of the StartToken
  private readonly Dictionary<string, List<CoverageSpan>> labeledFiles;
  public readonly string Name; // the name to assign to this coverage report
  public readonly string Units; // the units of coverage (plural). This will be written in the coverage report table.
  private readonly int uniqueId = nextUniqueId++;
  public string UniqueId => "." + (uniqueId == 0 ? "" : (uniqueId + ".")); // to add as postfix to files

  /// <summary>
  /// Generate a new empty coverage report for a given program.
  /// Scan the program for the list of files it consists of an pre-populate the labeledFiles dictionary accordingly.
  /// </summary>
  public CoverageReport(Program program, string name, string units) {
    Name = name;
    Units = units;
    labeledFiles = new();
    HashSet<string> fileNames = new();
    FindAllFiles(program.DefaultModuleDef, fileNames);
    foreach (var fileName in fileNames) {
      labeledFiles[fileName] = new();
    }
  }

  /// <summary>
  /// Assign a coverage label to the code indicated by the <param name="span"></param> range token.
  /// If the span intersects with existing coverage information, it will be merged according to
  /// CoverageLabelExtension.Combine. 
  /// </summary>
  public void LabelCode(RangeToken span, CoverageLabel label) {
    Contract.Assert(labeledFiles.ContainsKey(span.ActualFilename));
    if (span.StartToken.CompareTo(span.EndToken) == 0) {
      return;
    }
    var labeledFile = labeledFiles[span.ActualFilename];
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
    return labeledFiles.GetOrDefault(fileName, () => new List<CoverageSpan>());
  }

  public IEnumerable<string> AllFiles() {
    return labeledFiles.Keys;
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