#nullable disable
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class CoverageReport {

  private readonly Dictionary<Uri, List<CoverageSpan>> labelsByFile;
  private readonly Dictionary<Uri, HashSet<ModuleDefinition>> modulesByFile;
  public readonly string Name; // the name to assign to this coverage report
  public readonly string Units; // the units of coverage (plural). This will be written in the coverage report table.

  public string Suffix { get; }

  public string ActualPath { get; private set; }

  public string ActualIndexPath { get; private set; }

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
    this.Suffix = suffix;
    labelsByFile = new();
    modulesByFile = new();
    if (program != null) {
      RegisterFiles(program);
    }
  }

  /// <summary>
  /// Assign a coverage label to the code indicated by the <param name="span"></param> range token.
  /// </summary>
  public void LabelCode(IOrigin span, CoverageLabel label) {
    Contract.Assert(labelsByFile.ContainsKey(span.Uri));
    var labeledFile = labelsByFile[span.Uri];
    var coverageSpan = new CoverageSpan(span, label);
    labeledFile.Add(coverageSpan);
  }

  public IEnumerable<CoverageSpan> CoverageSpansForFile(Uri uri) {
    return labelsByFile.GetOrDefault(uri, () => new List<CoverageSpan>());
  }

  public IEnumerable<ModuleDefinition> ModulesInFile(Uri uri) {
    return modulesByFile.GetOrDefault(uri, () => new HashSet<ModuleDefinition>());
  }

  public IEnumerable<Uri> AllFiles() {
    return labelsByFile.Keys;
  }

  public void RegisterFiles(Program program) {
    RegisterFiles(program.DefaultModuleDef);
  }

  public void RegisterFile(Uri uri) {
    if (!labelsByFile.ContainsKey(uri)) {
      labelsByFile[uri] = new List<CoverageSpan>();
    }
  }

  private void RegisterFiles(Node astNode) {
    if (astNode.StartToken.ActualFilename != null) {
      labelsByFile.GetOrCreate(astNode.StartToken.Uri, () => new List<CoverageSpan>());
    }

    if (astNode is LiteralModuleDecl moduleDecl) {
      if (astNode.StartToken.ActualFilename != null) {
        modulesByFile.GetOrCreate(astNode.StartToken.Uri, () => new HashSet<ModuleDefinition>()).Add(moduleDecl.ModuleDef);
      }

      RegisterFiles(moduleDecl.ModuleDef);
    }

    foreach (var declaration in astNode.Children.OfType<LiteralModuleDecl>()) {
      RegisterFiles(declaration);
    }
    foreach (var declaration in astNode.Children.OfType<Declaration>()) {
      RegisterFiles(declaration);
    }
  }
}