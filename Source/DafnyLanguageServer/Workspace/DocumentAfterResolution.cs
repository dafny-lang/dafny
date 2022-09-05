using System;
using System.Collections.Generic;
using System.Linq;
using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class DocumentAfterResolution : DocumentAfterParsing {
  public DocumentAfterResolution(DocumentTextBuffer textDocumentItem,
    Dafny.Program program,
    IReadOnlyList<Diagnostic> parseAndResolutionDiagnostics,
    NewSymbolTable? newSymbolTable,
    SymbolTable symbolTable,
    IReadOnlyList<Diagnostic> ghostDiagnostics) :
    base(textDocumentItem, program, ArraySegment<Diagnostic>.Empty) {
    ParseAndResolutionDiagnostics = parseAndResolutionDiagnostics;
    NewSymbolTable = newSymbolTable;
    SymbolTable = symbolTable;
    GhostDiagnostics = ghostDiagnostics;
  }

  public IReadOnlyList<Diagnostic> ParseAndResolutionDiagnostics { get; }
  public NewSymbolTable? NewSymbolTable { get; }
  public SymbolTable SymbolTable { get; }
  public IReadOnlyList<Diagnostic> GhostDiagnostics { get; }

  public override IEnumerable<Diagnostic> Diagnostics => ParseAndResolutionDiagnostics;

  public override IdeState ToIdeState(IdeState previousState) {
    return previousState with {
      TextDocumentItem = TextDocumentItem,
      ImplementationsWereUpdated = false,
      ResolutionDiagnostics = ParseAndResolutionDiagnostics,
      NewSymbolTable = NewSymbolTable ?? previousState.NewSymbolTable,
      SymbolTable = SymbolTable.Resolved ? SymbolTable : previousState.SymbolTable,
      GhostDiagnostics = GhostDiagnostics
    };
  }
}

public class NewSymbolTable {

  public static NewSymbolTable Empty() {
    return new NewSymbolTable();
  }

  private NewSymbolTable() {
    NodePositions = new IntervalTree<Position, INode>();
    Usages = new Dictionary<INode, ISet<INode>>();
    Declarations = new Dictionary<INode, INode>();
  }
  
  public NewSymbolTable(Document document, IReadOnlyList<(INode usage, INode declaration)> usages) {
    var safeUsages = usages.Where(k => k.declaration.NameToken.Filename != null).ToList();
    Declarations = safeUsages.ToDictionary(k => k.usage, k => k.declaration);
    Usages = safeUsages.GroupBy(u => u.declaration).ToDictionary(
      g => g.Key, 
      g => (ISet<INode>)g.Select(k => k.usage).ToHashSet());
    NodePositions = new IntervalTree<Position, INode>();
    var symbols = safeUsages.Select(u => u.declaration).Concat(usages.Select(u => u.usage)).
      Where(u => u.NameToken.Filename == document.Uri.ToString()).Distinct();
    foreach (var symbol in symbols) {
      var range = symbol.NameToken.GetLspRange();
      NodePositions.Add(range.Start, range.End, symbol);
    }
  }
  
  private IIntervalTree<Position, INode> NodePositions { get; }
  private Dictionary<INode, INode> Declarations { get; }
  private Dictionary<INode, ISet<INode>> Usages { get; }

  public ISet<Location> GetUsages(Position position) {
    return NodePositions.Query(position).
      SelectMany(node => Usages.GetOrDefault(node, () => new HashSet<INode>())).
      Select(u => new Location { Uri = u.NameToken.Filename, Range = u.NameToken.GetLspRange() }).ToHashSet();
  }

  public Location? GetDeclaration(Position position) {
    return NodePositions.Query(position).Select(node => Declarations.GetOrDefault<INode, INode?>(node, () => null))
      .Where(x => x != null).Select(
        n => new Location { 
          Uri = DocumentUri.From(n!.NameToken.Filename),
          Range = n.NameToken.GetLspRange()
        }).FirstOrDefault();
  }
}

