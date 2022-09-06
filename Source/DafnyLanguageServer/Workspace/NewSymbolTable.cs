using System.Collections.Generic;
using System.Linq;
using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

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
      SelectMany(node => Usages.GetOrDefault(node, () => (ISet<INode>)new HashSet<INode>())).
      Select(u => new Location { Uri = u.NameToken.Filename, Range = u.NameToken.GetLspRange() }).ToHashSet();
  }

  public Location? GetDeclaration(Position position) {
    var referenceNodes = NodePositions.Query(position);
    return referenceNodes.Select(node => Declarations.GetOrDefault(node, () => (INode?)null))
      .Where(x => x != null).Select(
        n => new Location { 
          Uri = DocumentUri.From(n!.NameToken.ActualFilename),
          Range = n.NameToken.GetLspRange()
        }).FirstOrDefault();
  }
}