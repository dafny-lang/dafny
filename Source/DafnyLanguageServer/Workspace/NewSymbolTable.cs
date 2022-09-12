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
    NodePositions = new IntervalTree<Position, IHasNameToken>();
    Usages = new Dictionary<IHasNameToken, ISet<IHasNameToken>>();
    Declarations = new Dictionary<IHasNameToken, IHasNameToken>();
  }

  public NewSymbolTable(Document document, IReadOnlyList<(IHasNameToken usage, IHasNameToken declaration)> usages) {
    var safeUsages = usages.Where(k => k.declaration.NameToken.Filename != null).ToList();
    Declarations = safeUsages.ToDictionary(k => k.usage, k => k.declaration);
    Usages = safeUsages.GroupBy(u => u.declaration).ToDictionary(
      g => g.Key,
      g => (ISet<IHasNameToken>)g.Select(k => k.usage).ToHashSet());
    NodePositions = new IntervalTree<Position, IHasNameToken>();
    var symbols = safeUsages.Select(u => u.declaration).Concat<IHasNameToken>(usages.Select(u => u.usage)).
      Where(u => u.NameToken.Filename == document.Uri.ToString()).Distinct();
    foreach (var symbol in symbols) {
      var range = symbol.NameToken.GetLspRange();
      NodePositions.Add(range.Start, range.End, symbol);
    }
  }

  private IIntervalTree<Position, IHasNameToken> NodePositions { get; }
  private Dictionary<IHasNameToken, IHasNameToken> Declarations { get; }
  private Dictionary<IHasNameToken, ISet<IHasNameToken>> Usages { get; }

  public ISet<Location> GetUsages(Position position) {
    return NodePositions.Query(position).
      SelectMany(node => Usages.GetOrDefault(node, () => (ISet<IHasNameToken>)new HashSet<IHasNameToken>())).
      Select(u => new Location { Uri = u.NameToken.Filename, Range = u.NameToken.GetLspRange() }).ToHashSet();
  }

  public Location? GetDeclaration(Position position) {
    var referenceNodes = NodePositions.Query(position);
    return referenceNodes.Select(node => Declarations.GetOrDefault(node, () => (IHasNameToken?)null))
      .Where(x => x != null).Select(
        n => new Location {
          Uri = DocumentUri.From(n!.NameToken.ActualFilename),
          Range = n.NameToken.GetLspRange()
        }).FirstOrDefault();
  }
}