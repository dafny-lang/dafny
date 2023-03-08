using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class MethodSymbol : MemberSymbol, ILocalizableSymbol {
    /// <summary>
    /// Gets the method node representing the declaration of this symbol.
    /// </summary>
    public Method Declaration { get; }
    public object Node => Declaration;

    /// <summary>
    /// Gets the method parameters.
    /// </summary>
    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();

    /// <summary>
    /// Gets the return values.
    /// </summary>
    public IList<VariableSymbol> Returns { get; } = new List<VariableSymbol>();

    /// <summary>
    /// Gets the block
    /// </summary>
    public ScopeSymbol? Block { get; set; }
    public List<ScopeSymbol> Ensures { get; } = new();
    public List<ScopeSymbol> Requires { get; } = new();
    public List<ScopeSymbol> Modifies { get; } = new();
    public List<ScopeSymbol> Decreases { get; } = new();

    public override IEnumerable<ISymbol> Children =>
      Block.AsEnumerable<ISymbol>()
        .Concat(Parameters)
        .Concat(Returns)
        .Concat(Ensures)
        .Concat(Requires)
        .Concat(Modifies)
        .Concat(Decreases);

    public MethodSymbol(ISymbol? scope, Method method) : base(scope, method) {
      Declaration = method;
    }

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      var signatureWithoutReturn = $"{Declaration.WhatKind} {TypePrefix}{Declaration.Name}({Declaration.Ins.AsCommaSeperatedText()})";
      if (Declaration.Outs.Count == 0) {
        return signatureWithoutReturn;
      }
      return $"{signatureWithoutReturn} returns ({Declaration.Outs.AsCommaSeperatedText()})";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
