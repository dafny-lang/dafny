using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class MethodSymbol : MemberSymbol, ILocalizableSymbol {
    public Method Declaration { get; }
    public object Node => Declaration;

    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();
    public IList<VariableSymbol> Returns { get; } = new List<VariableSymbol>();
    public IList<ISymbol> Locals { get; } = new List<ISymbol>();

    public override IEnumerable<ISymbol> Children => Locals.Concat(Parameters).Concat(Returns);

    public MethodSymbol(ISymbol? scope, Method method) : base(scope, method) {
      Declaration = method;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {ClassPrefix}{Declaration.Name}({Declaration.Ins.AsCommaSeperatedText()}) returns ({Declaration.Outs.AsCommaSeperatedText()})";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
