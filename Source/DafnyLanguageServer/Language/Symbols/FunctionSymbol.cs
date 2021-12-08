using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class FunctionSymbol : MemberSymbol, ILocalizableSymbol {
    public Function Declaration { get; }
    public object Node => Declaration;

    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();

    /// <summary>
    /// Gets the body of the function
    /// </summary>
    public ScopeSymbol? Body { get; set; }
    public ScopeSymbol? ByMethodBody { get; set; }
    public List<ScopeSymbol> Ens { get; set; }
    public List<ScopeSymbol> Req { get; set; }
    public List<ScopeSymbol> Reads { get; set; }
    public List<ScopeSymbol> Decreases { get; set; }
    public override IEnumerable<ISymbol> Children =>
      AsEnumerable<ISymbol>(Body)
        .Concat(AsEnumerable(ByMethodBody))
        .Concat(Ens)
        .Concat(Req)
        .Concat(Reads)
        .Concat(Decreases)
        .Concat(Parameters);

    public FunctionSymbol(ISymbol? scope, Function function) : base(scope, function) {
      Declaration = function;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {TypePrefix}{Declaration.Name}({Declaration.Formals.AsCommaSeperatedText()}): {Declaration.ResultType.AsText()}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}