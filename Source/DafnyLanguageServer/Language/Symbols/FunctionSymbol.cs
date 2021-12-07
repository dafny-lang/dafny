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
    private IEnumerable<ISymbol> BodyAsEnumerable => Body != null ? new[] { Body } : Enumerable.Empty<ISymbol>();

    public ScopeSymbol? ByMethodBody { get; set; }
    private IEnumerable<ISymbol> ByMethodBodyAsEnumerable => ByMethodBody != null ? new[] { ByMethodBody } : Enumerable.Empty<ISymbol>();
    public override IEnumerable<ISymbol> Children => BodyAsEnumerable.Concat(ByMethodBodyAsEnumerable).Concat(Parameters);

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