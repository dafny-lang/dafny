using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class FunctionSymbol : MemberSymbol, ILocalizableSymbol {
    public Function Declaration { get; }
    public INode Node => Declaration;

    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();

    /// <summary>
    /// Gets the body of the function
    /// </summary>
    public ScopeSymbol? Body { get; set; }
    public ScopeSymbol? ByMethodBody { get; set; }
    public List<ScopeSymbol> Ensures { get; } = [];
    public List<ScopeSymbol> Requires { get; } = [];
    public List<ScopeSymbol> Reads { get; } = [];
    public List<ScopeSymbol> Decreases { get; } = [];
    public override IEnumerable<ILegacySymbol> Children =>
      Body.AsEnumerable<ILegacySymbol>()
        .Concat(ByMethodBody.AsEnumerable())
        .Concat(Ensures)
        .Concat(Requires)
        .Concat(Reads)
        .Concat(Decreases)
        .Concat(Parameters);

    public FunctionSymbol(ILegacySymbol? scope, Function function) : base(scope, function) {
      Declaration = function;
    }

    public string GetDetailText(DafnyOptions options, CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {TypePrefix}{Declaration.Name}({Declaration.Ins.AsCommaSeperatedText()}): {Declaration.ResultType.AsText(options)}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}