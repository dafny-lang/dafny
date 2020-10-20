using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  public class FunctionSymbol : Symbol, ILocalizableSymbol {
    public Function Declaration { get; }
    public object Node => Declaration;

    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();

    public override IEnumerable<ISymbol> Children => Parameters;

    public FunctionSymbol(ISymbol? scope, Function function) : base(scope, function.Name) {
      Declaration = function;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"function {Declaration.Name}({Declaration.Formals.AsCommaSeperatedText()}) : {Declaration.ResultType.AsText()}";
    }

    public Range GetHoverRange() {
      return Declaration.tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}