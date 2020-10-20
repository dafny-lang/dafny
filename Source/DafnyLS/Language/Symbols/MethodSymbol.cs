using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  public class MethodSymbol : Symbol, ILocalizableSymbol {
    public Method Declaration { get; }
    public object Node => Declaration;

    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();
    public ISet<VariableSymbol> Returns { get; } = new HashSet<VariableSymbol>();
    public IList<VariableSymbol> Locals { get; } = new List<VariableSymbol>();

    public override IEnumerable<ISymbol> Children => Parameters.Concat(Returns).Concat(Locals);

    public MethodSymbol(ISymbol? scope, Method method) : base(scope, method.Name) {
      Declaration = method;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"method {Declaration.Name}({Declaration.Ins.AsCommaSeperatedText()}) : ({Declaration.Outs.AsCommaSeperatedText()})";
    }

    public Range GetHoverRange() {
      return Declaration.tok.GetLspRange();
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
