using Microsoft.Dafny;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class MethodSymbol : Symbol, ILocalizableSymbol {
    public Method Declaration { get; }
    public object Node => Declaration;

    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();
    public ISet<VariableSymbol> Returns { get; } = new HashSet<VariableSymbol>();
    public IList<VariableSymbol> Locals { get; } = new List<VariableSymbol>();

    // TODO The resolution priority is currently given by the order of the children.
    // TODO We have to properly align the locals to their enclosing block to correctly handle shadowing.
    public override IEnumerable<ISymbol> Children => Locals.Concat(Parameters).Concat(Returns);

    public MethodSymbol(ISymbol? scope, Method method) : base(scope, method.Name) {
      Declaration = method;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"method {Declaration.Name}({Declaration.Ins.AsCommaSeperatedText()}) : ({Declaration.Outs.AsCommaSeperatedText()})";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
