using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class PrintStmt : Statement, ICloneable<PrintStmt> {
  public readonly List<Expression> Args;

  public static readonly Option<bool> TrackPrintEffectsOption = new("--track-print-effects",
    "A compiled method, constructor, or iterator is allowed to have print effects only if it is marked with {{:print}}.");
  static PrintStmt() {
    DafnyOptions.RegisterLegacyBinding(TrackPrintEffectsOption, (options, value) => {
      options.EnforcePrintEffects = value;
    });
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Args));
  }

  public PrintStmt Clone(Cloner cloner) {
    return new PrintStmt(cloner, this);
  }

  public PrintStmt(Cloner cloner, PrintStmt original) : base(cloner, original) {
    Args = original.Args.Select(cloner.CloneExpr).ToList();
  }

  public PrintStmt(IToken tok, IToken endTok, List<Expression> args)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(args));

    Args = args;
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var arg in Args) {
        yield return arg;
      }
    }
  }
}
