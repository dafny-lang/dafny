using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore;
using DafnyCore.Options;

namespace Microsoft.Dafny;

public class PrintStmt : Statement, ICloneable<PrintStmt>, ICanFormat {
  public readonly List<Expression> Args;

  public static readonly Option<bool> TrackPrintEffectsOption = new("--track-print-effects",
    "A compiled method, constructor, or iterator is allowed to have print effects only if it is marked with {{:print}}.");
  static PrintStmt() {
    DafnyOptions.RegisterLegacyBinding(TrackPrintEffectsOption, (options, value) => {
      options.EnforcePrintEffects = value;
    });

    OptionRegistry.RegisterGlobalOption(TrackPrintEffectsOption, OptionCompatibility.CheckOptionLocalImpliesLibrary);
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

  public PrintStmt(IOrigin rangeOrigin, List<Expression> args)
    : base(rangeOrigin) {
    Contract.Requires(rangeOrigin != null);
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

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentPrintRevealStmt(indentBefore, OwnedTokens);
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    if (mustBeErasable) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_print_statement_is_not_ghost, this,
        "print statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
    } else {
      Args.ForEach(ee => ExpressionTester.CheckIsCompilable(resolver, reporter, ee, codeContext));
    }
  }
}
