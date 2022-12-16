using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// A CallStmt is always resolved.  It is typically produced as a resolved counterpart of the syntactic AST note ApplySuffix.
/// </summary>
public class CallStmt : Statement {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(MethodSelect.Member is Method);
    Contract.Invariant(cce.NonNullElements(Lhs));
    Contract.Invariant(cce.NonNullElements(Args));
  }

  public readonly List<Expression> Lhs;
  public readonly MemberSelectExpr MethodSelect;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;
  public Expression OriginalInitialLhs = null;

  public Expression Receiver { get { return MethodSelect.Obj; } }
  public Method Method { get { return (Method)MethodSelect.Member; } }

  public CallStmt(IToken tok, IToken endTok, List<Expression> lhs, MemberSelectExpr memSel, List<ActualBinding> args)
    : base(tok, endTok) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(lhs));
    Contract.Requires(memSel != null);
    Contract.Requires(memSel.Member is Method);
    Contract.Requires(cce.NonNullElements(args));

    this.Lhs = lhs;
    this.MethodSelect = memSel;
    this.Bindings = new ActualBindings(args);
  }

  /// <summary>
  /// This constructor is intended to be used when constructing a resolved CallStmt. The "args" are expected
  /// to be already resolved, and are all given positionally.
  /// </summary>
  public CallStmt(IToken tok, IToken endTok, List<Expression> lhs, MemberSelectExpr memSel, List<Expression> args)
    : this(tok, endTok, lhs, memSel, args.ConvertAll(e => new ActualBinding(null, e))) {
    Bindings.AcceptArgumentExpressionsAsExactParameterList();
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var ee in Lhs) {
        yield return ee;
      }
      yield return MethodSelect;
      foreach (var ee in Args) {
        yield return ee;
      }
    }
  }
}
