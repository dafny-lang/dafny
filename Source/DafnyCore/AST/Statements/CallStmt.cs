using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// A CallStmt is always resolved.  It is typically produced as a resolved counterpart of the syntactic AST note ApplySuffix.
/// </summary>
public class CallStmt : Statement, ICloneable<CallStmt> {
  // OverrideToken is required because MethodSelect.EndToken can be incorrect. Will remove once resolved expressions have correct ranges.
  public override IToken Tok => overrideToken ?? MethodSelect.EndToken.Next;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(MethodSelect.Member is Method);
    Contract.Invariant(cce.NonNullElements(Lhs));
    Contract.Invariant(cce.NonNullElements(Args));
  }

  public override IEnumerable<Node> Children => Lhs.Concat(new Node[] { MethodSelect, Bindings });
  public readonly List<Expression> Lhs;
  public readonly MemberSelectExpr MethodSelect;
  private readonly IToken overrideToken;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;
  public Expression OriginalInitialLhs = null;

  public Expression Receiver { get { return MethodSelect.Obj; } }
  public Method Method { get { return (Method)MethodSelect.Member; } }

  public CallStmt(RangeToken rangeToken, List<Expression> lhs, MemberSelectExpr memSel, List<ActualBinding> args, IToken overrideToken = null)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(cce.NonNullElements(lhs));
    Contract.Requires(memSel != null);
    Contract.Requires(memSel.Member is Method);
    Contract.Requires(cce.NonNullElements(args));

    this.Lhs = lhs;
    this.MethodSelect = memSel;
    this.overrideToken = overrideToken;
    this.Bindings = new ActualBindings(args);
  }

  public CallStmt Clone(Cloner cloner) {
    return new CallStmt(cloner, this);
  }

  public CallStmt(Cloner cloner, CallStmt original) : base(cloner, original) {
    MethodSelect = (MemberSelectExpr)cloner.CloneExpr(original.MethodSelect);
    Lhs = original.Lhs.Select(cloner.CloneExpr).ToList();
    Bindings = new ActualBindings(cloner, original.Bindings);
    overrideToken = original.overrideToken;
  }

  /// <summary>
  /// This constructor is intended to be used when constructing a resolved CallStmt. The "args" are expected
  /// to be already resolved, and are all given positionally.
  /// </summary>
  public CallStmt(RangeToken rangeToken, List<Expression> lhs, MemberSelectExpr memSel, List<Expression> args)
    : this(rangeToken, lhs, memSel, args.ConvertAll(e => new ActualBinding(null, e))) {
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
