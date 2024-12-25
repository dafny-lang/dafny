using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class FunctionCallExpr : Expression, IHasReferences, ICloneable<FunctionCallExpr> {
  public Name NameNode;
  public string Name => NameNode.Value;
  public readonly Expression Receiver;
  public readonly IOrigin OpenParen;  // can be null if Args.Count == 0
  public readonly Token CloseParen;
  public readonly Label/*?*/ AtLabel;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;
  [FilledInDuringResolution] public List<PreType> PreTypeApplication_AtEnclosingClass;
  [FilledInDuringResolution] public List<PreType> PreTypeApplication_JustFunction;
  [FilledInDuringResolution] public List<Type> TypeApplication_AtEnclosingClass;
  [FilledInDuringResolution] public List<Type> TypeApplication_JustFunction;
  [FilledInDuringResolution] public bool IsByMethodCall;

  /// <summary>
  /// Return a mapping from each type parameter of the function and its enclosing class to actual type arguments.
  /// This method should only be called on fully and successfully resolved FunctionCallExpr's.
  /// </summary>
  public Dictionary<TypeParameter, Type> GetTypeArgumentSubstitutions() {
    return TypeArgumentSubstitutionsWithParents();
  }

  /// <summary>
  /// Returns a mapping from formal type parameters to actual type arguments. For example, given
  ///     trait T<A> {
  ///       function F<X>(): bv8 { ... }
  ///     }
  ///     class C<B, D> extends T<map<B, D>> { }
  /// and FunctionCallExpr o.F<int>(args) where o has type C<real, bool>, the type map returned is
  ///     A -> map<real, bool>
  ///     B -> real
  ///     D -> bool
  ///     X -> int
  /// NOTE: This method should be called only when all types have been fully and successfully
  /// resolved.
  /// </summary>
  public Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsWithParents() {
    Contract.Requires(WasResolved());
    Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

    return MemberSelectExpr.TypeArgumentSubstitutionsWithParentsAux(Receiver.Type, Function, TypeApplication_JustFunction);
  }

  public enum CoCallResolution {
    No,
    Yes,
    NoBecauseFunctionHasSideEffects,
    NoBecauseFunctionHasPostcondition,
    NoBecauseRecursiveCallsAreNotAllowedInThisContext,
    NoBecauseIsNotGuarded,
    NoBecauseRecursiveCallsInDestructiveContext
  }
  [FilledInDuringResolution] public CoCallResolution CoCall = CoCallResolution.No;  // indicates whether or not the call is a co-recursive call
  [FilledInDuringResolution] public string CoCallHint = null;  // possible additional hint that can be used in verifier error message

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
    Contract.Invariant(Receiver != null);
    Contract.Invariant(cce.NonNullElements(Args));
    Contract.Invariant(
      Function == null || TypeApplication_AtEnclosingClass == null ||
      Function.EnclosingClass.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
    Contract.Invariant(
      Function == null || TypeApplication_JustFunction == null ||
      Function.TypeArgs.Count == TypeApplication_JustFunction.Count);
  }

  [FilledInDuringResolution] public Function Function;

  public FunctionCallExpr(string fn, Expression receiver, IOrigin openParen, Token closeParen,
    [Captured] ActualBindings bindings, Label /*?*/ atLabel = null)
    : this(Token.NoToken, new Name(Token.NoToken, fn), receiver, openParen, closeParen, bindings,
      atLabel) {
  }

  public FunctionCallExpr(IOrigin tok, Name fn, Expression receiver, IOrigin openParen, Token closeParen, [Captured] List<ActualBinding> args, Label/*?*/ atLabel = null)
    : this(tok, fn, receiver, openParen, closeParen, new ActualBindings(args), atLabel) {
    Contract.Requires(tok != null);
    Contract.Requires(fn != null);
    Contract.Requires(receiver != null);
    Contract.Requires(cce.NonNullElements(args));
    Contract.Requires(openParen != null || args.Count == 0);
    Contract.Ensures(type == null);
  }

  public FunctionCallExpr(IOrigin tok, Name fn, Expression receiver, IOrigin openParen, Token closeParen, [Captured] ActualBindings bindings, Label/*?*/ atLabel = null)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(fn != null);
    Contract.Requires(receiver != null);
    Contract.Requires(bindings != null);
    Contract.Requires(openParen != null);
    Contract.Ensures(type == null);

    this.NameNode = fn;
    this.Receiver = receiver;
    this.OpenParen = openParen;
    this.CloseParen = closeParen;
    this.AtLabel = atLabel;
    this.Bindings = bindings;
    this.FormatTokens = closeParen != null ? new[] { closeParen } : null;
  }

  /// <summary>
  /// This constructor is intended to be used when constructing a resolved FunctionCallExpr. The "args" are expected
  /// to be already resolved, and are all given positionally.
  /// </summary>
  public FunctionCallExpr(IOrigin tok, Name fn, Expression receiver, IOrigin openParen, Token closeParen, [Captured] List<Expression> args,
    Label /*?*/ atLabel = null)
    : this(tok, fn, receiver, openParen, closeParen, args.ConvertAll(e => new ActualBinding(null, e)), atLabel) {
    Bindings.AcceptArgumentExpressionsAsExactParameterList();
  }

  public FunctionCallExpr Clone(Cloner cloner) {
    return new FunctionCallExpr(cloner, this);
  }

  public FunctionCallExpr(Cloner cloner, FunctionCallExpr original) : base(cloner, original) {
    NameNode = new Name(cloner, original.NameNode);
    Receiver = cloner.CloneExpr(original.Receiver);
    OpenParen = original.OpenParen == null ? null : cloner.Origin(original.OpenParen);
    CloseParen = original.CloseParen;
    Bindings = new ActualBindings(cloner, original.Bindings);
    AtLabel = original.AtLabel;

    if (cloner.CloneResolvedFields) {
      TypeApplication_AtEnclosingClass = original.TypeApplication_AtEnclosingClass;
      TypeApplication_JustFunction = original.TypeApplication_JustFunction;
      IsByMethodCall = original.IsByMethodCall;
      Function = original.Function;
      CoCall = original.CoCall;
      CoCallHint = original.CoCallHint;
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Receiver;
      foreach (var e in Args) {
        yield return e;
      }
    }
  }

  public override IEnumerable<Type> ComponentTypes => Util.Concat(TypeApplication_AtEnclosingClass, TypeApplication_JustFunction);
  public IEnumerable<Reference> GetReferences() {
    return Enumerable.Repeat(new Reference(NameNode.Origin, Function), 1);
  }
}