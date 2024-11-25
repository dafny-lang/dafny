using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Instances of this class are introduced during resolution to indicate that a static method or function has
/// been invoked without specifying a receiver (that is, by just giving the name of the enclosing class).
/// </summary>
public class StaticReceiverExpr : LiteralExpr, ICloneable<StaticReceiverExpr> {
  public readonly Type UnresolvedType;
  /// <summary>
  /// A static member can be invoked through an object, in which case the object is not used for the call.
  /// However, the object expression must be verified and is thus stored here, in addition to its type.
  /// </summary>
  public Expression ObjectToDiscard;

  /// <summary>
  /// In case this static receiver was specified through a dot expression, this field contains the LHS of the dot.
  /// </summary>
  public Expression ContainerExpression;

  public StaticReceiverExpr(IOrigin tok, Type t, bool isImplicit)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(t != null);
    UnresolvedType = t;
    IsImplicit = isImplicit;
  }

  public StaticReceiverExpr(Cloner cloner, StaticReceiverExpr original) : base(cloner, original) {
    UnresolvedType = cloner.CloneType(original.UnresolvedType);
    IsImplicit = original.IsImplicit;
  }

  /// <summary>
  /// Constructs a resolved LiteralExpr representing the fictitious static-receiver literal whose type is
  /// "cl" parameterized by the type arguments of "cl" itself.
  /// </summary>
  public StaticReceiverExpr(IOrigin tok, TopLevelDeclWithMembers cl, bool isImplicit, Expression lhs = null)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(cl != null);
    var typeArgs = cl.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
    Type = new UserDefinedType(tok, cl is DefaultClassDecl ? cl.Name : cl.Name + "?", cl, typeArgs);
    UnresolvedType = Type;
    IsImplicit = isImplicit;
    ObjectToDiscard = lhs;
  }

  /// <summary>
  /// Constructs a resolved LiteralExpr representing the fictitious literal whose type is
  /// "cl" parameterized according to the type arguments to "t".  It is assumed that "t" denotes
  /// a class or trait that (possibly reflexively or transitively) extends "cl".
  /// Examples:
  /// * If "t" denotes "C(G)" and "cl" denotes "C", then the type of the StaticReceiverExpr
  ///   will be "C(G)".
  /// * Suppose "C" is a class that extends a trait "T"; then, if "t" denotes "C" and "cl" denotes
  ///   "T", then the type of the StaticReceiverExpr will be "T".
  /// * Suppose "C(X)" is a class that extends "T(f(X))", and that "T(Y)" is
  ///   a trait that in turn extends trait "W(g(Y))".  If "t" denotes type "C(G)" and "cl" denotes "W",
  ///   then type of the StaticReceiverExpr will be "T(g(f(G)))".
  /// </summary>
  public StaticReceiverExpr(IOrigin tok, UserDefinedType t, TopLevelDeclWithMembers cl, bool isImplicit, Expression lhs = null)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(t.ResolvedClass != null);
    Contract.Requires(cl != null);
    var top = t.AsTopLevelTypeWithMembersBypassInternalSynonym;
    if (top != cl) {
      Contract.Assert(top != null);
      var clArgsInTermsOfTFormals = cl.TypeArgs.ConvertAll(tp => top.ParentFormalTypeParametersToActuals[tp]);
      var subst = TypeParameter.SubstitutionMap(top.TypeArgs, t.TypeArgs);
      var typeArgs = clArgsInTermsOfTFormals.ConvertAll(ty => ty.Subst(subst));
      Type = new UserDefinedType(tok, cl.Name, cl, typeArgs);
    } else if (t.Name != cl.Name) {  // t may be using the name "C?", and we'd prefer it read "C"
      Type = new UserDefinedType(tok, cl.Name, cl, t.TypeArgs);
    } else {
      Type = t;
    }
    UnresolvedType = Type;
    IsImplicit = isImplicit;
    ObjectToDiscard = lhs;
  }

  public override bool IsImplicit { get; }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ObjectToDiscard != null) {
        yield return ObjectToDiscard;
      }
      foreach (var ee in base.SubExpressions) {
        yield return ee;
      }
    }
  }

  public override IEnumerable<INode> Children =>
    new[] { ObjectToDiscard, ContainerExpression }.Where(x => x != null).Concat(Type.Nodes);

  public new StaticReceiverExpr Clone(Cloner cloner) {
    return new StaticReceiverExpr(cloner, this);
  }
}
