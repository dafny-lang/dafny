using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Instances of this class are introduced during resolution to indicate that a static method or function has
/// been invoked without specifying a receiver (that is, by just giving the name of the enclosing class).
/// </summary>
public class StaticReceiverExpr : LiteralExpr {
  public readonly Type UnresolvedType;
  private bool Implicit;
  public Expression OriginalResolved;

  public StaticReceiverExpr(IToken tok, Type t, bool isImplicit)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(t != null);
    UnresolvedType = t;
    Implicit = isImplicit;
    OriginalResolved = null;
  }

  /// <summary>
  /// Constructs a resolved LiteralExpr representing the fictitious static-receiver literal whose type is
  /// "cl" parameterized by the type arguments of "cl" itself.
  /// </summary>
  public StaticReceiverExpr(IToken tok, TopLevelDeclWithMembers cl, bool isImplicit)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(cl != null);
    var typeArgs = cl.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
    Type = new UserDefinedType(tok, cl is ClassDecl klass && klass.IsDefaultClass ? cl.Name : cl.Name + "?", cl, typeArgs);
    UnresolvedType = Type;
    Implicit = isImplicit;
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
  public StaticReceiverExpr(IToken tok, UserDefinedType t, TopLevelDeclWithMembers cl, bool isImplicit, Expression lhs = null)
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
    Implicit = isImplicit;
    OriginalResolved = lhs;
  }

  public override bool IsImplicit {
    get { return Implicit; }
  }

  public override IEnumerable<INode> Children => base.Children.Concat(Type.Nodes);
}