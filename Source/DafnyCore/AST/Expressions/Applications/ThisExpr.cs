using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ThisExpr : Expression, ICloneable<ThisExpr> {
  public ThisExpr(Cloner cloner, ThisExpr original) : base(cloner, original) {
  }

  public ThisExpr(IToken tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }

  /// <summary>
  /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
  /// of member "m". This constructor is intended to be used by post-resolution code that needs
  /// to obtain a Dafny "this" expression.
  /// </summary>
  public ThisExpr(MemberDecl m)
    : base(m.tok) {
    Contract.Requires(m != null);
    Contract.Requires(m.tok != null);
    Contract.Requires(m.EnclosingClass != null);
    Contract.Requires(!m.IsStatic);
    Type = ModuleResolver.GetReceiverType(m.tok, m);
  }

  /// <summary>
  /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
  /// of member "m". This constructor is intended to be used by post-resolution code that needs
  /// to obtain a Dafny "this" expression.
  /// </summary>
  public ThisExpr(TopLevelDeclWithMembers cl)
    : base(cl.tok) {
    Contract.Requires(cl != null);
    Contract.Requires(cl.tok != null);
    Type = ModuleResolver.GetThisType(cl.tok, cl);
  }

  public ThisExpr Clone(Cloner cloner) {
    return new ThisExpr(cloner, this);
  }
}

public class ImplicitThisExpr : ThisExpr, ICloneable<ImplicitThisExpr> {
  public ImplicitThisExpr(Cloner cloner, ImplicitThisExpr original) : base(cloner, original) {
  }

  public ImplicitThisExpr(IToken tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }

  public override bool IsImplicit {
    get { return true; }
  }

  public new ImplicitThisExpr Clone(Cloner cloner) {
    return new ImplicitThisExpr(cloner, this);
  }
}

/// <summary>
/// An ImplicitThisExpr_ConstructorCall is used in the .InitCall of a TypeRhs,
/// which has a need for a "throw-away receiver".  Using a different type
/// gives a way to distinguish this receiver from other receivers, which
/// plays a role in checking the restrictions on divided block statements.
/// </summary>
public class ImplicitThisExpr_ConstructorCall : ImplicitThisExpr, ICloneable<ImplicitThisExpr_ConstructorCall> {
  public ImplicitThisExpr_ConstructorCall(Cloner cloner, ImplicitThisExpr_ConstructorCall original) : base(cloner, original) {
  }

  public ImplicitThisExpr_ConstructorCall(IToken tok)
    : base(tok) {
    Contract.Requires(tok != null);
  }

  public new ImplicitThisExpr_ConstructorCall Clone(Cloner cloner) {
    return new ImplicitThisExpr_ConstructorCall(cloner, this);
  }
}