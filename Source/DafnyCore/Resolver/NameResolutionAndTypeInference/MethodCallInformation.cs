using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MethodCallInformation {
  public readonly IToken Tok;
  public readonly MemberSelectExpr Callee;
  public readonly List<ActualBinding> ActualParameters;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
    Contract.Invariant(Callee != null);
    Contract.Invariant(Callee.Member is Method);
    Contract.Invariant(ActualParameters != null);
  }

  public MethodCallInformation(IToken tok, MemberSelectExpr callee, List<ActualBinding> actualParameters) {
    Contract.Requires(tok != null);
    Contract.Requires(callee != null);
    Contract.Requires(callee.Member is Method);
    Contract.Requires(actualParameters != null);
    this.Tok = tok;
    this.Callee = callee;
    this.ActualParameters = actualParameters;
  }
}