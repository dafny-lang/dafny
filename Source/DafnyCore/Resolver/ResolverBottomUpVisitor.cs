using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class ResolverBottomUpVisitor : BottomUpVisitor {
  protected Resolver resolver;
  public ResolverBottomUpVisitor(Resolver resolver) {
    Contract.Requires(resolver != null);
    this.resolver = resolver;
  }
}