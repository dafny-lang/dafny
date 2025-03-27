using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class NestedOrigin : OriginWrapper {
  public NestedOrigin(IOrigin outer, IOrigin inner) : this(outer, inner, null) {
  }

  public NestedOrigin(IOrigin outer, IOrigin inner, string message)
    : base(outer) {
    Contract.Requires(outer != null);
    Contract.Requires(inner != null);
    Inner = inner;
    this.Message = message;
  }
  public IOrigin Outer { get { return WrappedOrigin; } }
  public readonly IOrigin Inner;
  public readonly string Message;
}