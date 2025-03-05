using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class NestedOrigin : OriginWrapper {
  public NestedOrigin(IOrigin outer, IOrigin inner, string message = "this proposition could not be proved")
    : base(outer) {
    Contract.Requires(outer != null);
    Contract.Requires(inner != null);
    Inner = inner;
    this.Message = message;
  }
  public IOrigin Outer { get { return WrappedToken; } }
  public readonly IOrigin Inner;
  public readonly string Message;
}