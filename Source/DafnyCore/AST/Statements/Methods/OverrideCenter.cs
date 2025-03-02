using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

/// <summary>
/// This class temporarily exists to retain old behavior
/// When it comes to where errors are reported.
///
/// For function calls, the following location is used to report precondition failures:
/// 
/// someFunction(x, y);
/// ^           ^
/// old     future
///
/// For assertions, when the condition does not hold
/// assert P(x)
/// ^       ^
/// future  old
/// </summary>
class OverrideCenter : OriginWrapper {
  public OverrideCenter(IOrigin wrappedToken, IOrigin origin) : base(wrappedToken) {
    this.Center = origin.Center;
  }

  public OverrideCenter(IOrigin wrappedToken, Location newCenter) : base(wrappedToken) {
    this.Center = newCenter;
  }

  public override Location Center { get; }

  public override int col {
    get => WrappedToken.col;
    set => throw new System.NotImplementedException();
  }

  public override int line {
    get => WrappedToken.line;
    set => throw new System.NotImplementedException();
  }

  public override int pos {
    get => WrappedToken.pos;
    set => throw new System.NotImplementedException();
  }

  public override string val {
    get => WrappedToken.val;
    set => throw new System.NotImplementedException();
  }
}