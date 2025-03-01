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
  public OverrideCenter(IOrigin wrappedToken, Token newCenter) : base(wrappedToken) {
    this.Center = newCenter;
  }

  public override Token Center { get; }

  public override int col {
    get => Center.col;
    set => throw new System.NotImplementedException();
  }

  public override int line {
    get => Center.line;
    set => throw new System.NotImplementedException();
  }

  public override int pos {
    get => Center.pos;
    set => throw new System.NotImplementedException();
  }

  public override string val {
    get => Center.val;
    set => throw new System.NotImplementedException();
  }
}