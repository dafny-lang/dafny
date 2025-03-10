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
  public OverrideCenter(IOrigin wrappedOrigin, TokenRange newCenter) : base(wrappedOrigin) {
    this.ReportingRange = newCenter;
  }

  public override TokenRange ReportingRange { get; }

  public override int col {
    get => ReportingRange.Start.col;
    set => throw new System.NotImplementedException();
  }

  public override int line {
    get => ReportingRange.Start.line;
    set => throw new System.NotImplementedException();
  }

  public override int pos {
    get => ReportingRange.Start.pos;
    set => throw new System.NotImplementedException();
  }

  public override string val {
    get => ReportingRange.Start.val;
    set => throw new System.NotImplementedException();
  }
}