using Core;

namespace Microsoft.Dafny;

public abstract class DafnyAssertionDescription : AssertionDescription {
}

public class DafnyDivisionAssertion : DafnyAssertionDescription {
  public override string SuccessDescription => "Divisor is always non-zero.";

  public override string FailureDescription => "possible division by zero";

  public override string ShortDescription => "non-zero divisor";
}