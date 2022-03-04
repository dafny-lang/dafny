using Microsoft.Boogie;

namespace Microsoft.Dafny;

public abstract class DafnyAssertionDescription : ProofObligationDescription {
}

public class DafnyDivisionAssertion : DafnyAssertionDescription {
  public override string SuccessDescription => "Divisor is always non-zero.";

  public override string FailureDescription => "possible division by zero";

  public override string ShortDescription => "non-zero divisor";
}
