using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public abstract class DafnyAssertionDescription : ProofObligationDescription {
}

//// Arithmetic and logical operators

public class DafnyDivisionDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "divisor is always non-zero.";

  public override string FailureDescription =>
    "possible division by zero";

  public override string ShortDescription => "non-zero divisor";
}

public class DafnyShiftLowerDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "shift amount is always non-negative";

  public override string FailureDescription =>
    "shift amount must be non-negative";

  public override string ShortDescription => "shift lower bound";
}

public class DafnyShiftUpperDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"shift amount is always within the width of the result ({width})";

  public override string FailureDescription =>
    $"shift amount must not exceed the width of the result ({width})";

  public override string ShortDescription => "shift upper bound";

  private readonly int width;

  public DafnyShiftUpperDescription(int width) {
    this.width = width;
  }
}

//// Object properties

public class DafnyNonNullDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{what} object is never null";

  public override string FailureDescription =>
    $"{what} may be null";

  public override string ShortDescription => $"{what} non-null";

  private readonly string what;
  public DafnyNonNullDescription(string what) {
    this.what = what;
  }
}

public class DafnyAllocatedDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{what} is always allocated";

  public override string FailureDescription =>
    $"{what} may not be allocated";

  public override string ShortDescription => $"{what} allocated";

  private readonly string what;
  public DafnyAllocatedDescription(string what) {
    this.what = what;
  }
}

public class DafnyTwoStateAllocatedDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{what} is always allocated in the two-state {abstractionType}'s previous state";

  public override string FailureDescription =>
    $"{what} must be allocated in the two-state {abstractionType}'s previous state";

  public override string ShortDescription => $"{what} allocated in previous state";

  private readonly string what;
  private readonly string abstractionType;

  public DafnyTwoStateAllocatedDescription(string what, string abstractionType) {
    this.what = what;
    this.abstractionType = abstractionType;
  }
}

//// Contract constraints

public class DafnyPreconditionCheckDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    customErrMsg is null ?
      "function precondition satisfied" :
      $"error is impossible: {customErrMsg}";

  public override string FailureDescription =>
    customErrMsg ?? "possible violation of function precondition";

  public override string ShortDescription => "precondition";

  private readonly string customErrMsg;

  public DafnyPreconditionCheckDescription([CanBeNull] string customErrMsg) {
    this.customErrMsg = customErrMsg;
  }
}

public class DafnyAssertStatementDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    customErrMsg is null ?
      "assertion always holds" :
      $"error is impossible: {customErrMsg}";

  public override string FailureDescription =>
    customErrMsg ?? "assertion might not hold";

  public override string ShortDescription => "precondition";

  private readonly string customErrMsg;

  public DafnyAssertStatementDescription([CanBeNull] string customErrMsg) {
    this.customErrMsg = customErrMsg;
  }
}

public class DafnyCalculationStepDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "the calculation step between the previous line and this line always holds";

  public override string FailureDescription =>
    "the calculation step between the previous line and this line might not hold";

  public override string ShortDescription => "calc step";
}

public class DafnyEnsuresStrongerDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "the method provides a postcondition equal to or more detailed than in its parent trait";

  public override string FailureDescription =>
    "the method must provide an equal or more detailed postcondition than in its parent trait";

  public override string ShortDescription => "ensures stronger";
}

public class DafnyRequiresWeakerDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "the method provides a precondition equal to or more permissive than in its parent trait";

  public override string FailureDescription =>
    "the method must provide an equal or more permissive precondition than in its parent trait";

  public override string ShortDescription => "requires weaker";
}

public class DafnyForallPostDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "postcondition of forall statement always holds";

  public override string FailureDescription =>
    "possible violation of postcondition of forall statement";

  public override string ShortDescription => "forall ensures";
}

public class DafnyYieldEnsuresDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "yield-ensures condition always holds";

  public override string FailureDescription =>
    "possible violation of yield-ensures condition";

  public override string ShortDescription => "yield ensures";
}

//// Structural constraints

public class DafnyCompleteMatchDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "match statement covers all cases";

  public override string FailureDescription =>
    $"missing case in match statement: {missing}";

  public override string ShortDescription => "match complete";

  private readonly string missing;
  public DafnyCompleteMatchDescription(string missing) {
    this.missing = missing;
  }
}

//// Misc constraints

public class DafnyIndicesInDomainDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"all {objType} indices are in the domain of the initialization function";

  public override string FailureDescription =>
    $"all {objType} indices must be in the domain of the initialization function";

  public override string ShortDescription => "indices in domain";

  private readonly string objType;

  public DafnyIndicesInDomainDescription(string objType) {
    this.objType = objType;
  }
}

public class DafnySubrangeCheckDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"error is impossible: {msg}";

  public override string FailureDescription => msg;

  public override string ShortDescription => "subrange check";

  private readonly string msg;

  public DafnySubrangeCheckDescription(string msg) {
    this.msg = msg;
  }
}

public class DafnyWitnessCheckDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"error is impossible: {msg}";

  public override string FailureDescription => msg;

  public override string ShortDescription => "witness check";

  private readonly string msg;

  public DafnyWitnessCheckDescription(string msg) {
    this.msg = msg;
  }
}

public class DafnyPrefixEqualityLimitDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "prefix-equality limit is at least 0";

  public override string FailureDescription =>
    "prefix-equality limit must be at least 0";

  public override string ShortDescription => "prefix-equality limit";
}
