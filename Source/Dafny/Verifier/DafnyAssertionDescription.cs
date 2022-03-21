using System.Configuration;
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
    $"{PluralSuccess}{what} object is never null";

  public override string FailureDescription =>
    $"{PluralFailure}{what} may be null";

  public override string ShortDescription => $"{what} non-null";
  private readonly string what;
  private bool plural;
  private string PluralSuccess => plural ? "each " : "";
  private string PluralFailure => plural ? "some " : "";

  public DafnyNonNullDescription(string what, bool plural = false) {
    this.what = what;
    this.plural = plural;
  }
}

public class DafnyAllocatedDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{PluralSuccess}{what} is always allocated{WhenSuffix}";

  public override string FailureDescription =>
    $"{PluralFailure}{what} may not be allocated{WhenSuffix}";

  public override string ShortDescription => $"{what} allocated";

  private readonly string what;
  [CanBeNull] private readonly string when;
  private bool plural;
  private string WhenSuffix => when is null ? "" : $" {when}";
  private string PluralSuccess => plural ? "each " : "";
  private string PluralFailure => plural ? "some " : "";

  public DafnyAllocatedDescription(string what, string when, bool plural = false) {
    this.what = what;
    this.when = when;
    this.plural = plural;
  }
}

//// Contract constraints

public class DafnyPreconditionCheckDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    customErrMsg is null
      ? "function precondition satisfied"
      : $"error is impossible: {customErrMsg}";

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
    customErrMsg is null
      ? "assertion always holds"
      : $"error is impossible: {customErrMsg}";

  public override string FailureDescription =>
    customErrMsg ?? "assertion might not hold";

  public override string ShortDescription => "precondition";

  private readonly string customErrMsg;

  public DafnyAssertStatementDescription([CanBeNull] string customErrMsg) {
    this.customErrMsg = customErrMsg;
  }
}

public class DafnyLoopInvariantDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    customErrMsg is null
      ? "loop invariant always holds"
      : $"error is impossible: {customErrMsg}";

  public override string FailureDescription =>
    customErrMsg ?? "loop invariant violation";

  public override string ShortDescription => "loop invariant";

  private readonly string customErrMsg;

  public DafnyLoopInvariantDescription([CanBeNull] string customErrMsg) {
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
    $"match {matchForm} covers all cases";

  public override string FailureDescription =>
    $"missing case in match {matchForm}: {missing}";

  public override string ShortDescription => "match complete";

  private readonly string matchForm;
  private readonly string missing;
  public DafnyCompleteMatchDescription(string matchForm, string missing) {
    this.matchForm = matchForm;
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
    "type is inhabited";

  public override string FailureDescription =>
    witnessString is null
      ? "the given witness expression might not satisfy constraint"
      : (witnessString == "" ? $"{errMsg}{hintMsg}" : $"{errMsg} (only tried {witnessString}){hintMsg}");

  public override string ShortDescription => "witness check";

  private readonly string errMsg = "cannot find witness that shows type is inhabited";
  private readonly string hintMsg =
    "; try giving a hint through a 'witness' or 'ghost witness' clause, or use 'witness *' to treat as a possibly empty type";
  private readonly string witnessString;

  public DafnyWitnessCheckDescription(string witnessString) {
    this.witnessString = witnessString;
  }
}

public class DafnyPrefixEqualityLimitDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "prefix-equality limit is at least 0";

  public override string FailureDescription =>
    "prefix-equality limit must be at least 0";

  public override string ShortDescription => "prefix-equality limit";
}

public class DafnyForRangeBoundsDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "lower bound does not exceed upper bound";

  public override string FailureDescription =>
    "lower bound must not exceed upper bound";

  public override string ShortDescription => "for range bounds";
}

public class DafnyForRangeAssignableDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "entire range is assignable to index variable";

  public override string FailureDescription =>
    $"entire range must be assignable to index variable, but some {msg}";

  public override string ShortDescription => "for range assignable";

  private readonly string msg;

  public DafnyForRangeAssignableDescription(string msg) {
    this.msg = msg;
  }
}

public class DafnyNotRecursiveSettingDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{what} is valid in recursive setting";

  public override string FailureDescription =>
    $"cannot use {what} in recursive setting.{hint ?? ""}";

  public override string ShortDescription => "valid in recursion";

  private readonly string what;
  private readonly string hint;

  public DafnyNotRecursiveSettingDescription(string what, string hint) {
    this.what = what;
    this.hint = hint;
  }
}

public class DafnyTerminationDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "loop or recursion terminates";

  public override string FailureDescription =>
    (inferredDescreases
      ? "cannot prove termination; try supplying a decreases clause"
      : "decreases clause might not decrease") +
    (hint is null ? "" : $" ({hint})");

  public override string ShortDescription => "termination";

  private readonly bool inferredDescreases;
  private readonly string hint;

  public DafnyTerminationDescription(bool inferredDescreases, string hint = null) {
    this.inferredDescreases = inferredDescreases;
    this.hint = hint;
  }
}

public class DafnyDefaultNonrecursiveDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "default value is non-recursive";

  public override string FailureDescription =>
    "default-value expression is not allowed to involve recursive or mutually recursive calls";

  public override string ShortDescription => "default nonrecursive";
}

public class DafnyModifiableDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{description} is in the enclosing context's modifies clause";

  public override string FailureDescription =>
    $"assignment may update {description} not in the enclosing context's modifies clause";

  public override string ShortDescription => "modifiable";

  private readonly string description;

  public DafnyModifiableDescription(string description) {
    this.description = description;
  }
}

public class DafnyForallLHSUniqueDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "left-hand sides of forall-statement bound variables are unique";

  public override string FailureDescription =>
    "left-hand sides for different forall-statement bound variables may refer to the same location";

  public override string ShortDescription => "forall bound unique";
}

public class DafnyTraitFrameDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    isModify
      ? "expression abides by trait context's modifies clause"
      : "expression abides by trait context's reads clause";

  public override string FailureDescription =>
    isModify
      ? "expression may read an object not in the parent trait context's reads clause"
      : "expression may modify an object not in the parent trait context's modifies clause";

  public override string ShortDescription =>
    isModify ? "trait modifies" : "trait reads";

  private bool isModify;

  public DafnyTraitFrameDescription(bool isModify) {
    this.isModify = isModify;
  }
}

public class DafnyTraitDecreasesDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{whatKind}'s decreases clause is below or equal to that in the trait";

  public override string FailureDescription =>
    $"{whatKind}'s decreases clause must be below or equal to that in the trait";

  public override string ShortDescription => "trait decreases";

  private readonly string whatKind;

  public DafnyTraitDecreasesDescription(string whatKind) {
    this.whatKind = whatKind;
  }
}

public class DafnyFrameSubsetDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    isWrite
      ? $"{whatKind} is allowed by context's modifies clause"
      : $"sufficient reads clause to {whatKind}";

  public override string FailureDescription =>
    isWrite
      ? $"{whatKind} may violate context's modifies clause"
      : $"insufficient reads clause to {whatKind}";

  public override string ShortDescription => "frame subset";

  private readonly string whatKind;
  private readonly bool isWrite;

  public DafnyFrameSubsetDescription(string whatKind, bool isWrite) {
    this.whatKind = whatKind;
    this.isWrite = isWrite;
  }
}
public class DafnyFrameDereferenceDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "frame expression does not dereference null";

  public override string FailureDescription =>
    "frame expression may dereference null";

  public override string ShortDescription => "frame dereference";
}

public class DafnyElementInDomainDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "element is in domain";

  public override string FailureDescription =>
    "element may not be in domain";

  public override string ShortDescription => "element in domain";
}

public class DafnyDefiniteAssignmentDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{what}, which is subject to definite-assignment rules, has been defined {where}";

  public override string FailureDescription =>
    $"{what}, which is subject to definite-assignment rules, might not have been defined {where}";

  public override string ShortDescription => "definite assignment";

  private readonly string what;
  private readonly string where;

  public DafnyDefiniteAssignmentDescription(string what, string where) {
    this.what = what;
    this.where = where;
  }
}

public class DafnyInRangeDescription : DafnyAssertionDescription {
  public override string SuccessDescription => $"{what} in range";

  public override string FailureDescription => $"{what} out of range";

  public override string ShortDescription => "in range";

  private readonly string what;

  public DafnyInRangeDescription(string what) {
    this.what = what;
  }
}

public class DafnyCharOverflowDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "char addition will not overflow";

  public override string FailureDescription =>
    "char addition might overflow";

  public override string ShortDescription => "char overflow";
}

public class DafnyCharUnderflowDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "char subtraction will not underflow";

  public override string FailureDescription =>
    "char subtraction might underflow";

  public override string ShortDescription => "char underflow";
}

public class DafnyConversionFitDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{prefix}{what} to be converted will always fit in {typeDesc}";

  public override string FailureDescription =>
    $"{prefix}{what} to be converted might not fit in {typeDesc}";

  public override string ShortDescription => "conversion fit";

  private readonly string prefix;
  private readonly string what;
  private readonly string typeDesc;

  public DafnyConversionFitDescription(string what, string typeDesc, string prefix = "") {
    this.prefix = prefix;
    this.what = what;
    this.typeDesc = typeDesc;
  }
}

public class DafnyNonNegativeDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{what} is never negative";

  public override string FailureDescription =>
    $"{what} might be negative";

  public override string ShortDescription => "non-negative";

  private readonly string what;

  public DafnyNonNegativeDescription(string what) {
    this.what = what;
  }
}

public class DafnyConversionPositiveDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{prefix}{what} is always positive";

  public override string FailureDescription =>
    $"{prefix}a negative {what} cannot be converted to an {typeDesc}";

  public override string ShortDescription => "conversion positive";

  private readonly string prefix;
  private readonly string what;
  private readonly string typeDesc;

  public DafnyConversionPositiveDescription(string what, string typeDesc, string prefix = "") {
    this.prefix = prefix;
    this.what = what;
    this.typeDesc = typeDesc;
  }
}

public class DafnyIsIntegerDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{prefix}the real-based number is an integer";

  public override string FailureDescription =>
    $"{prefix}the real-based number must be an integer (if you want truncation, apply .Floor to the real-based number)";

  public override string ShortDescription => "is integer";

  private readonly string prefix;

  public DafnyIsIntegerDescription(string prefix = "") {
    this.prefix = prefix;
  }
}

public class DafnyFunctionContractOverrideDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"the function provides an equal or {RestrictionDesc} than in its parent trait";

  public override string FailureDescription =>
    $"the function must provide an equal or {RestrictionDesc} than in its parent trait";

  public override string ShortDescription => "contract override valid";

  private readonly bool isEnsures;
  private string RestrictionDesc =>
    isEnsures ? "more detailed postcondition" : "more permissive precondition";

  public DafnyFunctionContractOverrideDescription(bool isEnsures) {
    this.isEnsures = isEnsures;
  }
}

public class DafnySequenceSelectRangeDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"upper bound within range of {what}";

  public override string FailureDescription =>
    $"upper bound below lower bound or above length of {what}";

  public override string ShortDescription => "upper bound within range";

  private readonly string what;

  public DafnySequenceSelectRangeDescription(string what) {
    this.what = what;
  }
}

public class DafnyComprehensionNoAliasDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "key expressions refer to unique values";

  public override string FailureDescription =>
    "key expressions may be referring to the same value";

  public override string ShortDescription => "unique key expressions";
}


public class DafnyDestructorValidDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"destructor '{dtorName}' is only applied to datatype values constructed by {ctorNames}";

  public override string FailureDescription =>
    $"destructor '{dtorName}' can only be applied to datatype values constructed by {ctorNames}";

  public override string ShortDescription => "destructor valid";

  private readonly string dtorName;
  private readonly string ctorNames;

  public DafnyDestructorValidDescription(string dtorName, string ctorNames) {
    this.dtorName = dtorName;
    this.ctorNames = ctorNames;
  }
}

public class DafnyDistinctLHSDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"left-hand sides {lhsa} and {lhsb} are distinct";

  public override string FailureDescription =>
    $"{when}left-hand sides {lhsa} and {lhsb} {may}refer to the same location{whenSuffix}";

  public override string ShortDescription => "distinct lhs";

  private readonly string lhsa;
  private readonly string lhsb;
  private readonly string may;
  private readonly string when;
  private readonly string whenSuffix;

  public DafnyDistinctLHSDescription(string lhsa, string lhsb, bool useMay, bool useWhen) {
    this.lhsa = lhsa;
    this.lhsb = lhsb;
    this.may = useMay ? "may " : "";
    this.when = useWhen ? "when " : "";
    this.whenSuffix = useWhen ? ", they must be assigned the same value" : "";
  }
}

public class DafnyArrayInitSizeDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"given array size agrees with the number of expressions in the initializing display ({size})";

  public override string FailureDescription =>
    $"given array size must agree with the number of expressions in the initializing display ({size})";

  public override string ShortDescription => "array initializer size";

  private readonly int size;

  public DafnyArrayInitSizeDescription(int size) {
    this.size = size;
  }
}

public class DafnyArrayInitEmptyDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "array initializer has empty size";

  public override string FailureDescription =>
    $"unless an initializer is provided for the array elements, a new array of '{typeDesc}' must have empty size";

  public override string ShortDescription => "array initializer empty";

  private readonly string typeDesc;

  public DafnyArrayInitEmptyDescription(string typeDesc) {
    this.typeDesc = typeDesc;
  }
}

public class DafnyPatternShapeDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"RHS will always match the pattern '{ctorName}'";

  public override string FailureDescription =>
    $"RHS is not certain to look like the pattern '{ctorName}'";

  public override string ShortDescription => "pattern shape valid";

  private readonly string ctorName;

  public DafnyPatternShapeDescription(string ctorName) {
    this.ctorName = ctorName;
  }
}

public class DafnyCorrectConstructorDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"source of datatype update is constructed by {ctorNames}";

  public override string FailureDescription =>
    $"source of datatype update must be constructed by {ctorNames}";

  public override string ShortDescription => "constructor names valid";

  private readonly string ctorNames;

  public DafnyCorrectConstructorDescription(string ctorNames) {
    this.ctorNames = ctorNames;
  }
}

public class DafnyOrdinalSubtractionIsNatural : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "TODO";

  public override string FailureDescription =>
    "RHS of ORDINAL subtraction must be a natural number, but the given RHS might be larger";

  public override string ShortDescription => "TODO";
}

public class DafnyOrdinalSubtractionUnderflow : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "TODO";

  public override string FailureDescription =>
    "ORDINAL subtraction might underflow a limit ordinal (that is, RHS might be too large)";

  public override string ShortDescription => "TODO";
}

public class DafnyLetSuchThanUniqueDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "the value of this let-such-that expression is uniquely determined";

  public override string FailureDescription =>
    "to be compilable, the value of a let-such-that expression must be uniquely determined";

  public override string ShortDescription => "let-such-that unique";
}

public class DafnyLetSuchThanExistsDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    "a value exists that satisfies this let-such-that expression";

  public override string FailureDescription =>
    "cannot establish the existence of LHS values that satisfy the such-that predicate";

  public override string ShortDescription => "let-such-that exists";
}

public class DafnyAssignmentShrinksDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"the assignment to {fieldName} always shrinks the set";

  public override string FailureDescription =>
    $"an assignment to {fieldName} is only allowed to shrink the set";

  public override string ShortDescription => "assignment shrinks"; // TODO: better

  private readonly string fieldName;

  public DafnyAssignmentShrinksDescription(string fieldName) {
    this.fieldName = fieldName;
  }
}

public class DafnyConversionIsNaturalDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{prefix}value to be converted is always a natural number";

  public override string FailureDescription =>
    $"{prefix}value to be converted might be bigger than every natural number";

  public override string ShortDescription => "converted value is natural";

  private readonly string prefix;

  public DafnyConversionIsNaturalDescription(string prefix) {
    this.prefix = prefix;
  }
}

public class DafnyConversionSatisfiesConstraintsDescription : DafnyAssertionDescription {
  public override string SuccessDescription =>
    $"{prefix}result of operation never violates {kind} constraints for '{name}'";

  public override string FailureDescription =>
    $"{prefix}result of operation might violate {kind} constraint for '{name}'";

  public override string ShortDescription => "conversion satisfies type constraints";

  private readonly string prefix;
  private readonly string kind;
  private readonly string name;

  public DafnyConversionSatisfiesConstraintsDescription(string prefix, string kind, string name) {
    this.prefix = prefix;
    this.kind = kind;
    this.name = name;
  }
}
