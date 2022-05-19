using System.Collections.Generic;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny.ProofObligationDescription;

public abstract class ProofObligationDescription : Boogie.ProofObligationDescription {
  public abstract Expression GetAssertedExpr(DafnyOptions options);
}

// When there is no way to translate the asserted constraint in Dafny
public abstract class ProofObligationDescriptionNotInDafny : ProofObligationDescription {
  public override Expression GetAssertedExpr(DafnyOptions options) {
    return null;
  }
}

//// Arithmetic and logical operators, conversions

public class DivisorNonZero : ProofObligationDescription {
  public override string SuccessDescription =>
    "divisor is always non-zero.";

  public override string FailureDescription =>
    "possible division by zero";

  public override string ShortDescription => "non-zero divisor";

  private readonly Expression divisor;

  public DivisorNonZero(Expression divisor) {
    this.divisor = divisor;
  }

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return new BinaryExpr(divisor.tok, BinaryExpr.Opcode.Neq, divisor, new LiteralExpr(divisor.tok, 0));
  }
}

public class ShiftLowerBound : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "shift amount is always non-negative";

  public override string FailureDescription =>
    "shift amount must be non-negative";

  public override string ShortDescription => "shift lower bound";
}

public class ShiftUpperBound : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"shift amount is always within the width of the result ({width})";

  public override string FailureDescription =>
    $"shift amount must not exceed the width of the result ({width})";

  public override string ShortDescription => "shift upper bound";

  private readonly int width;

  public ShiftUpperBound(int width) {
    this.width = width;
  }
}

public class ConversionIsNatural : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{prefix}value to be converted is always a natural number";

  public override string FailureDescription =>
    $"{prefix}value to be converted might be bigger than every natural number";

  public override string ShortDescription => "converted value is natural";

  private readonly string prefix;

  public ConversionIsNatural(string prefix) {
    this.prefix = prefix;
  }
}

public class ConversionSatisfiesConstraints : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{prefix}result of operation never violates {kind} constraints for '{name}'";

  public override string FailureDescription =>
    $"{prefix}result of operation might violate {kind} constraint for '{name}'";

  public override string ShortDescription => "conversion satisfies type constraints";

  private readonly string prefix;
  private readonly string kind;
  private readonly string name;

  public ConversionSatisfiesConstraints(string prefix, string kind, string name) {
    this.prefix = prefix;
    this.kind = kind;
    this.name = name;
  }
}

public class OrdinalSubtractionIsNatural : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "RHS of ORDINAL subtraction is always a natural number";

  public override string FailureDescription =>
    "RHS of ORDINAL subtraction must be a natural number, but the given RHS might be larger";

  public override string ShortDescription => "ordinal subtraction is natural";
}

public class OrdinalSubtractionUnderflow : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "ORDINAL subtraction will never go below limit ordinal";

  public override string FailureDescription =>
    "ORDINAL subtraction might underflow a limit ordinal (that is, RHS might be too large)";

  public override string ShortDescription => "ordinal subtraction underflow";
}

public class CharOverflow : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "char addition will not overflow";

  public override string FailureDescription =>
    "char addition might overflow";

  public override string ShortDescription => "char overflow";
}

public class CharUnderflow : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "char subtraction will not underflow";

  public override string FailureDescription =>
    "char subtraction might underflow";

  public override string ShortDescription => "char underflow";
}

public class ConversionFit : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{prefix}{what} to be converted will always fit in {toType}";

  public override string FailureDescription =>
    $"{prefix}{what} to be converted might not fit in {toType}";

  public override string ShortDescription => "conversion fit";

  private readonly string prefix;
  private readonly string what;
  private readonly Type toType;

  public ConversionFit(string what, Type toType, string prefix = "") {
    this.prefix = prefix;
    this.what = what;
    this.toType = toType;
  }
}

public class NonNegative : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{what} is never negative";

  public override string FailureDescription =>
    $"{what} might be negative";

  public override string ShortDescription => "non-negative";

  private readonly string what;

  public NonNegative(string what) {
    this.what = what;
  }
}

public class ConversionPositive : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{prefix}{what} is always positive";

  public override string FailureDescription =>
    $"{prefix}a negative {what} cannot be converted to an {toType}";

  public override string ShortDescription => "conversion positive";

  private readonly string prefix;
  private readonly string what;
  private readonly Type toType;

  public ConversionPositive(string what, Type toType, string prefix = "") {
    this.prefix = prefix;
    this.what = what;
    this.toType = toType;
  }
}

public class IsInteger : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{prefix}the real-based number is an integer";

  public override string FailureDescription =>
    $"{prefix}the real-based number must be an integer (if you want truncation, apply .Floor to the real-based number)";

  public override string ShortDescription => "is integer";

  private readonly string prefix;

  public IsInteger(string prefix = "") {
    this.prefix = prefix;
  }
}

//// Object properties

public class NonNull : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{PluralSuccess}{what} object is never null";

  public override string FailureDescription =>
    $"{PluralFailure}{what} might be null";

  public override string ShortDescription => $"{what} non-null";
  private readonly string what;
  private bool plural;
  private string PluralSuccess => plural ? "each " : "";
  private string PluralFailure => plural ? "some " : "";

  public NonNull(string what, bool plural = false) {
    this.what = what;
    this.plural = plural;
  }
}

public class IsAllocated : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{PluralSuccess}{what} is always allocated{WhenSuffix}";

  public override string FailureDescription =>
    $"{PluralFailure}{what} might not be allocated{WhenSuffix}";

  public override string ShortDescription => $"{what} allocated";

  private readonly string what;
  [CanBeNull] private readonly string when;
  private bool plural;
  private string WhenSuffix => when is null ? "" : $" {when}";
  private string PluralSuccess => plural ? "each " : "";
  private string PluralFailure => plural ? "some " : "";

  public IsAllocated(string what, string when, bool plural = false) {
    this.what = what;
    this.when = when;
    this.plural = plural;
  }
}

public class IsOlderProofObligation : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription {
    get {
      var successOlder = olderParameterCount == 1 ? " is" : "s are";
      var successOther = otherParameterCount == 1 ? "the" : "any";
      return $"the 'older' parameter{successOlder} not newer than {successOther} other parameter when the predicate returns 'true'";
    }
  }

  public override string FailureDescription {
    get {
      var failureOlder = olderParameterCount == 1 ? "the" : "an";
      var failureOther =
        olderParameterCount == 1 && otherParameterCount == 1 ? "the other parameter" :
        otherParameterCount == 1 ? "the non-'older' parameter" :
        "all non-'older' parameters";
      return $"{failureOlder} 'older' parameter might be newer than {failureOther} when the predicate returns 'true'";
    }
  }

  public override string ShortDescription => $"older parameter{(2 <= olderParameterCount ? "s" : "")}";

  private readonly int olderParameterCount;
  private readonly int otherParameterCount;

  public IsOlderProofObligation(int olderParameterCount, int allParameterCount) {
    Contract.Requires(1 <= olderParameterCount);
    Contract.Requires(olderParameterCount <= allParameterCount);
    this.olderParameterCount = olderParameterCount;
    this.otherParameterCount = allParameterCount - olderParameterCount;
  }
}

//// Contract constraints

public class PreconditionSatisfied : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    customErrMsg is null
      ? "function precondition satisfied"
      : $"error is impossible: {customErrMsg}";

  public override string FailureDescription =>
    customErrMsg ?? "function precondition might not hold";

  public override string ShortDescription => "precondition";

  private readonly string customErrMsg;

  public PreconditionSatisfied([CanBeNull] string customErrMsg) {
    this.customErrMsg = customErrMsg;
  }
}

public class AssertStatement : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    customErrMsg is null
      ? "assertion always holds"
      : $"error is impossible: {customErrMsg}";

  public override string FailureDescription =>
    customErrMsg ?? "assertion might not hold";

  public override string ShortDescription => "assert statement";

  private readonly string customErrMsg;

  public AssertStatement([CanBeNull] string customErrMsg) {
    this.customErrMsg = customErrMsg;
  }
}

public class LoopInvariant : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    customErrMsg is null
      ? "loop invariant always holds"
      : $"error is impossible: {customErrMsg}";

  public override string FailureDescription =>
    customErrMsg ?? "loop invariant violation";

  public override string ShortDescription => "loop invariant";

  private readonly string customErrMsg;

  public LoopInvariant([CanBeNull] string customErrMsg) {
    this.customErrMsg = customErrMsg;
  }
}

public class CalculationStep : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "the calculation step between the previous line and this line always holds";

  public override string FailureDescription =>
    "the calculation step between the previous line and this line might not hold";

  public override string ShortDescription => "calc step";
}

public class EnsuresStronger : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "the method provides a postcondition equal to or more detailed than in its parent trait";

  public override string FailureDescription =>
    "the method must provide an equal or more detailed postcondition than in its parent trait";

  public override string ShortDescription => "ensures stronger";
}

public class RequiresWeaker : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "the method provides a precondition equal to or more permissive than in its parent trait";

  public override string FailureDescription =>
    "the method must provide an equal or more permissive precondition than in its parent trait";

  public override string ShortDescription => "requires weaker";
}

public class ForallPostcondition : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "postcondition of forall statement always holds";

  public override string FailureDescription =>
    "possible violation of postcondition of forall statement";

  public override string ShortDescription => "forall ensures";
}

public class YieldEnsures : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "yield-ensures condition always holds";

  public override string FailureDescription =>
    "possible violation of yield-ensures condition";

  public override string ShortDescription => "yield ensures";
}

public class TraitFrame : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    isModify
      ? $"{whatKind} abides by trait context's modifies clause"
      : $"{whatKind} abides by trait context's reads clause";

  public override string FailureDescription =>
    isModify
      ? $"{whatKind} might modify an object not in the parent trait context's modifies clause"
      : $"{whatKind} might read an object not in the parent trait context's reads clause";

  public override string ShortDescription =>
    isModify ? "trait modifies" : "trait reads";

  private readonly string whatKind;
  private bool isModify;

  public TraitFrame(string whatKind, bool isModify) {
    this.whatKind = whatKind;
    this.isModify = isModify;
  }
}

public class TraitDecreases : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{whatKind}'s decreases clause is below or equal to that in the trait";

  public override string FailureDescription =>
    $"{whatKind}'s (possibly automatically generated) decreases clause must be below or equal to that in the trait";

  public override string ShortDescription => "trait decreases";

  private readonly string whatKind;

  public TraitDecreases(string whatKind) {
    this.whatKind = whatKind;
  }
}

public class FrameSubset : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    isWrite
      ? $"{whatKind} is allowed by context's modifies clause"
      : $"sufficient reads clause to {whatKind}";

  public override string FailureDescription =>
    isWrite
      ? $"{whatKind} might violate context's modifies clause"
      : $"insufficient reads clause to {whatKind}";

  public override string ShortDescription => "frame subset";

  private readonly string whatKind;
  private readonly bool isWrite;

  public FrameSubset(string whatKind, bool isWrite) {
    this.whatKind = whatKind;
    this.isWrite = isWrite;
  }
}

public class FrameDereferenceNonNull : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "frame expression does not dereference null";

  public override string FailureDescription =>
    "frame expression might dereference null";

  public override string ShortDescription => "frame dereference";
}

public class Terminates : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "loop or recursion terminates";

  public override string FailureDescription =>
    (inferredDescreases
      ? ("cannot prove termination; try supplying a decreases clause" + (isLoop ? " for the loop" : ""))
      : $"decreases {FormDescription} might not decrease") +
    (hint is null ? "" : $" ({hint})");

  public override string ShortDescription => "termination";

  private readonly bool inferredDescreases;
  private readonly bool isLoop;
  private readonly string hint;
  private string FormDescription => isLoop ? "expression" : "clause";

  public Terminates(bool inferredDescreases, bool isLoop, string hint = null) {
    this.inferredDescreases = inferredDescreases;
    this.isLoop = isLoop;
    this.hint = hint;
  }
}

public class DecreasesBoundedBelow : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"decreases {component} is bounded below by {zeroStr}";

  public override string FailureDescription =>
    $"decreases {component} must be bounded below by {zeroStr}{suffix}";

  public override string ShortDescription => "bounded decreases expression";

  private string component => N == 1 ? "expression" : $"expression at index {k}";
  private readonly string zeroStr;
  private readonly string suffix;
  private readonly int N, k;

  public DecreasesBoundedBelow(int N, int k, string zeroStr, string suffix) {
    this.N = N;
    this.k = k;
    this.zeroStr = zeroStr;
    this.suffix = suffix;
  }
}

public class Modifiable : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{description} is in the enclosing context's modifies clause";

  public override string FailureDescription =>
    $"assignment might update {description} not in the enclosing context's modifies clause";

  public override string ShortDescription => "modifiable";

  private readonly string description;

  public Modifiable(string description) {
    this.description = description;
  }
}

public class FunctionContractOverride : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"the function provides an equal or {RestrictionDesc} than in its parent trait";

  public override string FailureDescription =>
    $"the function must provide an equal or {RestrictionDesc} than in its parent trait";

  public override string ShortDescription => "contract override valid";

  private readonly bool isEnsures;
  private string RestrictionDesc =>
    isEnsures ? "more detailed postcondition" : "more permissive precondition";

  public FunctionContractOverride(bool isEnsures) {
    this.isEnsures = isEnsures;
  }
}

//// Structural constraints

public class MatchIsComplete : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"match {matchForm} covers all cases";

  public override string FailureDescription =>
    $"missing case in match {matchForm}: {missing}";

  public override string ShortDescription => "match complete";

  private readonly string matchForm;
  private readonly string missing;
  public MatchIsComplete(string matchForm, string missing) {
    this.matchForm = matchForm;
    this.missing = missing;
  }
}

public class AlternativeIsComplete : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"alternative cases cover all possibilties";

  public override string FailureDescription =>
    $"alternative cases fail to cover all possibilties";

  public override string ShortDescription => "alternative complete";
}

public class PatternShapeIsValid : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"RHS will always match the pattern '{ctorName}'";

  public override string FailureDescription =>
    $"RHS is not certain to look like the pattern '{ctorName}'";

  public override string ShortDescription => "pattern shape valid";

  private readonly string ctorName;

  public PatternShapeIsValid(string ctorName) {
    this.ctorName = ctorName;
  }
}

public class ValidConstructorNames : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"source of datatype update is constructed by {ctorNames}";

  public override string FailureDescription =>
    $"source of datatype update must be constructed by {ctorNames}";

  public override string ShortDescription => "valid constructor names";

  private readonly string ctorNames;

  public ValidConstructorNames(string ctorNames) {
    this.ctorNames = ctorNames;
  }
}

public class DestructorValid : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"destructor '{dtorName}' is only applied to datatype values constructed by {ctorNames}";

  public override string FailureDescription =>
    $"destructor '{dtorName}' can only be applied to datatype values constructed by {ctorNames}";

  public override string ShortDescription => "destructor valid";

  private readonly string dtorName;
  private readonly string ctorNames;

  public DestructorValid(string dtorName, string ctorNames) {
    this.dtorName = dtorName;
    this.ctorNames = ctorNames;
  }
}

public class NotGhostVariant : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"in a compiled context, {subject} is not applied to a datatype value of a ghost variant (ghost constructor {ctorNames})";

  public override string FailureDescription =>
    $"in a compiled context, {subject} cannot be applied to a datatype value of a ghost variant (ghost constructor {ctorNames})";

  public override string ShortDescription => "not ghost variant";

  private readonly string subject;
  private readonly string ctorNames;

  public NotGhostVariant(string subject, List<DatatypeCtor> ctors) {
    this.subject = subject;
    this.ctorNames = DatatypeDestructor.PrintableCtorNameList(ctors, "or");
  }

  public NotGhostVariant(string whatKind, string dtorNames, List<DatatypeCtor> ctors) {
    this.subject = $"{whatKind} {dtorNames}";
    this.ctorNames = DatatypeDestructor.PrintableCtorNameList(ctors, "or");
  }
}


//// Misc constraints

public class IndicesInDomain : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"all {objType} indices are in the domain of the initialization function";

  public override string FailureDescription =>
    $"all {objType} indices must be in the domain of the initialization function";

  public override string ShortDescription => "indices in domain";

  private readonly string objType;

  public IndicesInDomain(string objType) {
    this.objType = objType;
  }
}

public class SubrangeCheck : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    isSubset
      ? $"value always satisfies the subset constraints of '{targetType}'"
      : $"value of expression (of type '{sourceType}') is always an instance of type '{targetType}'";

  public override string FailureDescription => BaseFailureDescription + (isCertain ? "" : cause);

  public override string ShortDescription => "subrange check";

  private string BaseFailureDescription =>
    isSubset
      ? $"{prefix}value does not satisfy the subset constraints of '{targetType}'"
      : $"{prefix}value of expression (of type '{sourceType}') is not known to be an instance of type '{targetType}'" +
        (isCertain ? ", because it might be null" : "");

  private readonly string prefix;
  private readonly string sourceType;
  private readonly string targetType;
  private readonly bool isSubset;
  private readonly bool isCertain;
  private readonly string cause;

  public SubrangeCheck(string prefix, string sourceType, string targetType, bool isSubset, bool isCertain, [CanBeNull] string cause) {
    this.prefix = prefix;
    this.sourceType = sourceType;
    this.targetType = targetType;
    this.isSubset = isSubset;
    this.isCertain = isCertain;
    this.cause = cause is null ? "" : $" (possible cause: {cause})";
  }
}

public class WitnessCheck : ProofObligationDescriptionNotInDafny {
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

  public WitnessCheck(string witnessString) {
    this.witnessString = witnessString;
  }
}

public class PrefixEqualityLimit : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "prefix-equality limit is at least 0";

  public override string FailureDescription =>
    "prefix-equality limit must be at least 0";

  public override string ShortDescription => "prefix-equality limit";
}

public class ForRangeBoundsValid : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "lower bound does not exceed upper bound";

  public override string FailureDescription =>
    "lower bound must not exceed upper bound";

  public override string ShortDescription => "for range bounds";
}

public class ForRangeAssignable : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "entire range is assignable to index variable";

  public override string FailureDescription =>
    $"entire range must be assignable to index variable, but some {desc.FailureDescription}";

  public override string ShortDescription => "for range assignable";

  private readonly ProofObligationDescription desc;

  public ForRangeAssignable(ProofObligationDescription desc) {
    this.desc = desc;
  }
}

public class ValidInRecursion : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{what} is valid in recursive setting";

  public override string FailureDescription =>
    $"cannot use {what} in recursive setting.{hint ?? ""}";

  public override string ShortDescription => "valid in recursion";

  private readonly string what;
  private readonly string hint;

  public ValidInRecursion(string what, string hint) {
    this.what = what;
    this.hint = hint;
  }
}

public class IsNonRecursive : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "default value is non-recursive";

  public override string FailureDescription =>
    "default-value expression is not allowed to involve recursive or mutually recursive calls";

  public override string ShortDescription => "default nonrecursive";
}

public class ForallLHSUnique : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "left-hand sides of forall-statement bound variables are unique";

  public override string FailureDescription =>
    "left-hand sides for different forall-statement bound variables might refer to the same location";

  public override string ShortDescription => "forall bound unique";
}

public class ElementInDomain : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "element is in domain";

  public override string FailureDescription =>
    "element might not be in domain";

  public override string ShortDescription => "element in domain";
}

public class DefiniteAssignment : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"{what}, which is subject to definite-assignment rules, is always initialized {where}";

  public override string FailureDescription =>
    $"{what}, which is subject to definite-assignment rules, might be uninitialized {where}";

  public override string ShortDescription => "definite assignment";

  private readonly string what;
  private readonly string where;

  public DefiniteAssignment(string what, string where) {
    this.what = what;
    this.where = where;
  }
}

public class InRange : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription => $"{what} in range";

  public override string FailureDescription => $"{what} out of range";

  public override string ShortDescription => "in range";

  private readonly string what;

  public InRange(string what) {
    this.what = what;
  }
}

public class SequenceSelectRangeValid : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"upper bound within range of {what}";

  public override string FailureDescription =>
    $"upper bound below lower bound or above length of {what}";

  public override string ShortDescription => "sequence select range valid";

  private readonly string what;

  public SequenceSelectRangeValid(string what) {
    this.what = what;
  }
}

public class ComprehensionNoAlias : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "key expressions refer to unique values";

  public override string FailureDescription =>
    "key expressions might be referring to the same value";

  public override string ShortDescription => "unique key expressions";
}

public class DistinctLHS : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"left-hand sides {lhsa} and {lhsb} are distinct";

  public override string FailureDescription =>
    $"{when}left-hand sides {lhsa} and {lhsb} {might}refer to the same location{whenSuffix}";

  public override string ShortDescription => "distinct lhs";

  private readonly string lhsa;
  private readonly string lhsb;
  private readonly string might;
  private readonly string when;
  private readonly string whenSuffix;

  public DistinctLHS(string lhsa, string lhsb, bool useMight, bool useWhen) {
    this.lhsa = lhsa;
    this.lhsb = lhsb;
    this.might = useMight ? "might " : "";
    this.when = useWhen ? "when " : "";
    this.whenSuffix = useWhen ? ", they must be assigned the same value" : "";
  }
}

public class ArrayInitSizeValid : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"given array size agrees with the number of expressions in the initializing display ({size})";

  public override string FailureDescription =>
    $"given array size must agree with the number of expressions in the initializing display ({size})";

  public override string ShortDescription => "array initializer size";

  private readonly int size;

  public ArrayInitSizeValid(int size) {
    this.size = size;
  }
}

public class ArrayInitEmpty : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "array initializer has empty size";

  public override string FailureDescription =>
    $"unless an initializer is provided for the array elements, a new array of '{typeDesc}' must have empty size";

  public override string ShortDescription => "array initializer empty";

  private readonly string typeDesc;

  public ArrayInitEmpty(string typeDesc) {
    this.typeDesc = typeDesc;
  }
}

public class LetSuchThanUnique : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "the value of this let-such-that expression is uniquely determined";

  public override string FailureDescription =>
    "to be compilable, the value of a let-such-that expression must be uniquely determined";

  public override string ShortDescription => "let-such-that unique";
}

public class LetSuchThatExists : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    "a value exists that satisfies this let-such-that expression";

  public override string FailureDescription =>
    "cannot establish the existence of LHS values that satisfy the such-that predicate";

  public override string ShortDescription => "let-such-that exists";
}

public class AssignmentShrinks : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"the assignment to {fieldName} always shrinks the set";

  public override string FailureDescription =>
    $"an assignment to {fieldName} is only allowed to shrink the set";

  public override string ShortDescription => "assignment shrinks";

  private readonly string fieldName;

  public AssignmentShrinks(string fieldName) {
    this.fieldName = fieldName;
  }
}

public class BoilerplateTriple : ProofObligationDescriptionNotInDafny {
  public override string SuccessDescription =>
    $"error is impossible: {msg}";

  public override string FailureDescription => msg;

  public override string ShortDescription => "boilerplate triple";

  private readonly string msg;

  public BoilerplateTriple(string msg) {
    this.msg = msg;
  }
}
