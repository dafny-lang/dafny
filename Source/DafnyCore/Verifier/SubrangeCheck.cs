using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class SubrangeCheck : ProofObligationDescription {
  public override DafnyDiagnostic GetDiagnostic(TokenRange range) {
    if (!isSubset && !isCertain) {
      return new DafnyDiagnostic(MessageSource.Verifier, "NotInstanceOfType", range, [sourceType, targetType],
        ErrorLevel.Error, []);
    }
    return null;
  }

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
  private readonly Expression check;

  public SubrangeCheck(
    string prefix, string sourceType, string targetType,
    bool isSubset, bool isCertain, [CanBeNull] string cause, [CanBeNull] Expression check
  ) {
    this.prefix = prefix;
    this.sourceType = sourceType;
    this.targetType = targetType;
    this.isSubset = isSubset;
    this.isCertain = isCertain;
    this.cause = cause is null ? "" : $" (possible cause: {cause})";
    this.check = check;
  }

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return check;
  }
}