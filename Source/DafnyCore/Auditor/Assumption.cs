using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;

namespace Microsoft.Dafny.Auditor;

public record AssumptionDescription(
  string Issue,
  string Mitigation,
  string MitigationIetf,
  bool IsExplicit
) {
  public static AssumptionDescription HasAxiomAttribute = new(
    Issue: "Declaration has explicit [{:axiom}] attribute.",
    Mitigation: "Provide a proof or test.",
    MitigationIetf: "SHOULD provide a proof or test.",
    IsExplicit: true);
  public static AssumptionDescription HasVerifyFalseAttribute = new(
    Issue: "Declaration has [{:verify false}] attribute.",
    Mitigation: "Remove [{:verify false}] attribute and prove if possible.",
    MitigationIetf: "MUST remove [{:verify false}] attribute and prove.",
    IsExplicit: false);
  public static AssumptionDescription ExternFunction = new(
    Issue: "Function with [{:extern}] attribute.",
    Mitigation: "Turn into a [method] with [modifies {}] and test thoroughly for lack of side effects.",
    MitigationIetf: "SHOULD use [method] with [modifies {}] instead.",
    IsExplicit: false);

  public static AssumptionDescription ExternWithPrecondition = new(
    Issue: "Declaration with [{:extern}] has a requires clause.",
    Mitigation: "Test any external callers (maybe with [/testContracts]).",
    MitigationIetf: "MUST test any external callers.",
    IsExplicit: false);
  public static AssumptionDescription ExternWithPostcondition = new(
    Issue: "Declaration with [{:extern}] has a ensures clause.",
    Mitigation: "Test external callee (maybe with [/testContracts]).",
    MitigationIetf: "MUST test external callee.",
    IsExplicit: false);

  public static AssumptionDescription AssumeStatement(bool hasAxiomAttribute) {
    return new(
      Issue:
      hasAxiomAttribute
        ? "Definition has [assume {:axiom}] statement in body."
        : "Definition has [assume] statement in body.",
      Mitigation:
        hasAxiomAttribute
          ? "Replace with [assert] and prove."
          : "Replace with [assert] and prove or add [{:axiom}].",
      MitigationIetf:
        hasAxiomAttribute
          ? "SHOULD replace with [assert] and prove."
          : "MUST replace with [assert] and prove or add [{:axiom}].",
      IsExplicit: false
    );
  }
  public static AssumptionDescription MayNotTerminate = new(
    Issue: "Method may not terminate (uses [decreases *]).",
    Mitigation: "Provide a valid [decreases] clause.",
    MitigationIetf: "SHOULD provide a valid [decreases] clause.",
    IsExplicit: false);
  public static AssumptionDescription HasTerminationFalseAttribute = new(
    Issue: "Trait method calls may not terminate (uses [{:termination false}]).",
    Mitigation: "Remove if possible.",
    MitigationIetf: "MUST remove [{:termination false}] or justify.",
    IsExplicit: false);
  public static AssumptionDescription HasAssumeCrossModuleTerminationAttribute = new(
    Issue: "Trait method calls may not terminate (uses [@AssumeCrossModuleTermination]).",
    Mitigation: "Remove if possible.",
    MitigationIetf: "MUST remove [@AssumeCrossModuleTermination] or justify.",
    IsExplicit: false);
  public static AssumptionDescription ForallWithoutBody = new(
    Issue: "Definition contains [forall] statement with no body.",
    Mitigation: "Provide a body.",
    MitigationIetf: "MUST provide a body.",
    IsExplicit: false);
  public static AssumptionDescription LoopWithoutBody = new(
    Issue: "Definition contains loop with no body.",
    Mitigation: "Provide a body.",
    MitigationIetf: "MUST provide a body.",
    IsExplicit: false);

  public static AssumptionDescription HasAssumeConcurrentAttribute(bool isModifies) {
    return new AssumptionDescription(
      Issue: (isModifies ? "Modifies" : "Reads") + " clause has [{:assume_concurrent}] attribute.",
      Mitigation: "Manually review and test in a concurrent setting.",
      MitigationIetf: "MUST manually review and test in a concurrent setting.",
      IsExplicit: true);
  }

  public static AssumptionDescription NoBody(bool isGhost) {
    return new(
      Issue: (isGhost ? "Ghost" : "Compiled") +
             " declaration has no body and has an ensures clause.",
      Mitigation: "Provide a body or add [{:axiom}].",
      MitigationIetf: (isGhost ? "MUST" : "SHOULD") + " provide a body or add [{:axiom}].",
      IsExplicit: false);
  }

  public static readonly AssumptionDescription AssertOnly = new(
    Issue: "Assertion has explicit temporary [{:only}] attribute.",
    Mitigation: "Remove the [{:only}] attribute.",
    MitigationIetf: "MUST remove the [{:only}] attribute.",
    IsExplicit: true
  );

  public static readonly AssumptionDescription MemberOnly = new(
    Issue: "Member has explicit temporary [{:only}] attribute.",
    Mitigation: "Remove the [{:only}] attribute.",
    MitigationIetf: "MUST remove the [{:only}] attribute.",
    IsExplicit: true
  );
}
public record Assumption(Declaration decl, IOrigin Tok, AssumptionDescription desc) {
  public string Warning() {
    var tickIssue = UpdateVerbatim(desc.Issue, "`", "`");
    var tickMitigation = UpdateVerbatim(desc.Mitigation, "`", "`");
    return decl.Name + ": " + tickIssue + " Possible mitigation: " + tickMitigation;
  }

  public static string UpdateVerbatim(string text, string beg, string end) {
    return text.Replace("[", beg).Replace("]", end);
  }
}
