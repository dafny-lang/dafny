using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;

namespace Microsoft.Dafny.Auditor;

public record AssumptionDescription(
  string issue,
  string mitigation,
  string mitigationIETF,
  bool isExplicit,
  bool allowedInLibraries
) {
  public static AssumptionDescription HasAxiomAttribute = new(
    issue: "Declaration has explicit [{:axiom}] attribute.",
    mitigation: "Provide a proof or test.",
    mitigationIETF: "SHOULD provide a proof or test.",
    isExplicit: true,
    allowedInLibraries: true);
  public static AssumptionDescription HasVerifyFalseAttribute = new(
    issue: "Declaration has [{:verify false}] attribute.",
    mitigation: "Remove [{:verify false}] attribute and prove if possible.",
    mitigationIETF: "MUST remove [{:verify false}] attribute and prove.",
    isExplicit: false,
    allowedInLibraries: false);
  public static AssumptionDescription ExternFunction = new(
    issue: "Function with [{:extern}] attribute.",
    mitigation: "Turn into a [method] or test thoroughly for lack of side effects.",
    mitigationIETF: "SHOULD use [method] instead.",
    isExplicit: false,
    allowedInLibraries: false);
  public static AssumptionDescription ExternWithPrecondition = new(
    issue: "Declaration with [{:extern}] has a requires clause.",
    mitigation: "Test any external callers (maybe with [/testContracts]).",
    mitigationIETF: "MUST test any external callers.",
    isExplicit: false,
    allowedInLibraries: false);
  public static AssumptionDescription ExternWithPostcondition = new(
    issue: "Declaration with [{:extern}] has a ensures clause.",
    mitigation: "Test external callee (maybe with [/testContracts]).",
    mitigationIETF: "MUST test external callee.",
    isExplicit: false,
    allowedInLibraries: false);
  public static AssumptionDescription AssumeStatement(bool hasAxiomAttribute) {
    return new(
      issue: "Definition has [assume] statement in body.",
      mitigation:
        hasAxiomAttribute
          ? "Replace with [assert] and prove."
          : "Replace with [assert] and prove or add [{:axiom}].",
      mitigationIETF:
        hasAxiomAttribute
          ? "SHOULD replace with [assert] and prove."
          : "MUST replace with [assert] and prove or add [{:axiom}].",
      isExplicit: false,
      allowedInLibraries: false
    );
  }
  public static AssumptionDescription MayNotTerminate = new(
    issue: "Method may not terminate (uses [decreases *]).",
    mitigation: "Provide a valid [decreases] clause.",
    mitigationIETF: "SHOULD provide a valid [decreases] clause.",
    isExplicit: false,
    // This isn't unsound but it's hard to imagine useful libraries
    // with non-terminating methods. If we ever want to offer something like a
    // top-level event loop driver we can revisit.
    allowedInLibraries: false);
  public static AssumptionDescription HasTerminationFalseAttribute = new(
    issue: "Trait method calls may not terminate (uses [{:termination false}]).",
    mitigation: "Remove if possible.",
    mitigationIETF: "MUST remove or justify.",
    isExplicit: false,
    allowedInLibraries: false);
  public static AssumptionDescription ForallWithoutBody = new(
    issue: "Definition contains [forall] statement with no body.",
    mitigation: "Provide a body.",
    mitigationIETF: "MUST provide a body.",
    isExplicit: false,
    allowedInLibraries: false);
  public static AssumptionDescription LoopWithoutBody = new(
    issue: "Definition contains loop with no body.",
    mitigation: "Provide a body.",
    mitigationIETF: "MUST provide a body.",
    isExplicit: false,
    allowedInLibraries: false);
  public static AssumptionDescription HasConcurrentAttribute = new(
    issue: "Declaration has [{:concurrent}] attribute.",
    mitigation: "Manually review and test in a concurrent setting.",
    mitigationIETF: "MUST manually review and test in a concurrent setting.",
    isExplicit: false,
    allowedInLibraries: false);

  public static AssumptionDescription NoBody(bool isGhost) {
    return new(
      issue: (isGhost ? "Ghost" : "Compiled") +
             " declaration has no body and has an ensures clause.",
      mitigation: "Provide a body or add [{:axiom}].",
      mitigationIETF: (isGhost ? "MUST" : "SHOULD") + " provide a body or add [{:axiom}].",
      isExplicit: false,
      allowedInLibraries: false);
  }

  public static AssumptionDescription AssertOnly = new(
    issue: "Assertion has explicit temporary [{:only}] attribute.",
    mitigation: "Remove the [{:only}] attribute",
    mitigationIETF: "Must remove the [{:only}] attribute",
    isExplicit: true,
    allowedInLibraries: false
  );
}
public record Assumption(Declaration decl, IToken tok, AssumptionDescription desc) {
  public string Warning() {
    var tickIssue = UpdateVerbatim(desc.issue, "`", "`");
    var tickMitigation = UpdateVerbatim(desc.mitigation, "`", "`");
    return decl.Name + ": " + tickIssue + " Possible mitigation: " + tickMitigation;
  }

  public static string UpdateVerbatim(string text, string beg, string end) {
    return text.Replace("[", beg).Replace("]", end);
  }
}
