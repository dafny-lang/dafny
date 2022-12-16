using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;

namespace Microsoft.Dafny.Auditor;

public record AssumptionDescription(string issue, string mitigation, bool isExplicit) {
  public static AssumptionDescription AxiomAttributeAssumption = new(
    issue: "Declaration has explicit [{:axiom}] attribute.",
    mitigation: "Provide a proof or test.",
    isExplicit: true);
  public static AssumptionDescription VerifyFalseAssumption = new(
    issue: "Declaration has [{:verify false}] attribute.",
    mitigation: "Remove and prove if possible.",
    isExplicit: false);
  public static AssumptionDescription ExternWithPrecondition = new(
    issue: "Declaration with [{:extern}] has a requires clause.",
    mitigation: "Test external caller (maybe with [/testContracts]).",
    isExplicit: false);
  public static AssumptionDescription ExternWithPostcondition = new(
    issue: "Declaration with [{:extern}] has a ensures clause.",
    mitigation: "Test external callee (maybe with [/testContracts]).",
    isExplicit: false);
  public static AssumptionDescription AssumeInBody = new(
    issue: "Definition has [assume] statement in body.",
    mitigation: "Replace with [assert] and prove or add [{:axiom}].",
    isExplicit: false);
  public static AssumptionDescription DecreasesStar = new(
    issue: "Method may not terminate (uses [decreases *]).",
    mitigation: "Provide a valid [decreases] clause.",
    isExplicit: false);
  public static AssumptionDescription TerminationFalse = new(
    issue: "Trait method calls may not terminate (uses [{:termination false}]).",
    mitigation: "Remove if possible.",
    isExplicit: false);

  public static AssumptionDescription NoBody(bool isGhost) {
    return new(
      issue: (isGhost ? "Ghost" : "Compiled") +
             " declaration has no body and has an ensures clause.",
      mitigation: "Provide a body or add [{:axiom}].",
      isExplicit: false);
  }
}

public record Assumption(Declaration decl, IEnumerable<AssumptionDescription> assumptions) {
  public IEnumerable<string> Warnings() {
    foreach (var desc in assumptions) {
      var tickIssue = AuditReport.UpdateVerbatim(desc.issue, "`", "`");
      var tickMitigation = AuditReport.UpdateVerbatim(desc.mitigation, "`", "`");
      yield return decl.Name + ": " + tickIssue + " Possible mitigation: " + tickMitigation;
    }
  }
}

/// <summary>
/// Combines AssumptionExtractor with AuditReport to generate a full
/// report from a program.
/// </summary>
public class ReportBuilder {
  public static AuditReport BuildReport(Program program) {
    AuditReport report = new();

    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        report.AddAssumptions(topLevelDecl, topLevelDecl.Assumptions());
        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var decl in topLevelDeclWithMembers.Members) {
          report.AddAssumptions(decl, decl.Assumptions());
        }
      }
    }

    return report;
  }
}
