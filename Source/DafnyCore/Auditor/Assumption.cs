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
  public static AssumptionDescription ExternWithRequires = new(
    issue: "Declaration with [{:extern}] has a requires clause.",
    mitigation: "Test external caller (maybe with [/testContracts]).",
    isExplicit: false);
  public static AssumptionDescription ExternWithEnsures = new(
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


/// <summary>
/// A set of assumption-related properties of a Dafny entity. Certain
/// combinations of these properties classify the entity as containing
/// an assumption.
/// </summary>
/*
public struct AssumptionProperties {
  internal bool IsGhost;
  internal bool IsSubsetType;
  internal bool IsCallable;
  internal bool IsTrait;
  internal bool MissingBody;
  internal bool HasAxiomAttribute;
  internal bool HasExternAttribute;
  internal bool HasVerifyFalseAttribute;
  internal bool HasAssumeInBody;
  internal bool MayNotTerminate;
  internal IEnumerable<AttributedExpression> RequiresClauses; // non-null implies one or more elements
  internal IEnumerable<AttributedExpression> EnsuresClauses; // non-null implies one or more elements

  /// <summary>
  /// Determines whether the set of properties constitutes an assumption.
  /// </summary>
  /// <returns>whether this entity contains assumptions</returns>
  public bool HasAssumptions() {
    return HasAxiomAttribute ||
           (IsCallable &&
            (((EnsuresClauses is not null || RequiresClauses is not null) &&
              (MissingBody || HasExternAttribute)) ||
             HasAssumeInBody)) ||
           (MayNotTerminate && (IsCallable || IsTrait));
  }

  /// <summary>
  /// Describe all of the assumptions this entity makes.
  /// </summary>
  /// <returns>a list of (assumption, mitigation) pairs</returns>
  public IEnumerable<AssumptionDescription> Description() {
    if (HasAxiomAttribute) {
      return new List<AssumptionDescription>{
        AssumptionDescription.AxiomAttributeAssumption
      };
    }

    List<AssumptionDescription> descs = new();

    if (IsCallable && MissingBody) {
      descs.Add(AssumptionDescription.NoBody(EnsuresClauses is not null, IsGhost));
    }
    if (IsCallable && HasExternAttribute && RequiresClauses is not null) {
      descs.Add(AssumptionDescription.ExternWithRequires);
    }
    if (IsCallable && HasExternAttribute && EnsuresClauses is not null) {
      descs.Add(AssumptionDescription.ExternWithEnsures);
    }
    if (IsCallable && HasAssumeInBody) {
      descs.Add(AssumptionDescription.AssumeInBody);
    }
    if (IsCallable && MayNotTerminate) {
      descs.Add(AssumptionDescription.DecreasesStar);
    }
    if (IsTrait && MayNotTerminate) {
      descs.Add(AssumptionDescription.TerminationFalse);
    }
    if (HasVerifyFalseAttribute) {
      descs.Add(AssumptionDescription.VerifyFalseAssumption);
    }

    return descs;
  }
}
*/

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
/// Extracts all assumptions from a declaration.
/// </summary>
/*
public class AssumptionExtractor {

  private static bool StmtContainsAssume(Statement s) {
    if (s is null) {
      return false;
    }

    return s is AssumeStmt ||
           s.SubStatements.Any(StmtContainsAssume) |
           s.SubExpressions.Any(ExprContainsAssume);
  }

  private static bool ExprContainsAssume(Expression e) {
    if (e is null) {
      return false;
    }

    return (e is StmtExpr es && StmtContainsAssume(es.S)) ||
           e.SubExpressions.Any(ExprContainsAssume);
  }

  public static AssumptionProperties GetAssumptionTags(Declaration decl) {
    var props = new AssumptionProperties();

    props.IsSubsetType = decl is SubsetTypeDecl;

    if (decl is ICallable c) {
      props.IsCallable = true;
      if (decl is Method m) {
        if (m.Body is null) {
          props.MissingBody = true;
        } else {
          props.HasAssumeInBody = StmtContainsAssume(m.Body);
        }

        if (m.Req is not null && m.Req.Count != 0) {
          props.RequiresClauses = m.Req;
        }

        if (m.Ens is not null && m.Ens.Count != 0) {
          props.EnsuresClauses = m.Ens;
        }

        props.MayNotTerminate = m.AllowsNontermination;
        props.IsGhost = m.IsGhost;
      } else if (decl is Function f) {
        if (f.Body is null) {
          props.MissingBody = true;
        } else {
          props.HasAssumeInBody = ExprContainsAssume(f.Body);
        }

        if (f.Req is not null && f.Req.Count != 0) {
          props.RequiresClauses = f.Req;
        }

        if (f.Ens is not null && f.Ens.Count != 0) {
          props.EnsuresClauses = f.Ens;
        }
        props.IsGhost = f.IsGhost;
      }
    } else if (decl is TraitDecl) {
      props.IsTrait = true;
      props.MayNotTerminate =
        Attributes.Find(decl.Attributes, "termination") is Attributes ta &&
        ta.Args.Count == 1 &&
        Expression.IsBoolLiteral(ta.Args[0], out var termination) &&
        termination == false;
    }

    props.HasExternAttribute = Attributes.Contains(decl.Attributes, "extern");
    props.HasAxiomAttribute = Attributes.Contains(decl.Attributes, "axiom");

    props.HasVerifyFalseAttribute =
      Attributes.Find(decl.Attributes, "verify") is Attributes va &&
      va.Args.Count == 1 &&
      Expression.IsBoolLiteral(va.Args[0], out var verify) &&
      verify == false;

    return props;
  }
}
*/

/// <summary>
/// Combines AssumptionExtractor with AuditReport to generate a full
/// report from a program.
/// </summary>
public class ReportBuilder {
  public static AuditReport BuildReport(Program program) {
    AuditReport report = new();

    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        report.AddAssumptions(topLevelDecl, topLevelDecl.Assumptions);
        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var decl in topLevelDeclWithMembers.Members) {
          report.AddAssumptions(decl, decl.Assumptions);
        }
      }
    }

    return report;
  }
}
