using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.Auditor;

public record AssumptionDescription(string issue, string mitigation);

/// <summary>
/// A set of assumption-related properties of a Dafny entity. Certain
/// combinations of these properties classify the entity as containing
/// an assumption.
/// </summary>
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
        new(
          issue: "Declaration has explicit [{:axiom}] attribute.",
          mitigation: "Provide a proof, test, or other justification.")
      };
    }

    List<AssumptionDescription> descs = new();

    if (IsCallable && MissingBody) {
      descs.Add(
        new(
          issue: (IsGhost ? "Ghost" : "Compiled") +
            " declaration has no body" +
            (EnsuresClauses is null ? "." : " and has an ensures clause."),
          mitigation: "Provide a body or add [{:axiom}]."));
    }
    if (IsCallable && HasExternAttribute && RequiresClauses is not null) {
      descs.Add(
        new(
          issue: "Declaration with [{:extern}] has a requires clause.",
          mitigation: "Test external caller (maybe with [/testContracts]) or justify."));
    }
    if (IsCallable && HasExternAttribute && EnsuresClauses is not null) {
      descs.Add(
        new(
          issue: "Declaration with [{:extern}] has a ensures clause.",
          mitigation: "Test external callee (maybe with [/testContracts]) or justify."));
    }
    if (IsCallable && HasAssumeInBody) {
      descs.Add(
        new(
          issue: "Definition has [assume] statement in body.",
          mitigation: "Replace with [assert] and prove or add [{:axiom}]."));
    }
    if (IsCallable && MayNotTerminate) {
      descs.Add(
        new(
          issue: "Method may not terminate (uses [decreases *]).",
          mitigation: "Provide a valid [decreases] clause or justify the absence."));
    }
    if (IsTrait && MayNotTerminate) {
      descs.Add(
        new(
          issue: "Trait method calls may not terminate (uses [{:termination false}]).",
          mitigation: "Remove or justify."));
    }
    if (HasVerifyFalseAttribute) {
      descs.Add(
        new(
          issue: "Definition has [{:verify false}] attribute.",
          mitigation: "Remove and prove or justify."));
    }

    return descs;
  }
}

public record Assumption(Declaration decl, AssumptionProperties props) {
  public IEnumerable<string> Warnings() {
    foreach (var (problem, mitigation) in props.Description()) {
      yield return decl.Name + ": " + problem + " Possible mitigation: " + mitigation;
    }
  }
}

/// <summary>
/// Extracts all assumptions from a declaration.
/// </summary>
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

/// <summary>
/// Combines AssumptionExtractor with AuditReport to generate a full
/// report from a program.
/// </summary>
public class ReportBuilder {
  public static AuditReport BuildReport(Program program) {
    AuditReport report = new();

    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        report.AddAssumptions(topLevelDecl, AssumptionExtractor.GetAssumptionTags(topLevelDecl));
        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var decl in topLevelDeclWithMembers.Members) {
          report.AddAssumptions(decl, AssumptionExtractor.GetAssumptionTags(decl));
        }
      }
    }

    return report;
  }
}
