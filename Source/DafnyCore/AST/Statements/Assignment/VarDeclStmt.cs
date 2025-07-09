#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class VarDeclStmt : Statement, ICloneable<VarDeclStmt>, ICanFormat {
  public List<LocalVariable> Locals;
  public ConcreteAssignStatement? Assign;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Locals));
    Contract.Invariant(Locals.Count != 0);
  }

  public VarDeclStmt Clone(Cloner cloner) {
    return new VarDeclStmt(cloner, this);
  }

  public VarDeclStmt(Cloner cloner, VarDeclStmt original) : base(cloner, original) {
    Locals = original.Locals.Select(l => cloner.CloneLocalVariable(l, false)).ToList();
    Assign = (ConcreteAssignStatement)cloner.CloneStmt(original.Assign, false);
  }

  [SyntaxConstructor]
  public VarDeclStmt(IOrigin origin, List<LocalVariable> locals, ConcreteAssignStatement? assign, Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(locals.Count != 0);

    Locals = locals;
    Assign = assign;
  }

  public override IEnumerable<Statement> SubStatements {
    get { if (Assign != null) { yield return Assign; } }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var v in Locals) {
        foreach (var e in Attributes.SubExpressions(v.Attributes)) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<INode> Children => Locals.Concat<Node>(SubStatements);

  public override IEnumerable<INode> PreResolveChildren => Children;
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var result = formatter.SetIndentVarDeclStmt(indentBefore, OwnedTokens, false, false);
    return Assign != null ? formatter.SetIndentUpdateStmt(Assign, indentBefore, true) : result;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    if (mustBeErasable) {
      foreach (var local in Locals) {
        // a local variable in a specification-only context might as well be ghost
        local.MakeGhost();
      }
    }
    if (Assign != null) {
      Assign.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext, proofContext, allowAssumptionVariables, inConstructorInitializationPhase);
    }
    IsGhost = (Assign == null || Assign.IsGhost) && Locals.All(v => v.IsGhost);

    // Check on "assumption" variables
    foreach (var local in Locals) {
      if (Attributes.Contains(local.Attributes, "assumption")) {
        if (allowAssumptionVariables) {
          if (!local.Type.IsBoolType) {
            reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_assumption_var_must_be_bool, local.Origin,
              "assumption variable must be of type 'bool'");
          }
          if (!local.IsGhost) {
            reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_assumption_var_must_be_ghost, local.Origin,
              "assumption variable must be ghost");
          }
        } else {
          reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_assumption_var_must_be_in_method, local.Origin,
            "assumption variable can only be declared in a method");
        }
      }
    }
  }
}