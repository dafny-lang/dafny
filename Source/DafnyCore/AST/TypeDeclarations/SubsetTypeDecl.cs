#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class SubsetTypeDecl : TypeSynonymDecl, RedirectingTypeDecl, ICanAutoRevealDependencies, ICanVerify {
  public override string WhatKind => "subset type";
  public BoundVar Var;
  public Expression Constraint;
  public enum WKind { CompiledZero, Compiled, Ghost, OptOut, Special }
  public WKind WitnessKind;
  public Expression? Witness;  // non-null iff WitnessKind is Compiled or Ghost

  private bool? constraintIsCompilable = null;
  [FilledInDuringResolution]
  bool RedirectingTypeDecl.ConstraintIsCompilable {
    get {
      Contract.Assert(constraintIsCompilable != null);
      return (bool)constraintIsCompilable;
    }
    set {
      Contract.Assert(constraintIsCompilable == null);
      constraintIsCompilable = value;
    }
  }

  [SyntaxConstructor]
  public SubsetTypeDecl(IOrigin origin, Name nameNode, TypeParameterCharacteristics characteristics,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition,
    BoundVar var, Expression constraint, WKind witnessKind, Expression? witness,
    Attributes? attributes)
    : base(origin, nameNode, characteristics, typeArgs, enclosingModuleDefinition, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires((witnessKind == WKind.Compiled || witnessKind == WKind.Ghost) == (witness != null));
    Var = var;
    Constraint = constraint;
    Witness = witness;
    WitnessKind = witnessKind;
  }

  public override Type Rhs => Var.Type;

  public override IEnumerable<INode> Children =>
    base.Children.Concat(new[] { Constraint }).Concat(
      Witness != null ? new[] { Witness } :
        Enumerable.Empty<INode>()
      );

  BoundVar RedirectingTypeDecl.Var => Var;
  PreType? RedirectingTypeDecl.BasePreType => Var.PreType;
  Type RedirectingTypeDecl.BaseType => Var.Type;
  Expression RedirectingTypeDecl.Constraint => Constraint;
  WKind RedirectingTypeDecl.WitnessKind => WitnessKind;
  Expression? RedirectingTypeDecl.Witness => Witness;

  public override List<Type> ParentTypes(List<Type> typeArgs, bool includeTypeBounds) {
    return [RhsWithArgument(typeArgs)];
  }
  public bool ShouldVerify => true; // This could be made more accurate
  public ModuleDefinition ContainingModule => EnclosingModuleDefinition;
  public override SymbolKind? Kind => SymbolKind.Class;
  public override string GetDescription(DafnyOptions options) {
    return "subset type";
  }

  public void AutoRevealDependencies(AutoRevealFunctionDependencies Rewriter, DafnyOptions Options, ErrorReporter Reporter) {
    if (Witness is null) {
      return;
    }

    var expressions = Constraint.SubExpressions.ToList().Concat(Witness.SubExpressions.ToList());
    foreach (var expression in expressions) {
      if (expression is not FunctionCallExpr funcExpr) {
        continue;
      }

      var func = funcExpr.Function;

      if (!AutoRevealFunctionDependencies.IsRevealable(EnclosingModuleDefinition.AccessibleMembers, func)) {
        continue;
      }

      if (func.IsMadeImplicitlyOpaque(Options)) {
        var revealStmt0 = AutoRevealFunctionDependencies.BuildRevealStmt(func, Witness.Origin, EnclosingModuleDefinition);

        if (revealStmt0 is not null) {
          var newExpr = new StmtExpr(Witness.Origin, revealStmt0, Witness) {
            Type = Witness.Type
          };
          Witness = newExpr;
        }
      }

      foreach (var newFunc in Rewriter.GetEnumerator(func, func.EnclosingClass, new List<Expression>(), EnclosingModuleDefinition)) {
        var origExpr = Witness;
        var revealStmt = AutoRevealFunctionDependencies.BuildRevealStmt(newFunc.Function, Witness.Origin, EnclosingModuleDefinition);

        if (revealStmt is null) {
          continue;
        }

        var newExpr = new StmtExpr(Witness.Origin, revealStmt, origExpr) {
          Type = origExpr.Type
        };
        Witness = newExpr;
      }
    }
  }
}