using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class SubsetTypeDecl : TypeSynonymDecl, RedirectingTypeDecl, ICanAutoRevealDependencies, ICanVerify {
  public override string WhatKind => "subset type";
  public readonly BoundVar Var;
  public readonly Expression Constraint;
  public enum WKind { CompiledZero, Compiled, Ghost, OptOut, Special }
  public readonly WKind WitnessKind;
  public Expression/*?*/ Witness;  // non-null iff WitnessKind is Compiled or Ghost
  [FilledInDuringResolution] public bool ConstraintIsCompilable;
  [FilledInDuringResolution] public bool CheckedIfConstraintIsCompilable = false; // Set to true lazily by the Resolver when the Resolver fills in "ConstraintIsCompilable".
  public SubsetTypeDecl(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module,
    BoundVar id, Expression constraint, WKind witnessKind, Expression witness,
    Attributes attributes)
    : base(rangeToken, name, characteristics, typeArgs, module, id.Type, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(module != null);
    Contract.Requires(id != null && id.Type != null);
    Contract.Requires(constraint != null);
    Contract.Requires((witnessKind == WKind.Compiled || witnessKind == WKind.Ghost) == (witness != null));
    Var = id;
    Constraint = constraint;
    Witness = witness;
    WitnessKind = witnessKind;
  }

  public override IEnumerable<INode> Children =>
    base.Children.Concat(new[] { Constraint }).Concat(
      Witness != null ? new[] { Witness } :
        Enumerable.Empty<INode>()
      );

  BoundVar RedirectingTypeDecl.Var => Var;
  Expression RedirectingTypeDecl.Constraint => Constraint;
  WKind RedirectingTypeDecl.WitnessKind => WitnessKind;
  Expression RedirectingTypeDecl.Witness => Witness;

  public override List<Type> ParentTypes(List<Type> typeArgs) {
    return new List<Type> { RhsWithArgument(typeArgs) };
  }
  public bool ShouldVerify => true; // This could be made more accurate
  public ModuleDefinition ContainingModule => EnclosingModuleDefinition;
  public virtual DafnySymbolKind Kind => DafnySymbolKind.Class;
  public virtual string GetDescription(DafnyOptions options) {
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
        var revealStmt0 = AutoRevealFunctionDependencies.BuildRevealStmt(func, Witness.Tok, EnclosingModuleDefinition);

        if (revealStmt0 is not null) {
          var newExpr = new StmtExpr(Witness.Tok, revealStmt0, Witness) {
            Type = Witness.Type
          };
          Witness = newExpr;
        }
      }

      foreach (var newFunc in Rewriter.GetEnumerator(func, func.EnclosingClass, new List<Expression>(), EnclosingModuleDefinition)) {
        var origExpr = Witness;
        var revealStmt = AutoRevealFunctionDependencies.BuildRevealStmt(newFunc.Function, Witness.Tok, EnclosingModuleDefinition);

        if (revealStmt is null) {
          continue;
        }

        var newExpr = new StmtExpr(Witness.Tok, revealStmt, origExpr) {
          Type = origExpr.Type
        };
        Witness = newExpr;
      }
    }
  }
}