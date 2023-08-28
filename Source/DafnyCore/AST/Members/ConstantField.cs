using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ConstantField : SpecialField, ICallable, ICanAutoRevealDependencies, ICanVerify {
  public override string WhatKind => "const field";
  public Expression Rhs;

  public override bool IsOpaque { get; }

  public ConstantField(RangeToken rangeToken, Name name, Expression/*?*/ rhs, bool hasStaticKeyword, bool isGhost, bool isOpaque, Type type, Attributes attributes)
    : base(rangeToken, name, ID.UseIdParam, NonglobalVariable.SanitizeName(name.Value), hasStaticKeyword, isGhost, false, false, type, attributes) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    this.Rhs = rhs;
    this.IsOpaque = isOpaque;
  }

  public override bool CanBeRevealed() {
    return true;
  }

  public new bool IsGhost { get { return this.isGhost; } }
  public List<TypeParameter> TypeArgs { get { return new List<TypeParameter>(); } }
  public List<Formal> Ins { get { return new List<Formal>(); } }
  public ModuleDefinition EnclosingModule { get { return this.EnclosingClass.EnclosingModuleDefinition; } }
  public bool MustReverify { get { return false; } }
  public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
  public string NameRelativeToModule {
    get {
      if (EnclosingClass is DefaultClassDecl) {
        return Name;
      } else {
        return EnclosingClass.Name + "." + Name;
      }
    }
  }
  public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
  public bool InferredDecreases {
    get { throw new cce.UnreachableException(); }
    set { throw new cce.UnreachableException(); }
  }
  public bool AllowsAllocation => true;

  public override IEnumerable<INode> Children => base.Children.Concat(new[] { Rhs }.Where(x => x != null));
  public override DafnySymbolKind Kind => DafnySymbolKind.Constant;

  public override IEnumerable<INode> PreResolveChildren => Children;
  public ModuleDefinition ContainingModule => EnclosingModule;
  public bool ShouldVerify => Rhs != null; // This could be made more accurate by checking whether the Rhs needs to be verified.
  public void AutoRevealDependencies(AutoRevealFunctionDependencies Rewriter, DafnyOptions Options, ErrorReporter Reporter) {
    if (Rhs is null) {
      return;
    }

    foreach (var expression in Rhs.SubExpressions) {
      if (expression is FunctionCallExpr funcExpr) {
        var func = funcExpr.Function;

        if (AutoRevealFunctionDependencies.IsRevealable(EnclosingModule.AccessibleMembers, func)) {
          if (func.IsMadeImplicitlyOpaque(Options)) {
            var expr = Rhs;

            var revealStmt0 = AutoRevealFunctionDependencies.BuildRevealStmt(func,
              expr.Tok, EnclosingModule);

            if (revealStmt0 is not null) {
              var newExpr = new StmtExpr(expr.Tok, revealStmt0, expr) {
                Type = expr.Type
              };
              Rhs = newExpr;
            }
          }

          foreach (var newFunc in Rewriter.GetEnumerator(func, func.EnclosingClass, new List<Expression> { Rhs },
                     EnclosingModule)) {
            var origExpr = Rhs;
            var revealStmt =
              AutoRevealFunctionDependencies.BuildRevealStmt(newFunc.Function, Rhs.Tok, EnclosingModule);

            if (revealStmt is not null) {
              var newExpr = new StmtExpr(Rhs.Tok, revealStmt, origExpr) {
                Type = origExpr.Type
              };
              Rhs = newExpr;
            }
          }
        }
      }
    }
  }
}