using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class ConstantField : Field, ICallable, ICanAutoRevealDependencies, ICanVerify {
  public override string WhatKind => "const field";
  public Expression Rhs;

  public virtual string IdParam => NonglobalVariable.SanitizeName(Name);
  
  public override bool IsOpaque { get; }

  public override bool IsMutable => false;
  public override bool IsUserMutable => false;

  [SyntaxConstructor]
  public ConstantField(IOrigin origin, Name nameNode, Expression/*?*/ rhs, bool hasStaticKeyword,
    bool isGhost, bool isOpaque, Type type, Attributes attributes)
    : base(origin, nameNode, isGhost, type, attributes) {
    Contract.Requires(nameNode != null);
    Contract.Requires(type != null);
    this.Rhs = rhs;
    this.IsOpaque = isOpaque;
    HasStaticKeyword = hasStaticKeyword;
  }

  public override bool HasStaticKeyword { get; }

  public override bool CanBeRevealed() {
    return true;
  }

  public bool ContainsHide { get; set; }
  public List<TypeParameter> TypeArgs { get { return []; } }
  public List<Formal> Ins { get { return []; } }
  public ModuleDefinition EnclosingModule { get { return this.EnclosingClass.EnclosingModuleDefinition; } }
  public bool MustReverify { get { return false; } }
  public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;

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

  public override IEnumerable<INode> Children =>
    base.Children.Concat(new[] { Rhs }.Where(x => x != null));
  public override SymbolKind? Kind => SymbolKind.Constant;

  public override IEnumerable<INode> PreResolveChildren => Children;
  public ModuleDefinition ContainingModule => EnclosingModule;
  public bool ShouldVerify => Rhs != null; // This could be made more accurate by checking whether the Rhs needs to be verified.
  public void AutoRevealDependencies(AutoRevealFunctionDependencies Rewriter, DafnyOptions Options, ErrorReporter Reporter) {
    if (Rhs is null) {
      return;
    }

    var addedReveals = Rewriter.ExprToFunctionalDependencies(Rhs, EnclosingModule);
    Rhs = Rewriter.AddRevealStmtsToExpression(Rhs, addedReveals);

    if (addedReveals.Any()) {
      Reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, Origin,
        AutoRevealFunctionDependencies.GenerateMessage(addedReveals.ToList()));
    }
  }
  public string Designator => WhatKind;
}