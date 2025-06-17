using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class Invariant : MemberDecl, ICallable, ICanVerify {
  public readonly List<AttributedExpression> Body;

  public Invariant([NotNull] Cloner cloner, [NotNull] MemberDecl original) :
    base(cloner, original)
  {
    Contract.Requires(original is Invariant);
    Body = ((Invariant)original).Body.Select(cloner.CloneAttributedExpr).ToList();
  }

  public Invariant([NotNull] IOrigin origin, [NotNull] List<AttributedExpression> body) :
    base(origin, new(origin, "invariant"), true, null)
  {
    Body = body;
  }

  public override IEnumerable<Expression> SubExpressions =>
    Body.ConvertAll(clause => clause.E);

  public override string WhatKind => "invariant";
  
  string ICallable.NameRelativeToModule => EnclosingClass.Name + "." + Name;
  Specification<Expression> ICallable.Decreases =>
    new([new LiteralExpr(Origin, 0)], null); // dummy "decreases 0"
  bool ICallable.InferredDecreases {
    get => false;
    set => throw new cce.UnreachableException();
  }
  bool ICallable.AllowsAllocation => true; // functions can...
  public override bool HasStaticKeyword => false;
  public override SymbolKind? Kind => null;
  public override string GetDescription(DafnyOptions options) => "invariant"; // TODO(somayyas)
  ModuleDefinition ICanVerify.ContainingModule => EnclosingClass.EnclosingModuleDefinition;
  bool ICanVerify.ShouldVerify => true;
  ModuleDefinition IASTVisitorContext.EnclosingModule => EnclosingClass.EnclosingModuleDefinition;
  bool ICodeContext.ContainsHide {
    get => false;
    set => throw new cce.UnreachableException();
  }
  List<TypeParameter> ICodeContext.TypeArgs => EnclosingClass.TypeArgs;
  List<Formal> ICodeContext.Ins => [];
  bool ICodeContext.MustReverify => false;
  bool ICodeContext.AllowsNontermination => false;
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;
  string IFrameScope.Designator => WhatKind;
}