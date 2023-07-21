using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;

namespace Microsoft.Dafny;

public class NewtypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl, IHasDocstring {
  public override string WhatKind { get { return "newtype"; } }
  public override bool CanBeRevealed() { return true; }
  public PreType BasePreType;
  public Type BaseType { get; set; } // null when refining
  public BoundVar Var { get; set; }  // can be null (if non-null, then object.ReferenceEquals(Var.Type, BaseType))
  public Expression Constraint { get; set; }  // is null iff Var is
  public SubsetTypeDecl.WKind WitnessKind { get; set; } = SubsetTypeDecl.WKind.CompiledZero;
  public Expression/*?*/ Witness { get; set; } // non-null iff WitnessKind is Compiled or Ghost
  [FilledInDuringResolution] public NativeType NativeType; // non-null for fixed-size representations (otherwise, use BigIntegers for integers)
  public NewtypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, Type baseType, List<Type> parentTraits,
    List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, new List<TypeParameter>(), members, attributes, isRefining, parentTraits) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(isRefining ^ (baseType != null));
    Contract.Requires(members != null);
    BaseType = baseType;
  }
  public NewtypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, BoundVar bv, Expression constraint,
    SubsetTypeDecl.WKind witnessKind, Expression witness, List<Type> parentTraits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, new List<TypeParameter>(), members, attributes, isRefining, parentTraits) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(bv != null && bv.Type != null);
    Contract.Requires((witnessKind == SubsetTypeDecl.WKind.Compiled || witnessKind == SubsetTypeDecl.WKind.Ghost) == (witness != null));
    Contract.Requires(members != null);
    BaseType = bv.Type;
    Var = bv;
    Constraint = constraint;
    Witness = witness;
    WitnessKind = witnessKind;
    this.NewSelfSynonym();
  }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public TypeParameter.EqualitySupportValue EqualitySupport {
    get {
      if (this.BaseType.SupportsEquality) {
        return TypeParameter.EqualitySupportValue.Required;
      } else {
        return TypeParameter.EqualitySupportValue.Unspecified;
      }
    }
  }

  string RedirectingTypeDecl.Name { get { return Name; } }
  IToken RedirectingTypeDecl.tok { get { return tok; } }
  IEnumerable<IToken> RedirectingTypeDecl.OwnedTokens => OwnedTokens;
  IToken RedirectingTypeDecl.StartToken => StartToken;
  Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
  ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
  BoundVar RedirectingTypeDecl.Var { get { return Var; } }
  Expression RedirectingTypeDecl.Constraint { get { return Constraint; } }
  SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
  Expression RedirectingTypeDecl.Witness { get { return Witness; } }
  FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

  bool ICodeContext.IsGhost {
    get { throw new NotSupportedException(); }  // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
  }
  List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
  string ICallable.NameRelativeToModule { get { return Name; } }
  Specification<Expression> ICallable.Decreases {
    get {
      // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
      // the question of what its Decreases clause is should never arise.
      throw new cce.UnreachableException();
    }
  }
  bool ICallable.InferredDecreases {
    get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
  }

  public override bool AcceptThis => true;

  public override bool IsEssentiallyEmpty() {
    // A "newtype" is not considered "essentially empty", because it always has a parent type to be resolved.
    return false;
  }

  protected override string GetTriviaContainingDocstring() {
    IToken candidate = null;
    foreach (var token in OwnedTokens) {
      if (token.val == "{") {
        candidate = token.Prev;
        if (candidate.TrailingTrivia.Trim() != "") {
          return candidate.TrailingTrivia;
        }
      }
    }

    if (candidate == null && EndToken.TrailingTrivia.Trim() != "") {
      return EndToken.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}

public class NativeType {
  public readonly string Name;
  public readonly BigInteger LowerBound;
  public readonly BigInteger UpperBound;
  public readonly int Bitwidth;  // for unassigned types, this shows the number of bits in the type; else is 0
  public enum Selection { Byte, SByte, UShort, Short, UInt, Int, Number, ULong, Long }
  public readonly Selection Sel;
  public NativeType(string Name, BigInteger LowerBound, BigInteger UpperBound, int bitwidth, Selection sel) {
    Contract.Requires(Name != null);
    Contract.Requires(0 <= bitwidth && (bitwidth == 0 || LowerBound == 0));
    this.Name = Name;
    this.LowerBound = LowerBound;
    this.UpperBound = UpperBound;
    this.Bitwidth = bitwidth;
    this.Sel = sel;
  }
}

public interface RevealableTypeDecl {
  TopLevelDecl AsTopLevelDecl { get; }
  TypeDeclSynonymInfo SynonymInfo { get; set; }
}