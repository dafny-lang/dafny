using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;

namespace Microsoft.Dafny;

public class NewtypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl, IHasDocstring, ICanVerify {
  public override string WhatKind { get { return "newtype"; } }
  public override bool CanBeRevealed() { return true; }
  public PreType BasePreType;
  PreType RedirectingTypeDecl.BasePreType => BasePreType;
  public Type BaseType { get; set; } // null when refining
  public BoundVar Var { get; set; }  // can be null (if non-null, then object.ReferenceEquals(Var.Type, BaseType))
  public Expression Constraint { get; set; }  // is null iff Var is
  public SubsetTypeDecl.WKind WitnessKind { get; set; } = SubsetTypeDecl.WKind.CompiledZero;
  public Expression/*?*/ Witness { get; set; } // non-null iff WitnessKind is Compiled or Ghost
  [FilledInDuringResolution] public NativeType NativeType; // non-null for fixed-size representations (otherwise, use BigIntegers for integers)

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

  [FilledInDuringResolution] public bool TargetTypeCoversAllBitPatterns; // "target complete" -- indicates that any bit pattern that can fill the target type is a value of the newtype

  public NewtypeDecl(IOrigin origin, Name nameNode, List<TypeParameter> typeParameters, ModuleDefinition enclosingModule,
    Type baseType,
    SubsetTypeDecl.WKind witnessKind, Expression witness, List<Type> parentTraits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(origin, nameNode, enclosingModule, typeParameters, members, attributes, parentTraits) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModule != null);
    Contract.Requires((witnessKind == SubsetTypeDecl.WKind.Compiled || witnessKind == SubsetTypeDecl.WKind.Ghost) == (witness != null));
    Contract.Requires(members != null);
    BaseType = baseType;
    Witness = witness;
    IsRefining = isRefining;
    WitnessKind = witnessKind;
    this.NewSelfSynonym();
  }
  public NewtypeDecl(IOrigin origin, Name nameNode, List<TypeParameter> typeParameters, ModuleDefinition enclosingModule,
    BoundVar bv, Expression constraint,
    SubsetTypeDecl.WKind witnessKind, Expression witness, List<Type> parentTraits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(origin, nameNode, enclosingModule, typeParameters, members, attributes, parentTraits) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModule != null);
    Contract.Requires(bv != null && bv.Type != null);
    Contract.Requires((witnessKind == SubsetTypeDecl.WKind.Compiled || witnessKind == SubsetTypeDecl.WKind.Ghost) == (witness != null));
    Contract.Requires(members != null);
    BaseType = bv.Type;
    Var = bv;
    IsRefining = isRefining;
    Constraint = constraint;
    Witness = witness;
    WitnessKind = witnessKind;
    this.NewSelfSynonym();
  }

  public override bool IsRefining { get; }

  public Type ConcreteBaseType(List<Type> typeArguments) {
    Contract.Requires(TypeArgs.Count == typeArguments.Count);
    if (typeArguments.Count == 0) {
      // this optimization seems worthwhile
      return BaseType;
    }
    var subst = TypeParameter.SubstitutionMap(TypeArgs, typeArguments);
    return BaseType.Subst(subst);
  }

  /// <summary>
  /// Return .BaseType instantiated with "typeArgs", but only look at the part of .BaseType that is in scope.
  /// </summary>
  public Type RhsWithArgument(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    var scope = Type.GetScope();
    var rtd = BaseType.AsRevealableType;
    if (rtd != null) {
      Contract.Assume(rtd.AsTopLevelDecl.IsVisibleInScope(scope));
      if (!rtd.IsRevealedInScope(scope)) {
        // type is actually hidden in this scope
        return rtd.SelfSynonym(typeArgs);
      }
    }
    return ConcreteBaseType(typeArgs);
  }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  private IndDatatypeDecl.ES equalitySupport = IndDatatypeDecl.ES.NotYetComputed;

  public IndDatatypeDecl.ES EqualitySupport {
    get {
      if (equalitySupport == IndDatatypeDecl.ES.NotYetComputed) {
        var thingsChanged = false;
        if (ModuleResolver.SurelyNeverSupportEquality(BaseType)) {
          equalitySupport = IndDatatypeDecl.ES.Never;
        } else {
          ModuleResolver.DetermineEqualitySupportType(BaseType, ref thingsChanged);
          equalitySupport = IndDatatypeDecl.ES.ConsultTypeArguments;
        }
      }

      return equalitySupport;
    }
  }

  string RedirectingTypeDecl.Name { get { return Name; } }
  IOrigin RedirectingTypeDecl.Tok { get { return Origin; } }
  Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
  ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
  BoundVar RedirectingTypeDecl.Var { get { return Var; } }
  Expression RedirectingTypeDecl.Constraint { get { return Constraint; } }
  SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
  Expression RedirectingTypeDecl.Witness { get { return Witness; } }
  VerificationIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

  public bool ContainsHide {
    get => throw new NotSupportedException();
    set => throw new NotSupportedException();
  }

  bool ICodeContext.IsGhost {
    get { throw new NotSupportedException(); }  // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
  }
  List<TypeParameter> ICodeContext.TypeArgs => TypeArgs;
  List<Formal> ICodeContext.Ins => [];
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;
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

  public string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }

    foreach (var token in OwnedTokens) {
      if (token.val == "=") {
        if ((token.Prev.TrailingTrivia + token.LeadingTrivia).Trim() is { } tentativeTrivia1 and not "") {
          return tentativeTrivia1;
        }
      }
    }

    if (EndToken.TrailingTrivia.Trim() is { } tentativeTrivia and not "") {
      return tentativeTrivia;
    }

    return null;
  }

  public ModuleDefinition ContainingModule => EnclosingModuleDefinition;
  public bool ShouldVerify => true; // This could be made more accurate
  public string Designator => WhatKind;
}

public class NativeType {
  public string Name;
  public BigInteger LowerBound;
  public BigInteger UpperBound;
  public int Bitwidth;  // for unassigned types, this shows the number of bits in the type; else is 0
  public enum Selection { Byte, SByte, UShort, Short, UInt, Int, Number, ULong, Long, UDoubleLong, DoubleLong }
  public Selection Sel;
  public NativeType(string Name, BigInteger LowerBound, BigInteger UpperBound, int bitwidth, Selection sel) {
    Contract.Requires(Name != null);
    Contract.Requires(0 <= bitwidth && (bitwidth == 0 || LowerBound == 0));
    this.Name = Name;
    this.LowerBound = LowerBound;
    this.UpperBound = UpperBound;
    this.Bitwidth = bitwidth;
    this.Sel = sel;
  }

  public Selection? UnsignedCounterpart() {
    switch (Sel) {
      case Selection.SByte: return Selection.Byte;
      case Selection.Short: return Selection.UShort;
      case Selection.Int: return Selection.UInt;
      case Selection.Long: return Selection.ULong;
      default:
        return null;
    }
  }
}

public interface RevealableTypeDecl {
  TopLevelDecl AsTopLevelDecl { get; }
  TypeDeclSynonymInfo SynonymInfo { get; set; }
}