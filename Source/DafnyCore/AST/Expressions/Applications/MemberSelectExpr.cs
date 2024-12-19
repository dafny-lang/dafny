using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MemberSelectExpr : Expression, IHasReferences, ICloneable<MemberSelectExpr> {
  public readonly Expression Obj;
  public Name MemberNameNode;
  public string MemberName => MemberNameNode.Value;
  [FilledInDuringResolution] public MemberDecl Member;    // will be a Field or Function
  [FilledInDuringResolution] public Label /*?*/ AtLabel;  // non-null for a two-state selection
  [FilledInDuringResolution] public bool InCompiledContext;

  /// <summary>
  /// PreTypeApplication_AtEnclosingClass is the list of type arguments used to instantiate the type that
  /// declares Member (which is some supertype of the receiver type).
  /// </summary>
  [FilledInDuringResolution] public List<PreType> PreTypeApplicationAtEnclosingClass;

  /// <summary>
  /// PreTypeApplication_JustMember is the list of type arguments used to instantiate the type parameters
  /// of Member.
  /// </summary>
  [FilledInDuringResolution] public List<PreType> PreTypeApplicationJustMember;

  /// <summary>
  /// TypeApplication_AtEnclosingClass is the list of type arguments used to instantiate the type that
  /// declares Member (which is some supertype of the receiver type).
  /// </summary>
  [FilledInDuringResolution] public List<Type> TypeApplicationAtEnclosingClass;

  /// <summary>
  /// TypeApplication_JustMember is the list of type arguments used to instantiate the type parameters
  /// of Member.
  /// </summary>
  [FilledInDuringResolution] public List<Type> TypeApplicationJustMember;

  /// <summary>
  /// Returns a mapping from formal type parameters to actual type arguments. For example, given
  ///     trait T<A> {
  ///       function F<X>(): bv8 { ... }
  ///     }
  ///     class C<B, D> extends T<map<B, D>> { }
  /// and MemberSelectExpr o.F<int> where o has type C<real, bool>, the type map returned is
  ///     A -> map<real, bool>
  ///     X -> int
  /// To also include B and D in the mapping, use TypeArgumentSubstitutionsWithParents instead.
  /// </summary>
  public Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsAtMemberDeclaration() {
    Contract.Requires(WasResolved());
    Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

    var subst = new Dictionary<TypeParameter, Type>();

    // Add the mappings from the member's own type parameters
    if (Member is ICallable icallable) {
      Contract.Assert(TypeApplicationJustMember.Count == icallable.TypeArgs.Count);
      for (var i = 0; i < icallable.TypeArgs.Count; i++) {
        subst.Add(icallable.TypeArgs[i], TypeApplicationJustMember[i]);
      }
    } else {
      Contract.Assert(TypeApplicationJustMember.Count == 0);
    }

    // Add the mappings from the enclosing class.
    TopLevelDecl cl = Member.EnclosingClass;
    // Expand the type down to its non-null type, if any
    if (cl != null) {
      Contract.Assert(cl.TypeArgs.Count == TypeApplicationAtEnclosingClass.Count);
      for (var i = 0; i < cl.TypeArgs.Count; i++) {
        subst.Add(cl.TypeArgs[i], TypeApplicationAtEnclosingClass[i]);
      }
    }

    return subst;
  }

  /// <summary>
  /// Returns a mapping from formal type parameters to actual pre-type arguments. For example, given
  ///     trait T<A> {
  ///       function F<X>(): bv8 { ... }
  ///     }
  ///     class C<B, D> extends T<map<B, D>> { }
  /// and MemberSelectExpr o.F<int> where o has type C<real, bool>, the type map returned is
  ///     A -> map<real, bool>
  ///     X -> int
  /// To also include B and D in the mapping, use PreTypeArgumentSubstitutionsWithParents instead.
  /// </summary>
  public Dictionary<TypeParameter, PreType> PreTypeArgumentSubstitutionsAtMemberDeclaration() {
    Contract.Requires(WasResolved());
    Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

    var subst = new Dictionary<TypeParameter, PreType>();

    // Add the mappings from the member's own type parameters
    if (Member is ICallable icallable) {
      Contract.Assert(PreTypeApplicationJustMember.Count == icallable.TypeArgs.Count);
      for (var i = 0; i < icallable.TypeArgs.Count; i++) {
        subst.Add(icallable.TypeArgs[i], PreTypeApplicationJustMember[i]);
      }
    } else {
      Contract.Assert(PreTypeApplicationJustMember.Count == 0);
    }

    // Add the mappings from the enclosing class.
    TopLevelDecl cl = Member.EnclosingClass;
    // Expand the type down to its non-null type, if any
    if (cl != null) {
      Contract.Assert(cl.TypeArgs.Count == PreTypeApplicationAtEnclosingClass.Count);
      for (var i = 0; i < cl.TypeArgs.Count; i++) {
        subst.Add(cl.TypeArgs[i], PreTypeApplicationAtEnclosingClass[i]);
      }
    }

    return subst;
  }

  /// <summary>
  /// Returns a mapping from formal type parameters to actual type arguments. For example, given
  ///     trait T<A> {
  ///       function F<X>(): bv8 { ... }
  ///     }
  ///     class C<B, D> extends T<map<B, D>> { }
  /// and MemberSelectExpr o.F<int> where o has type C<real, bool>, the type map returned is
  ///     A -> map<real, bool>
  ///     B -> real
  ///     D -> bool
  ///     X -> int
  /// NOTE: This method should be called only when all types have been fully and successfully
  /// resolved. During type inference, when there may still be some unresolved proxies, use
  /// TypeArgumentSubstitutionsAtMemberDeclaration instead.
  /// </summary>
  public Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsWithParents() {
    Contract.Requires(WasResolved());
    Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

    return TypeArgumentSubstitutionsWithParentsAux(Obj.Type, Member, TypeApplicationJustMember);
  }

  public static Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsWithParentsAux(Type receiverType, MemberDecl member, List<Type> typeApplicationMember) {
    Contract.Requires(receiverType != null);
    Contract.Requires(member != null);
    Contract.Requires(typeApplicationMember != null);
    Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

    var subst = new Dictionary<TypeParameter, Type>();

    // Add the mappings from the member's own type parameters
    if (member is ICallable) {
      // Make sure to include the member's type parameters all the way up the inheritance chain
      for (var ancestor = member; ancestor != null; ancestor = ancestor.OverriddenMember) {
        var icallable = (ICallable)ancestor;
        Contract.Assert(typeApplicationMember.Count == icallable.TypeArgs.Count);
        for (var i = 0; i < icallable.TypeArgs.Count; i++) {
          subst.Add(icallable.TypeArgs[i], typeApplicationMember[i]);
        }
      }
    } else {
      Contract.Assert(typeApplicationMember.Count == 0);
    }

    // Add the mappings from the receiver's type "cl"
    var udt = receiverType.NormalizeExpand() as UserDefinedType;
    if (udt != null) {
      if (udt.ResolvedClass is InternalTypeSynonymDecl isyn) {
        udt = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
      }
      if (udt.ResolvedClass is NonNullTypeDecl nntd) {
        udt = nntd.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
      }
    }
    var cl = udt?.ResolvedClass;

    if (cl != null) {
      Contract.Assert(cl.TypeArgs.Count == udt.TypeArgs.Count);
      for (var i = 0; i < cl.TypeArgs.Count; i++) {
        subst.Add(cl.TypeArgs[i], udt.TypeArgs[i]);
      }

      // Add in the mappings from parent types' formal type parameters to types
      if (cl is TopLevelDeclWithMembers cls) {
        foreach (var entry in cls.ParentFormalTypeParametersToActuals) {
          var v = entry.Value.Subst(subst);
          subst.Add(entry.Key, v);
        }
      }
    }

    return subst;
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Obj != null);
    Contract.Invariant(MemberName != null);
    Contract.Invariant((Member != null) == (TypeApplicationAtEnclosingClass != null));  // TypeApplication_* are set whenever Member is set
    Contract.Invariant((Member != null) == (TypeApplicationJustMember != null));  // TypeApplication_* are set whenever Member is set
  }

  public MemberSelectExpr Clone(Cloner cloner) {
    return new MemberSelectExpr(cloner, this);
  }

  public MemberSelectExpr(Cloner cloner, MemberSelectExpr original) : base(cloner, original) {
    Obj = cloner.CloneExpr(original.Obj);
    MemberNameNode = new Name(cloner, original.MemberNameNode);

    if (cloner.CloneResolvedFields) {
      Member = cloner.CloneMember(original.Member, true);
      AtLabel = original.AtLabel;
      InCompiledContext = original.InCompiledContext;
      TypeApplicationAtEnclosingClass = original.TypeApplicationAtEnclosingClass;
      TypeApplicationJustMember = original.TypeApplicationJustMember;
    }
  }

  public MemberSelectExpr(IOrigin tok, Expression obj, Name memberName)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(obj != null);
    Contract.Requires(memberName != null);
    this.Obj = obj;
    this.MemberNameNode = memberName;
  }

  /// <summary>
  /// Returns a resolved MemberSelectExpr for a field.
  /// </summary>
  public MemberSelectExpr(IOrigin tok, Expression obj, Field field)
    : this(tok, obj, new Name(field.Name)) {
    Contract.Requires(tok != null);
    Contract.Requires(obj != null);
    Contract.Requires(field != null);
    Contract.Requires(obj.Type != null);  // "obj" is required to be resolved

    this.Member = field;  // resolve here

    var receiverType = obj.Type.NormalizeExpand();
    this.TypeApplicationAtEnclosingClass = receiverType.TypeArgs;
    this.TypeApplicationJustMember = new List<Type>();

    var typeMap = new Dictionary<TypeParameter, Type>();
    if (receiverType is UserDefinedType udt) {
      var cl = udt.ResolvedClass as TopLevelDeclWithMembers;
      Contract.Assert(cl != null);
      Contract.Assert(cl.TypeArgs.Count == TypeApplicationAtEnclosingClass.Count);
      for (var i = 0; i < cl.TypeArgs.Count; i++) {
        typeMap.Add(cl.TypeArgs[i], TypeApplicationAtEnclosingClass[i]);
      }
      foreach (var entry in cl.ParentFormalTypeParametersToActuals) {
        var v = entry.Value.Subst(typeMap);
        typeMap.Add(entry.Key, v);
      }
    } else if (field.EnclosingClass == null) {
      // leave typeMap as the empty substitution
    } else {
      Contract.Assert(field.EnclosingClass.TypeArgs.Count == TypeApplicationAtEnclosingClass.Count);
      for (var i = 0; i < field.EnclosingClass.TypeArgs.Count; i++) {
        typeMap.Add(field.EnclosingClass.TypeArgs[i], TypeApplicationAtEnclosingClass[i]);
      }
    }
    this.Type = field.Type.Subst(typeMap);  // resolve here
  }

  public void MemberSelectCase(Action<Field> fieldK, Action<Function> functionK) {
    MemberSelectCase<bool>(
      f => {
        fieldK(f);
        return true;
      },
      f => {
        functionK(f);
        return true;
      });
  }

  public A MemberSelectCase<A>(Func<Field, A> fieldK, Func<Function, A> functionK) {
    var field = Member as Field;
    var function = Member as Function;
    if (field != null) {
      return fieldK(field);
    } else {
      Contract.Assert(function != null);
      return functionK(function);
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return Obj; }
  }

  public override IEnumerable<Type> ComponentTypes => Util.Concat(TypeApplicationAtEnclosingClass, TypeApplicationJustMember);

  [FilledInDuringResolution] public List<Type> ResolvedOutparameterTypes;

  public IEnumerable<Reference> GetReferences() {
    return new[] { new Reference(Tok, Member) };
  }
}
