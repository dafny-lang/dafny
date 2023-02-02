using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MemberSelectExpr : Expression, IHasUsages, ICloneable<MemberSelectExpr> {
  public readonly Expression Obj;

  public override IToken Tok => MemberNameNode.Tok;
  
  public string MemberName => MemberNameNode.Value;
  public Name MemberNameNode;
  [FilledInDuringResolution] public MemberDecl Member;    // will be a Field or Function
  [FilledInDuringResolution] public Label /*?*/ AtLabel;  // non-null for a two-state selection
  [FilledInDuringResolution] public bool InCompiledContext;

  /// <summary>
  /// TypeApplication_AtEnclosingClass is the list of type arguments used to instantiate the type that
  /// declares Member (which is some supertype of the receiver type).
  /// </summary>
  [FilledInDuringResolution] public List<Type> TypeApplication_AtEnclosingClass;

  /// <summary>
  ///  TypeApplication_JustMember is the list of type arguments used to instantiate the type parameters
  /// of Member.
  /// </summary>
  [FilledInDuringResolution] public List<Type> TypeApplication_JustMember;

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
      Contract.Assert(TypeApplication_JustMember.Count == icallable.TypeArgs.Count);
      for (var i = 0; i < icallable.TypeArgs.Count; i++) {
        subst.Add(icallable.TypeArgs[i], TypeApplication_JustMember[i]);
      }
    } else {
      Contract.Assert(TypeApplication_JustMember.Count == 0);
    }

    // Add the mappings from the enclosing class.
    TopLevelDecl cl = Member.EnclosingClass;
    // Expand the type down to its non-null type, if any
    if (cl != null) {
      Contract.Assert(cl.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
      for (var i = 0; i < cl.TypeArgs.Count; i++) {
        subst.Add(cl.TypeArgs[i], TypeApplication_AtEnclosingClass[i]);
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

    return TypeArgumentSubstitutionsWithParentsAux(Obj.Type, Member, TypeApplication_JustMember);
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
    Contract.Invariant((Member != null) == (TypeApplication_AtEnclosingClass != null));  // TypeApplication_* are set whenever Member is set
    Contract.Invariant((Member != null) == (TypeApplication_JustMember != null));  // TypeApplication_* are set whenever Member is set
  }

  public MemberSelectExpr Clone(Cloner cloner) {
    return new MemberSelectExpr(cloner, this);
  }

  public MemberSelectExpr(Cloner cloner, MemberSelectExpr original) : base(cloner, original) {
    Obj = cloner.CloneExpr(original.Obj);
    MemberNameNode = original.MemberNameNode.Clone(cloner);

    if (cloner.CloneResolvedFields) {
      Member = cloner.CloneMember(original.Member, true);
      AtLabel = original.AtLabel;
      InCompiledContext = original.InCompiledContext;
      TypeApplication_AtEnclosingClass = original.TypeApplication_AtEnclosingClass;
      TypeApplication_JustMember = original.TypeApplication_JustMember;
    }
  }

  public MemberSelectExpr(RangeToken rangeToken, Expression obj, Name memberName)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(obj != null);
    Contract.Requires(memberName != null);
    this.Obj = obj;
    this.MemberNameNode = memberName;
  }

  /// <summary>
  /// Returns a resolved MemberSelectExpr for a field.
  /// </summary>
  public MemberSelectExpr(RangeToken rangeToken, Expression obj, Field field)
    : this(rangeToken, obj, field.NameNode) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(obj != null);
    Contract.Requires(field != null);
    Contract.Requires(obj.Type != null);  // "obj" is required to be resolved

    this.Member = field;  // resolve here

    var receiverType = obj.Type.NormalizeExpand();
    this.TypeApplication_AtEnclosingClass = receiverType.TypeArgs;
    this.TypeApplication_JustMember = new List<Type>();
    this.ResolvedOutparameterTypes = new List<Type>();

    var typeMap = new Dictionary<TypeParameter, Type>();
    if (receiverType is UserDefinedType udt) {
      var cl = udt.ResolvedClass as TopLevelDeclWithMembers;
      Contract.Assert(cl != null);
      Contract.Assert(cl.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
      for (var i = 0; i < cl.TypeArgs.Count; i++) {
        typeMap.Add(cl.TypeArgs[i], TypeApplication_AtEnclosingClass[i]);
      }
      foreach (var entry in cl.ParentFormalTypeParametersToActuals) {
        var v = entry.Value.Subst(typeMap);
        typeMap.Add(entry.Key, v);
      }
    } else if (field.EnclosingClass == null) {
      // leave typeMap as the empty substitution
    } else {
      Contract.Assert(field.EnclosingClass.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
      for (var i = 0; i < field.EnclosingClass.TypeArgs.Count; i++) {
        typeMap.Add(field.EnclosingClass.TypeArgs[i], TypeApplication_AtEnclosingClass[i]);
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

  public override IEnumerable<Type> ComponentTypes => Util.Concat(TypeApplication_AtEnclosingClass, TypeApplication_JustMember);

  [FilledInDuringResolution] public List<Type> ResolvedOutparameterTypes;

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { Member };
  }

  public IToken NameToken => tok;
}