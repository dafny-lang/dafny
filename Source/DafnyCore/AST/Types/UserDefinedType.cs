using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class UserDefinedType : NonProxyType, IHasReferences {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
    Contract.Invariant(Name != null);
    Contract.Invariant(cce.NonNullElements(TypeArgs));
    Contract.Invariant(NamePath is NameSegment or ExprDotName);
    Contract.Invariant(!ArrowType.IsArrowTypeName(Name) || this is ArrowType);
  }

  public readonly Expression NamePath;  // either NameSegment or ExprDotName (with the inner expression satisfying this same constraint)
  public readonly string Name;
  [Rep]

  public string FullName {
    get {
      if (ResolvedClass?.EnclosingModuleDefinition?.TryToAvoidName == false) {
        return ResolvedClass.EnclosingModuleDefinition.Name + "." + Name;
      } else {
        return Name;
      }
    }
  }

  string compileName;
  public string GetCompileName(DafnyOptions options) => compileName ??= ResolvedClass.GetCompileName(options);

  public string GetFullCompanionCompileName(DafnyOptions options) {
    Contract.Requires(ResolvedClass is TraitDecl || (ResolvedClass is NonNullTypeDecl nntd && nntd.Class is TraitDecl));
    var m = ResolvedClass.EnclosingModuleDefinition;
    var s = m.TryToAvoidName ? "" : m.GetCompileName(options) + ".";
    return s + "_Companion_" + ResolvedClass.GetCompileName(options);
  }

  [FilledInDuringResolution] public TopLevelDecl ResolvedClass;  // if Name denotes a class/datatype/iterator and TypeArgs match the type parameters of that class/datatype/iterator

  public UserDefinedType(IOrigin tok, string name, List<Type> optTypeArgs)
    : this(tok, new NameSegment(tok, name, optTypeArgs)) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(optTypeArgs == null || optTypeArgs.Count > 0);  // this is what it means to be syntactically optional
  }

  public UserDefinedType(IOrigin tok, Expression namePath) {
    Contract.Requires(tok != null);
    Contract.Requires(namePath is NameSegment || namePath is ExprDotName);
    this.tok = tok;
    if (namePath is NameSegment) {
      var n = (NameSegment)namePath;
      this.Name = n.Name;
      this.TypeArgs = n.OptTypeArguments;
    } else {
      var n = (ExprDotName)namePath;
      this.Name = n.SuffixName;
      this.TypeArgs = n.OptTypeArguments;
    }
    if (this.TypeArgs == null) {
      this.TypeArgs = new List<Type>();  // TODO: is this really the thing to do?
    }
    this.NamePath = namePath;
  }
  public UserDefinedType(Cloner cloner, UserDefinedType original)
    : this(cloner.Origin(original.Tok), cloner.CloneExpr(original.NamePath)) {
    if (cloner.CloneResolvedFields) {
      ResolvedClass = cloner.GetCloneIfAvailable(original.ResolvedClass);
      TypeArgs = original.TypeArgs.Select(cloner.CloneType).ToList();
    }
  }

  /// <summary>
  /// Constructs a Type (in particular, a UserDefinedType) from a TopLevelDecl denoting a type declaration.  If
  /// the given declaration takes type parameters, these are filled as references to the formal type parameters
  /// themselves.  (Usually, this method is called when the type parameters in the result don't matter, other
  /// than that they need to be filled in, so as to make a properly resolved UserDefinedType.)
  /// If "typeArgs" is non-null, then its type parameters are used in constructing the returned type.
  /// If "typeArgs" is null, then the formal type parameters of "cd" are used.
  /// </summary>
  public static UserDefinedType FromTopLevelDecl(IOrigin tok, TopLevelDecl cd, List<TypeParameter> typeArgs = null) {
    Contract.Requires(tok != null);
    Contract.Requires(cd != null);
    Contract.Assert((cd is ArrowTypeDecl) == ArrowType.IsArrowTypeName(cd.Name));
    var args = (typeArgs ?? cd.TypeArgs).ConvertAll(tp => (Type)new UserDefinedType(tp));
    return FromTopLevelDecl(tok, cd, args);
  }

  /// <summary>
  /// Constructs a Type (in particular, a UserDefinedType) from a TopLevelDecl denoting a type declaration.
  /// </summary>
  public static UserDefinedType FromTopLevelDecl(IOrigin tok, TopLevelDecl cd, List<Type> typeArguments) {
    if (cd is ArrowTypeDecl) {
      return new ArrowType(tok, (ArrowTypeDecl)cd, typeArguments);
    } else if (cd is ClassLikeDecl { IsReferenceTypeDecl: true }) {
      return new UserDefinedType(tok, cd.Name + "?", cd, typeArguments);
    } else {
      return new UserDefinedType(tok, cd.Name, cd, typeArguments);
    }
  }

  public static UserDefinedType FromTopLevelDeclWithAllBooleanTypeParameters(TopLevelDecl cd) {
    Contract.Requires(cd != null);
    Contract.Requires(!(cd is ArrowTypeDecl));

    var typeArgs = cd.TypeArgs.ConvertAll(tp => (Type)Type.Bool);
    return new UserDefinedType(cd.Tok, cd.Name, cd, typeArgs);
  }

  /// <summary>
  /// If "member" is non-null, then:
  ///   Return the upcast of "receiverType" that has base type "member.EnclosingClass".
  ///   Assumes that "receiverType" normalizes to a UserDefinedFunction with a .ResolveClass that is a subtype
  ///   of "member.EnclosingClass".
  ///   Preserves non-null-ness of "receiverType" if it is a non-null reference.
  /// Otherwise:
  ///   Return "receiverType" (expanded).
  /// </summary>
  public static Type UpcastToMemberEnclosingType(Type receiverType, MemberDecl/*?*/ member) {
    Contract.Requires(receiverType != null);
    if (member != null && member.EnclosingClass != null && !(member.EnclosingClass is ValuetypeDecl)) {
      var parentType = receiverType.AsParentType(member.EnclosingClass);

      if (receiverType.IsNonNullRefType) {
        if (parentType == null) {
          return null;
        } else if (parentType.ResolvedClass is ClassLikeDecl { IsReferenceTypeDecl: true }) {
          return CreateNonNullType(parentType);
        } else {
          return parentType;
        }
      } else {
        return parentType;
      }
    }
    return receiverType.NormalizeExpandKeepConstraints();
  }

  /// <summary>
  /// This constructor constructs a resolved class/datatype/iterator/subset-type/newtype type.
  /// Note, if "cd" is an arrow type or a possibly-null reference type, then it's better to call
  /// the FromTopLevelDecl method to create the UserDefinedType; that makes sure the right class
  /// and right name is used.
  /// </summary>
  public UserDefinedType(IOrigin tok, string name, TopLevelDecl cd, [Captured] List<Type> typeArgs, Expression/*?*/ namePath = null) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(cd != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cd.TypeArgs.Count == typeArgs.Count);
    Contract.Requires(namePath == null || namePath is NameSegment || namePath is ExprDotName);
    // The following is almost a precondition. In a few places, the source program names a class, not a type,
    // and in then name==cd.Name for a ClassDecl.
    //Contract.Requires(!(cd is ClassDecl) || name == cd.Name + "?");
    Contract.Requires(!(cd is ArrowTypeDecl) || name == cd.Name);
    Contract.Requires(!(cd is DefaultClassDecl) || name == cd.Name);
    Contract.Assert(cd is not ArrowTypeDecl || this is ArrowType);
    this.tok = tok;
    this.Name = name;
    this.ResolvedClass = cd;
    this.TypeArgs = typeArgs;
    if (namePath == null) {
      var ns = new NameSegment(tok, name, typeArgs.Count == 0 ? null : typeArgs);
      var r = new Resolver_IdentifierExpr(tok, cd, typeArgs);
      ns.ResolvedExpression = r;
      ns.Type = r.Type;
      this.NamePath = ns;
    } else {
      this.NamePath = namePath;
    }
  }

  public static UserDefinedType CreateNonNullType(UserDefinedType udtNullableType) {
    Contract.Requires(udtNullableType != null);
    Contract.Requires(udtNullableType.ResolvedClass is ClassLikeDecl { IsReferenceTypeDecl: true });
    var cl = (ClassLikeDecl)udtNullableType.ResolvedClass;
    return new UserDefinedType(udtNullableType.Tok, cl.NonNullTypeDecl.Name, cl.NonNullTypeDecl, udtNullableType.TypeArgs);
  }

  public static UserDefinedType CreateNullableType(UserDefinedType udtNonNullType) {
    Contract.Requires(udtNonNullType != null);
    Contract.Requires(udtNonNullType.ResolvedClass is NonNullTypeDecl);
    var nntd = (NonNullTypeDecl)udtNonNullType.ResolvedClass;
    return new UserDefinedType(udtNonNullType.Tok, nntd.Class.Name + "?", nntd.Class, udtNonNullType.TypeArgs);
  }

  public static UserDefinedType CreateNonNullTypeIfReferenceType(UserDefinedType classLikeType) {
    Contract.Requires(classLikeType != null);
    Contract.Requires(classLikeType.ResolvedClass is ClassLikeDecl);
    return classLikeType.IsRefType ? CreateNonNullType(classLikeType) : classLikeType;
  }

  public static UserDefinedType CreateNullableTypeIfReferenceType(UserDefinedType classLikeType) {
    Contract.Requires(classLikeType != null);
    Contract.Requires(!classLikeType.IsRefType || classLikeType.ResolvedClass is NonNullTypeDecl);
    return classLikeType.IsRefType ? CreateNullableType(classLikeType) : classLikeType;
  }

  /// <summary>
  /// This constructor constructs a resolved type parameter
  /// </summary>
  public UserDefinedType(TypeParameter tp)
    : this(tp.Tok, tp) {
    Contract.Requires(tp != null);
  }

  /// <summary>
  /// This constructor constructs a resolved type parameter
  /// </summary>
  public UserDefinedType(IOrigin tok, TypeParameter tp) {
    Contract.Requires(tok != null);
    Contract.Requires(tp != null);
    this.tok = tok;
    this.Name = tp.Name;
    this.TypeArgs = new List<Type>();
    this.ResolvedClass = tp;
    var ns = new NameSegment(tok, tp.Name, null);
    var r = new Resolver_IdentifierExpr(tok, tp);
    ns.ResolvedExpression = r;
    ns.Type = r.Type;
    this.NamePath = ns;
  }

  public override bool Equals(Type that, bool keepConstraints = false) {
    var i = NormalizeExpand(keepConstraints);
    if (i is UserDefinedType) {
      var ii = (UserDefinedType)i;
      var t = that.NormalizeExpand(keepConstraints) as UserDefinedType;
      if (t == null || ii.ResolvedClass != t.ResolvedClass || ii.TypeArgs.Count != t.TypeArgs.Count) {
        return false;
      } else {
        for (int j = 0; j < ii.TypeArgs.Count; j++) {
          if (!ii.TypeArgs[j].Equals(t.TypeArgs[j], keepConstraints)) {
            return false;
          }
        }
        return true;
      }
    } else {
      // TODO?: return i.Equals(that.NormalizeExpand());
      return i.Equals(that, keepConstraints);
    }
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    if (ResolvedClass is TypeParameter tp) {
      if (subst.TryGetValue(tp, out var s)) {
        Contract.Assert(TypeArgs.Count == 0);
        return s;
      } else {
        return this;
      }
    } else if (ResolvedClass != null) {
      List<Type> newArgs = null;  // allocate it lazily
      var resolvedClass = ResolvedClass;
      var isArrowType = ArrowType.IsPartialArrowTypeName(resolvedClass.Name) || ArrowType.IsTotalArrowTypeName(resolvedClass.Name);
      for (int i = 0; i < TypeArgs.Count; i++) {
        Type p = TypeArgs[i];
        Type s = p.Subst(subst);
        if (s is InferredTypeProxy && !isArrowType) {
          ((InferredTypeProxy)s).KeepConstraints = true;
        }
        if (s != p && newArgs == null) {
          // lazily construct newArgs
          newArgs = new List<Type>();
          for (int j = 0; j < i; j++) {
            newArgs.Add(TypeArgs[j]);
          }
        }
        if (newArgs != null) {
          newArgs.Add(s);
        }
      }
      if (newArgs == null) {
        // there were no substitutions
        return this;
      } else {
        // Note, even if t.NamePath is non-null, we don't care to keep that syntactic part of the expression in what we return here
        return new UserDefinedType(Tok, Name, resolvedClass, newArgs);
      }
    } else {
      // there's neither a resolved param nor a resolved class, which means the UserDefinedType wasn't
      // properly resolved; just return it
      return this;
    }
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new UserDefinedType(Tok, Name, ResolvedClass, arguments);
  }

  /// <summary>
  /// If type denotes a resolved class type, then return that class type.
  /// Otherwise, return null.
  /// </summary>
  public static UserDefinedType DenotesClass(Type type) {
    Contract.Requires(type != null);
    Contract.Ensures(Contract.Result<UserDefinedType>() == null || Contract.Result<UserDefinedType>().ResolvedClass is ClassDecl);
    type = type.NormalizeExpand();
    UserDefinedType ct = type as UserDefinedType;
    if (ct != null && ct.ResolvedClass is ClassDecl) {
      return ct;
    } else {
      return null;
    }
  }

  public static Type ArrayElementType(Type type) {
    Contract.Requires(type != null);
    Contract.Requires(type.IsArrayType);
    Contract.Ensures(Contract.Result<Type>() != null);

    UserDefinedType udt = DenotesClass(type);
    Contract.Assert(udt != null);
    Contract.Assert(udt.TypeArgs.Count == 1);  // holds true of all array types
    return udt.TypeArgs[0];
  }

  /// <summary>
  /// This method converts a UserDefinedType given in an "extends" clause to the TraitDecl it refers to.
  /// Return null if the UserDefinedType does not refer to a trait in this way.
  /// </summary>
  [CanBeNull]
  public TraitDecl AsParentTraitDecl() {
    // If .Name == "Tr" and "Tr" is a reference-type trait, then .ResolvedClass will be a NonNullTypeDecl
    // whose .ViewAsClass is that trait declaration we're looking for.
    if (ResolvedClass is NonNullTypeDecl { ViewAsClass: TraitDecl trait0 }) {
      Contract.Assert(trait0.IsReferenceTypeDecl);
      return trait0;
    }
    // If .Name == "Tr?" where "Tr" is a reference trait, then the "extends" clause is malformed. In this case,
    // .ResolvedClass will still be a TraitDecl, but we don't want to return it. To distinguish this case, we
    // compare the given .Name with the name of the trait declaration.
    if (ResolvedClass is TraitDecl trait1 && trait1.Name == Name) {
      Contract.Assert(!trait1.IsReferenceTypeDecl);
      return trait1;
    }
    return null;
  }

  public override IEnumerable<Node> Nodes => new[] { this }.Concat(TypeArgs.SelectMany(t => t.Nodes));

  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    Contract.Ensures(Contract.Result<string>() != null);
    if (SystemModuleManager.IsTupleTypeName(Name)) {
      // Unfortunately, ResolveClass may be null, so Name is all we have.  Reverse-engineer the string name.
      IEnumerable<bool> argumentGhostness = SystemModuleManager.ArgumentGhostnessFromString(Name, TypeArgs.Count);
      return "(" + Util.Comma(System.Linq.Enumerable.Zip(TypeArgs, argumentGhostness),
        (ty_u) => ModuleResolver.GhostPrefix(ty_u.Item2) + ty_u.Item1.TypeName(options, context, parseAble)) + ")";
    } else if (ArrowType.IsPartialArrowTypeName(Name)) {
      return ArrowType.PrettyArrowTypeName(options, ArrowType.PARTIAL_ARROW, TypeArgs, null, context, parseAble);
    } else if (ArrowType.IsTotalArrowTypeName(Name)) {
      return ArrowType.PrettyArrowTypeName(options, ArrowType.TOTAL_ARROW, TypeArgs, null, context, parseAble);
    } else {
#if TEST_TYPE_SYNONYM_TRANSPARENCY
        if (Name == "type#synonym#transparency#test" && ResolvedClass is TypeSynonymDecl) {
          return ((TypeSynonymDecl)ResolvedClass).Rhs.TypeName(context);
        }
#endif
      var s = Printer.ExprToString(options, NamePath);
      if (ResolvedClass != null) {
        var optionalTypeArgs = NamePath is NameSegment ? ((NameSegment)NamePath).OptTypeArguments : ((ExprDotName)NamePath).OptTypeArguments;
        if (optionalTypeArgs == null && TypeArgs != null && TypeArgs.Count != 0) {
          s += this.TypeArgsToString(options, context, parseAble);
        }
      }
      return s;
    }
  }

  public override bool SupportsEquality {
    get {
      if (ResolvedClass is ClassLikeDecl { IsReferenceTypeDecl: true }) {
        return ResolvedClass.IsRevealedInScope(Type.GetScope());
      } else if (ResolvedClass is TraitDecl) {
        return false;
      } else if (ResolvedClass is CoDatatypeDecl) {
        return false;
      } else if (ResolvedClass is IndDatatypeDecl) {
        var dt = (IndDatatypeDecl)ResolvedClass;
        Contract.Assume(dt.EqualitySupport != IndDatatypeDecl.ES.NotYetComputed);
        if (!dt.IsRevealedInScope(Type.GetScope())) {
          return false;
        }
        if (dt.EqualitySupport == IndDatatypeDecl.ES.Never) {
          return false;
        }
        Contract.Assert(dt.TypeArgs.Count == TypeArgs.Count);
        var i = 0;
        foreach (var tp in dt.TypeArgs) {
          if (tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype && !TypeArgs[i].SupportsEquality) {
            return false;
          }
          i++;
        }
        return true;
      } else if (ResolvedClass is NewtypeDecl newtypeDecl) {
        if (newtypeDecl.IsRevealedInScope(Type.GetScope())) {
          return newtypeDecl.RhsWithArgument(TypeArgs).SupportsEquality;
        } else {
          return false;
        }
      } else if (ResolvedClass is TypeSynonymDeclBase) {
        var t = (TypeSynonymDeclBase)ResolvedClass;
        if (t.SupportsEquality) {
          return true;
        } else if (t.IsRevealedInScope(Type.GetScope())) {
          return t.RhsWithArgument(TypeArgs).SupportsEquality;
        } else {
          return false;
        }
      } else if (ResolvedClass is TypeParameter) {
        return ((TypeParameter)ResolvedClass).SupportsEquality;
      } else if (ResolvedClass is AbstractTypeDecl) {
        return ((AbstractTypeDecl)ResolvedClass).SupportsEquality;
      }
      Contract.Assume(false);  // the SupportsEquality getter requires the Type to have been successfully resolved
      return true;
    }
  }

  public override bool PartiallySupportsEquality {
    get {
      var totalEqualitySupport = SupportsEquality;
      if (!totalEqualitySupport && ResolvedClass is TypeSynonymDeclBase synonymBase) {
        return synonymBase.IsRevealedInScope(Type.GetScope()) && synonymBase.RhsWithArgument(TypeArgs).PartiallySupportsEquality;
      } else if (!totalEqualitySupport && ResolvedClass is IndDatatypeDecl dt && dt.IsRevealedInScope(Type.GetScope())) {
        // Equality is partially supported (at run time) for a datatype that
        //   * is inductive (because codatatypes never support equality), and
        //   * has at least one non-ghost constructor (because if all constructors are ghost, then equality is never supported), and
        //   * for each non-ghost constructor, every argument totally supports equality (an argument totally supports equality
        //       if it is non-ghost (because ghost arguments are not available at run time) and has a type that supports equality).
        var hasNonGhostConstructor = false;
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          hasNonGhostConstructor = true;
          if (!ctor.Formals.All(formal => !formal.IsGhost && formal.Type.SupportsEquality)) {
            return false;
          }
        }
        Contract.Assert(dt.HasGhostVariant); // sanity check (if the types of all formals support equality, then either .SupportsEquality or there is a ghost constructor)
        return hasNonGhostConstructor;
      }
      return totalEqualitySupport;
    }
  }

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    if (ResolvedClass is ArrowTypeDecl) {
      return TypeArgs.Any(ta => ta.ComputeMayInvolveReferences(visitedDatatypes));
    } else if (ResolvedClass is ClassLikeDecl) {
      return true;
    } else if (ResolvedClass is NewtypeDecl) {
      return false;
    } else if (ResolvedClass is DatatypeDecl) {
      // Datatype declarations do not support explicit (!new) annotations. Instead, whether or not
      // a datatype involves references depends on the definition and parametrization of the type.
      // See ComputeMayInvolveReferences in class Type for more information.
      // In particular, if one of the datatype's constructors mentions a type that involves
      // references, then so does the datatype. And if one of the datatype's type arguments involves
      // references, then we consider the datatype to do so as well (without regard to whether or
      // not the type parameter is actually used in the definition of the datatype).
      var dt = (DatatypeDecl)ResolvedClass;
      if (!dt.IsRevealedInScope(Type.GetScope())) {
        // The type's definition is hidden from the current scope, so we
        // have to assume the type may involve references.
        return true;
      } else if (TypeArgs.Any(ta => ta.ComputeMayInvolveReferences(visitedDatatypes))) {
        return true;
      } else if (visitedDatatypes != null && visitedDatatypes.Contains(dt)) {
        // we're in the middle of looking through the types involved in dt's definition
        return false;
      } else {
        visitedDatatypes ??= new HashSet<DatatypeDecl>();
        visitedDatatypes.Add(dt);
        return dt.Ctors.Any(ctor => ctor.Formals.Any(f => f.Type.ComputeMayInvolveReferences(visitedDatatypes)));
      }
    } else if (ResolvedClass is TypeSynonymDeclBase) {
      var t = (TypeSynonymDeclBase)ResolvedClass;
      if (t.Characteristics.ContainsNoReferenceTypes) {
        // There's an explicit "(!new)" annotation on the type.
        return false;
      } else if (t.IsRevealedInScope(Type.GetScope())) {
        // The type's definition is available in the scope, so consult the RHS type
        return t.RhsWithArgument(TypeArgs).ComputeMayInvolveReferences(visitedDatatypes);
      } else {
        // The type's definition is hidden from the current scope and there's no explicit "(!new)", so we
        // have to assume the type may involve references.
        return true;
      }
    } else if (ResolvedClass is TypeParameter typeParameter) {
      if (visitedDatatypes != null) {
        // Datatypes look at the type arguments passed in, so we ignore their formal type parameters.
        // See comment above and in Type.ComputeMayInvolveReferences.
        Contract.Assert(typeParameter.Parent is DatatypeDecl);
        return false;
      } else {
        return !typeParameter.Characteristics.ContainsNoReferenceTypes;
      }
    } else if (ResolvedClass is AbstractTypeDecl opaqueTypeDecl) {
      return !opaqueTypeDecl.Characteristics.ContainsNoReferenceTypes;
    }
    Contract.Assume(false);  // unexpected or not successfully resolved Type
    return true;
  }

  public override List<Type> ParentTypes(bool includeTypeBounds) {
    return ResolvedClass != null ? ResolvedClass.ParentTypes(TypeArgs, includeTypeBounds) : base.ParentTypes(includeTypeBounds);
  }

  public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    super = super.NormalizeExpandKeepConstraints();

    // Specifically handle object as the implicit supertype of classes and traits.
    // "object?" is handled by Builtins rather than the Type hierarchy, so unfortunately
    // it can't be returned in ParentTypes().
    if (super.IsObjectQ) {
      return IsRefType;
    } else if (super.IsObject) {
      return ignoreNullity ? IsRefType : IsNonNullRefType;
    }

    return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
  }

  public IEnumerable<Reference> GetReferences() {
    return new[] { new Reference(Tok, ResolvedClass) };
  }

  public override IEnumerable<INode> Children => base.Children.Concat(new[] { NamePath });

  public override IEnumerable<INode> PreResolveChildren => new List<Node>() { NamePath };
}