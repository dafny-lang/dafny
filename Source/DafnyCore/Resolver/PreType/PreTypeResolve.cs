//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny {
  public abstract class ResolverPass {
    public readonly ModuleResolver resolver;

    protected ResolverPass(ModuleResolver resolver) {
      Contract.Requires(resolver != null);
      this.resolver = resolver;
    }

    protected int ErrorCount => resolver.Reporter.Count(ErrorLevel.Error);

    protected void ReportError(Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(d.tok, msg, args);
    }

    protected void ReportError(Statement stmt, string msg, params object[] args) {
      Contract.Requires(stmt != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(stmt.Tok, msg, args);
    }

    protected void ReportError(Expression expr, string msg, params object[] args) {
      Contract.Requires(expr != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(expr.tok, msg, args);
    }

    public void ReportError(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Error(MessageSource.Resolver, tok, msg, args);
    }

    public void ReportWarning(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Warning(MessageSource.Resolver, ParseErrors.ErrorId.none, tok, msg, args);
    }

    protected void ReportInfo(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Info(MessageSource.Resolver, tok, msg, args);
    }
  }

  public partial class PreTypeResolver : ResolverPass {
    private readonly Scope<IVariable> scope;
    public ErrorReporter Reporter => resolver.Reporter;
    public DafnyOptions Options => resolver.Options;
    public Scope<IVariable> Scope => scope;

    TopLevelDeclWithMembers currentClass;
    Method currentMethod;

    private readonly Dictionary<string, TopLevelDecl> preTypeBuiltins = new();
    public readonly PreTypeConstraints Constraints;

    TopLevelDecl BuiltInTypeDecl(string name) {
      Contract.Requires(name != null);
      if (preTypeInferenceModuleState.PreTypeBuiltins.TryGetValue(name, out var decl)) {
        return decl;
      }
      if (IsArrayName(name, out var dims)) {
        // make sure the array class has been created
        SystemModuleManager.ArrayType(Token.NoToken, dims,
          new List<Type> { new InferredTypeProxy() }, true).ModifyBuiltins(resolver.SystemModuleManager);
        decl = resolver.SystemModuleManager.arrayTypeDecls[dims];
      } else if (IsBitvectorName(name, out var width)) {
        var bvDecl = (ValuetypeDecl)resolver.SystemModuleManager.SystemModule.SourceDecls.Find(topLevelDecl => topLevelDecl.Name == name);
        if (bvDecl == null) {
          bvDecl = resolver.AddBitvectorTypeDecl(name, width);
        }
        preTypeInferenceModuleState.PreTypeBuiltins.Add(name, bvDecl);
        FillInPreTypesInSignature(bvDecl);
        foreach (var bitvectorMember in bvDecl.Members) {
          FillInPreTypesInSignature(bitvectorMember);
        }
        return bvDecl;
      } else {
        decl = null;
        foreach (var valueTypeDecl in resolver.ProgramResolver.SystemModuleManager.valuetypeDecls) {
          if (valueTypeDecl.Name == name) {
            // bool, int, real, ORDINAL, map, imap
            decl = valueTypeDecl;
            break;
          }
        }
        if (decl == null) {
          if (name is PreType.TypeNameSet or PreType.TypeNameSeq or PreType.TypeNameMultiset) {
            var variances = new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Strict };
            decl = new ValuetypeDecl(name, resolver.SystemModuleManager.SystemModule, variances, _ => false, null);
          } else if (name == PreType.TypeNameIset) {
            var variances = new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Permissive };
            decl = new ValuetypeDecl(name, resolver.SystemModuleManager.SystemModule, variances, _ => false, null);
          } else if (name == PreType.TypeNameObjectQ) {
            decl = resolver.SystemModuleManager.ObjectDecl;
          } else {
            decl = new ValuetypeDecl(name, resolver.SystemModuleManager.SystemModule, _ => false, null);
          }
        }
      }
      preTypeInferenceModuleState.PreTypeBuiltins.Add(name, decl);
      return decl;
    }

    TopLevelDecl BuiltInArrowTypeDecl(int arity) {
      Contract.Requires(0 <= arity);
      var name = ArrowType.ArrowTypeName(arity);
      if (!preTypeInferenceModuleState.PreTypeBuiltins.TryGetValue(name, out var decl)) {
        // the arrow type declaration should already have been created by the parser
        decl = resolver.SystemModuleManager.ArrowTypeDecls[arity];
        preTypeInferenceModuleState.PreTypeBuiltins.Add(name, decl);
      }
      return decl;
    }

    DPreType BuiltInArrowType(List<PreType> inPreTypes, PreType resultPreType) {
      return new DPreType(BuiltInArrowTypeDecl(inPreTypes.Count), Util.Snoc(inPreTypes, resultPreType));
    }

    DPreType BuiltInArrayType(int dims, PreType elementPreType) {
      Contract.Requires(1 <= dims);
      var arrayName = dims == 1 ? PreType.TypeNameArray : $"{PreType.TypeNameArray}{dims}";
      return new DPreType(BuiltInTypeDecl(arrayName), new List<PreType>() { elementPreType });
    }

    private int typeProxyCount = 0; // used to give each PreTypeProxy a unique ID

    public readonly List<(PreTypeProxy, string)> allPreTypeProxies = new();

    public PreType CreatePreTypeProxy(string description = null) {
      var proxy = new PreTypeProxy(typeProxyCount++);
      allPreTypeProxies.Add((proxy, description));
      return proxy;
    }

    /// <summary>
    /// This method can be used when .PreType has been found to be erroneous and its current value
    /// would be unexpected by the rest of the resolver. This method then sets .Type and .PreType to neutral values.
    /// </summary>
    void ResetTypeAssignment(Expression expr) {
      expr.PreType = CreatePreTypeProxy();
      expr.ResetTypeAssignment();
    }

    public enum Type2PreTypeOption { GoodForInference, GoodForPrinting, GoodForBoth }

    public PreType Type2PreType(Type type, string description = null, Type2PreTypeOption option = Type2PreTypeOption.GoodForBoth) {
      Contract.Requires(type != null);

      type = type.Normalize(); // keep type synonyms
      if (type.AsTypeSynonym is { } typeSynonymDecl && option != Type2PreTypeOption.GoodForInference &&
          typeSynonymDecl.IsRevealedInScope(Type.GetScope())) {
        // Compute a pre-type for the non-instantiated ("raw") RHS type (that is, for the RHS of the type-synonym declaration with the
        // formal type parameters of the type-synonym declaration).
        var rawRhsType = UserDefinedType.FromTopLevelDecl(typeSynonymDecl.tok, typeSynonymDecl);
        var preTypeArguments = type.TypeArgs.ConvertAll(ty => Type2PreType(ty, null, Type2PreTypeOption.GoodForBoth));

        // The printable pre-type is the original type synonym, but with preTypeArguments as arguments
        var printablePreType = new DPreType(typeSynonymDecl, preTypeArguments);

        // The expanded pre-type is the raw RHS pre-type, but substituting in preTypeArguments for the type parameters
        var rawRhsPreTypeForInference = Type2PreType(rawRhsType, null, Type2PreTypeOption.GoodForInference);
        var preType = rawRhsPreTypeForInference.Substitute(PreType.PreTypeSubstMap(typeSynonymDecl.TypeArgs, preTypeArguments));

        // Typically, preType is a DPreType. However, it could be that the RHS of the type synonym fizzles out to just one of the type
        // parameters of the type synonym, and if that type synonym started off a proxy, then "preType" will be a proxy.
        if (preType is DPreType dPreType) {
          return new DPreType(dPreType.Decl, dPreType.Arguments, printablePreType);
        } else {
          // TODO: it would be nice to have a place to include "printablePreType" as part of what's returned, but currently only DPreType allows that
          return preType;
        }
      }

      type = type.NormalizeExpandKeepConstraints(); // blow past proxies and type synonyms
      if (type.AsSubsetType is { } subsetType) {
        ResolvePreTypeSignature(subsetType);
        Contract.Assert(subsetType.Var.PreType != null);
        var typeArguments = type.TypeArgs.ConvertAll(ty => Type2PreType(ty, null, option));
        var preTypeMap = PreType.PreTypeSubstMap(subsetType.TypeArgs, typeArguments);
        return subsetType.Var.PreType.Substitute(preTypeMap);
      } else if (type is UserDefinedType { ResolvedClass: NewtypeDecl newtypeDecl }) {
        // Make sure the newtype declaration itself has been pre-type resolved
        ResolvePreTypeSignature(newtypeDecl);
        Contract.Assert(newtypeDecl.Var == null || newtypeDecl.Var.PreType != null);
        Contract.Assert(newtypeDecl.BasePreType != null);
      }

      if (type is TypeProxy) {
        return CreatePreTypeProxy(description ?? $"from type proxy {type}");
      }

      var decl = Type2Decl(type);
      var arguments = type.TypeArgs.ConvertAll(ty => Type2PreType(ty, null, option));
      return new DPreType(decl, arguments);
    }

    public TopLevelDecl Type2Decl(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(type is NonProxyType and not SelfType);
      TopLevelDecl decl;
      if (type is BoolType) {
        decl = BuiltInTypeDecl(PreType.TypeNameBool);
      } else if (type is CharType) {
        decl = BuiltInTypeDecl(PreType.TypeNameChar);
      } else if (type is IntType) {
        decl = BuiltInTypeDecl(PreType.TypeNameInt);
      } else if (type is RealType) {
        decl = BuiltInTypeDecl(PreType.TypeNameReal);
      } else if (type is BigOrdinalType) {
        decl = BuiltInTypeDecl(PreType.TypeNameORDINAL);
      } else if (type is BitvectorType bitvectorType) {
        decl = BuiltInTypeDecl(PreType.TypeNameBvPrefix + bitvectorType.Width);
      } else if (type is CollectionType) {
        var name =
          type is SetType st ? PreType.SetTypeName(st.Finite) :
          type is MultiSetType ? PreType.TypeNameMultiset :
          type is MapType mt ? PreType.MapTypeName(mt.Finite) :
          PreType.TypeNameSeq;
        decl = BuiltInTypeDecl(name);
      } else if (type is ArrowType at) {
        decl = BuiltInArrowTypeDecl(at.Arity);
      } else if (type is UserDefinedType udt) {
        decl = udt.ResolvedClass;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return decl;
    }

    /// <summary>
    /// Returns the non-newtype ancestor of "decl".
    /// This method assumes that the ancestors of "decl" do not form any cycles. That is, any such cycle detection must already
    /// have been done.
    /// </summary>
    public static TopLevelDecl AncestorDecl(TopLevelDecl decl) {
      while (decl is NewtypeDecl newtypeDecl) {
        var parent = newtypeDecl.BasePreType.Normalize();
        decl = ((DPreType)parent).Decl;
      }
      return decl;
    }

    /// <summary>
    /// Returns the non-newtype ancestor pre-type of "preType".
    /// This method assumes that the ancestors of "preType.Decl" do not form any cycles. That is, any such cycle detection must already
    /// have been done.
    /// </summary>
    public static DPreType AncestorPreType(DPreType preType) {
      while (preType.Decl is NewtypeDecl newtypeDecl) {
        var subst = PreType.PreTypeSubstMap(newtypeDecl.TypeArgs, preType.Arguments);
        preType = (DPreType)newtypeDecl.BasePreType.Substitute(subst);
      }
      return preType;
    }

    [CanBeNull]
    public static string AncestorName(PreType preType) {
      var dp = preType.Normalize() as DPreType;
      return dp == null ? null : AncestorDecl(dp.Decl).Name;
    }

    /// <summary>
    /// Returns the non-newtype ancestor of "preType".
    /// If the ancestor chain has a cycle or if some part of the chain hasn't yet been resolved, this method ends the traversal
    /// early (and returns the last ancestor traversed). This method does not return any error; that's assumed to be done elsewhere.
    /// </summary>
    public static DPreType NewTypeAncestor(DPreType preType) {
      Contract.Requires(preType != null);
      ISet<NewtypeDecl> visited = null;
      while (preType.Decl is NewtypeDecl newtypeDecl) {
        visited ??= new HashSet<NewtypeDecl>();
        if (visited.Contains(newtypeDecl)) {
          // The parents of the originally given "preType" are in a cycle; the error has been reported elsewhere, but here we just want to get out
          break;
        }
        visited.Add(newtypeDecl);
        var parent = newtypeDecl.BasePreType.Normalize() as DPreType;
        if (parent == null) {
          // The parent type of this newtype apparently hasn't been inferred yet, so stop traversal here
          break;
        }
        var subst = PreType.PreTypeSubstMap(newtypeDecl.TypeArgs, preType.Arguments);
        preType = (DPreType)parent.Substitute(subst);
      }
      return preType;
    }

    public static bool HasTraitSupertypes(DPreType dp) {
      /*
       * When traits can be used as supertypes for non-reference types (and "object" is an implicit parent trait of every
       * class), then this method can be implemented by
       *         return dp.Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0;
       * For now, every reference type except "object" has trait supertypes.
       */
      if (dp.Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0) {
        // this type has explicitly declared parent traits
        return true;
      }
      if (dp.Decl is TraitDecl trait && trait.IsObjectTrait) {
        // the built-in type "object" has no parent traits
        return false;
      }
      // any non-object reference type has "object" as an implicit parent trait
      return DPreType.IsReferenceTypeDecl(dp.Decl);
    }

    /// <summary>
    /// Add to "ancestors" every TopLevelDecl that is a reflexive, transitive parent of "d",
    /// but not exploring past any TopLevelDecl that is already in "ancestors".
    /// </summary>
    public static void ComputeAncestors(TopLevelDecl decl, ISet<TopLevelDecl> ancestors, SystemModuleManager systemModuleManager) {
      if (!ancestors.Contains(decl)) {
        ancestors.Add(decl);
        if (decl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
          topLevelDeclWithMembers.ParentTraitHeads.ForEach(parent => ComputeAncestors(parent, ancestors, systemModuleManager));
        }
        if (decl is TraitDecl { IsObjectTrait: true }) {
          // we're done
        } else if (DPreType.IsReferenceTypeDecl(decl)) {
          // object is also a parent type
          ComputeAncestors(systemModuleManager.ObjectDecl, ancestors, systemModuleManager);
        }
      }
    }

    /// <summary>
    /// Return "true" if "super" is a super-(pre)type of "sub".
    /// Otherwise, return "false".
    /// Note, if either "super" or "sub" contains a type proxy, then "false" is returned.
    /// </summary>
    public bool IsSuperPreTypeOf(DPreType super, DPreType sub) {
      var subAncestors = new HashSet<TopLevelDecl>();
      ComputeAncestors(sub.Decl, subAncestors, resolver.SystemModuleManager);
      if (!subAncestors.Contains(super.Decl)) {
        return false;
      }
      sub = sub.AsParentType(super.Decl, this);
      var argumentCount = super.Decl.TypeArgs.Count;
      Contract.Assert(super.Arguments.Count == argumentCount);
      Contract.Assert(sub.Arguments.Count == argumentCount);
      for (var i = 0; i < argumentCount; i++) {
        var superI = super.Arguments[i].Normalize() as DPreType;
        var subI = sub.Arguments[i].Normalize() as DPreType;
        if (superI == null || subI == null) {
          return false;
        }
        if (super.Decl.TypeArgs[i].Variance != TypeParameter.TPVariance.Contra && !IsSuperPreTypeOf(superI, subI)) {
          return false;
        }
        if (super.Decl.TypeArgs[i].Variance != TypeParameter.TPVariance.Co && !IsSuperPreTypeOf(subI, superI)) {
          return false;
        }
      }
      return true;
    }

    public static bool IsBitvectorName(string name, out int width) {
      Contract.Requires(name != null);
      if (name.StartsWith(PreType.TypeNameBvPrefix)) {
        var bits = name.Substring(2);
        width = 0; // set to 0, in case the first disjunct of the next line evaluates to true
        return bits == "0" || (bits.Length != 0 && bits[0] != '0' && int.TryParse(bits, out width));
      }
      width = 0; // unused by caller
      return false;
    }

    public static bool IsBitvectorName(string name) {
      return IsBitvectorName(name, out _);
    }

    public static bool IsArrayName(string name, out int dimensions) {
      Contract.Requires(name != null);
      if (name.StartsWith(PreType.TypeNameArray)) {
        var dims = name[PreType.TypeNameArray.Length..];
        if (dims.Length == 0) {
          dimensions = 1;
          return true;
        } else if (dims[0] != '0' && dims != "1" && int.TryParse(dims, out dimensions)) {
          return true;
        }
      }
      dimensions = 0; // unused by caller
      return false;
    }

    private class PreTypeInferenceModuleState {
      public readonly ISet<Declaration> StillNeedsPreTypeSignature;
      public readonly Stack<Declaration> InFirstPhase = new Stack<Declaration>();
      public readonly Dictionary<string, TopLevelDecl> PreTypeBuiltins;

      public PreTypeInferenceModuleState(List<Declaration> declarations, Dictionary<string, TopLevelDecl> preTypeBuiltins) {
        StillNeedsPreTypeSignature = new HashSet<Declaration>(declarations);
        PreTypeBuiltins = preTypeBuiltins;
      }
    }

    private readonly PreTypeInferenceModuleState preTypeInferenceModuleState;

    private PreTypeResolver(ModuleResolver resolver, PreTypeInferenceModuleState preTypeInferenceModuleState)
      : base(resolver) {
      this.preTypeInferenceModuleState = preTypeInferenceModuleState;

      scope = new Scope<IVariable>(resolver.Options);
      EnclosingStatementLabels = new Scope<Statement>(resolver.Options);
      dominatingStatementLabels = new Scope<Label>(resolver.Options);
      Constraints = new PreTypeConstraints(this);
    }

    void ScopePushAndReport(IVariable v, string kind, bool assignPreType = true) {
      Contract.Requires(scope != null);
      Contract.Requires(v != null);
      Contract.Requires(kind != null);
      if (assignPreType) {
        Contract.Assert(v.PreType == null);
        v.PreType = Type2PreType(v.Type, $"type of identifier '{v.Name}'");
        Contract.Assert(v.PreType is not DPreType { Decl: null }); // sanity check that the .Decl field was set
      } else {
        Contract.Assert(v.PreType != null);
      }
      ScopePushAndReport(scope, v.Name, v, v.Tok, kind);
    }

    void ScopePushExpectSuccess(IVariable v, string kind, bool assignPreType = true) {
      Contract.Requires(scope != null);
      Contract.Requires(v != null);
      Contract.Requires(kind != null);
      if (assignPreType) {
        Contract.Assert(v.PreType == null);
        v.PreType = Type2PreType(v.Type, $"type of identifier '{v.Name}'");
      } else {
        Contract.Assert(v.PreType != null);
      }
      var r = ScopePushAndReport(scope, v.Name, v, v.Tok, kind);
      Contract.Assert(r == Scope<IVariable>.PushResult.Success);
    }

    private Scope<Thing>.PushResult ScopePushAndReport<Thing>(Scope<Thing> scope, string name, Thing thing, IToken tok, string kind) where Thing : class {
      Contract.Requires(scope != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      Contract.Requires(tok != null);
      Contract.Requires(kind != null);
      var r = scope.Push(name, thing);
      switch (r) {
        case Scope<Thing>.PushResult.Success:
          break;
        case Scope<Thing>.PushResult.Duplicate:
          ReportError(tok, "Duplicate {0} name: {1}", kind, name);
          break;
        case Scope<Thing>.PushResult.Shadow:
          ReportWarning(tok, "Shadowed {0} name: {1}", kind, name);
          break;
      }
      return r;
    }

    void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString) {
      Constraints.AddSubtypeConstraint(super, sub, tok, errorFormatString);
    }

    void AddConfirmation(PreTypeConstraints.CommonConfirmationBag check, PreType preType, IToken tok, string errorFormatString, Action onProxyAction = null) {
      Constraints.AddConfirmation(check, preType, tok, errorFormatString, onProxyAction);
    }

    void AddComparableConstraint(PreType a, PreType b, IToken tok, bool allowBaseTypeCast, string errorFormatString) {
      // A "comparable types" constraint involves a disjunction. This can get gnarly for inference, so the full disjunction
      // is checked post inference. The constraint can, however, be of use during inference, so we also add an approximate
      // constraint (which is set up NOT to generate any error messages by itself, since otherwise errors would be duplicated).
      Constraints.AddGuardedConstraint(() => ApproximateComparableConstraints(a, b, tok, allowBaseTypeCast,
        "(Duplicate error message) " + errorFormatString, false));
      Constraints.AddConfirmation(tok, () => CheckComparableTypes(a, b, allowBaseTypeCast), () => string.Format(errorFormatString, a, b));
    }

    /// <summary>
    /// This method returns whether or not A and B are comparable types (notated with the constraint A ~~ B).
    ///
    /// The meaning of a comparable constraint
    ///     A ~~ B
    /// is the disjunction
    ///     A ::> B    or    B ::> A
    ///
    /// If "!allowConversion", then "X ::> Y" means
    ///     X :> Y
    ///
    /// If "allowConversion", then "X ::> Y" means
    ///     X' :> Y', or
    ///     X' and Y' are various bv types, or
    ///     X' is int and Y' is in {int, char, bv, ORDINAL, real}.
    /// where X' and Y' are the newtype ancestors of X and Y, respectively.
    /// Additionally, under the legacy option /generalNewtypes:0 (which will be phased out over time), the latter also allows
    /// several additional cases, see IsConversionCompatible.
    /// </summary>
    bool CheckComparableTypes(PreType a, PreType b, bool allowConversion) {
      if (PreType.Same(a, b)) {
        // this allows the case where "a" and "b" are proxies that are equal
        return true;
      }
      if (a.Normalize() is not DPreType aa || b.Normalize() is not DPreType bb) {
        return false;
      }
      if (IsSuperPreTypeOf(aa, bb) || IsSuperPreTypeOf(bb, aa)) {
        return true;
      }
      if (!allowConversion) {
        return false;
      }
      if (IsConversionCompatible(aa, bb) || IsConversionCompatible(bb, aa)) {
        return true;
      }
      return false;
    }

    bool IsConversionCompatible(DPreType fromType, DPreType toType) {
      var fromAncestor = AncestorPreType(fromType);
      var toAncestor = AncestorPreType(toType);

      if (PreType.Same(fromAncestor, toAncestor)) {
        return true;
      }
      var fromFamily = fromAncestor.Decl.Name;
      var toFamily = toAncestor.Decl.Name;
      var toName = toType.Decl.Name;

      if (IsBitvectorName(fromFamily) && (toFamily == PreType.TypeNameInt || IsBitvectorName(toFamily))) {
        return true;
      }
      if (fromFamily == PreType.TypeNameInt && toName is PreType.TypeNameChar or PreType.TypeNameReal or PreType.TypeNameORDINAL) {
        return true;
      }

      var legacy = !resolver.Options.Get(CommonOptionBag.GeneralNewtypes);
      if (legacy) {
        if (fromFamily == PreType.TypeNameReal &&
            (toFamily is PreType.TypeNameInt or PreType.TypeNameChar or PreType.TypeNameORDINAL || IsBitvectorName(toFamily))) {
          return true;
        }
        if (fromFamily == PreType.TypeNameChar && (toFamily is PreType.TypeNameInt or PreType.TypeNameORDINAL || IsBitvectorName(toFamily))) {
          return true;
        }
        if (IsBitvectorName(fromFamily) &&
            (toFamily is PreType.TypeNameInt or PreType.TypeNameReal or PreType.TypeNameChar or PreType.TypeNameORDINAL)) {
          return true;
        }
      }

      return false;
    }

    bool ApproximateComparableConstraints(PreType a, PreType b, IToken tok, bool allowBaseTypeCast, string errorFormatString, bool reportErrors = true) {
      // See CheckComparableTypes for the meaning of "comparable type".
      // To decide between these two possibilities, enough information must be available about A and/or B.
      var normalizedA = a.Normalize() as DPreType;
      var normalizedB = b.Normalize() as DPreType;
      if (normalizedA != null && normalizedB != null && normalizedA.Decl != normalizedB.Decl) {
        var subArguments = Constraints.GetTypeArgumentsForSuperType(normalizedB.Decl, normalizedA, allowBaseTypeCast);
        if (subArguments != null) {
          // use B :> A
          var aa = new DPreType(normalizedB.Decl, subArguments, normalizedA.PrintablePreType);
          Constraints.DebugPrint($"    DEBUG: turning ~~ into {b} :> {aa}");
          Constraints.AddSubtypeConstraint(b, aa, tok, errorFormatString, null, reportErrors);
          return true;
        }
        subArguments = Constraints.GetTypeArgumentsForSuperType(normalizedA.Decl, normalizedB, allowBaseTypeCast);
        if (subArguments != null) {
          // use A :> B
          var bb = new DPreType(normalizedA.Decl, subArguments, normalizedB.PrintablePreType);
          Constraints.DebugPrint($"    DEBUG: turning ~~ into {a} :> {bb}");
          Constraints.AddSubtypeConstraint(a, bb, tok, errorFormatString, null, reportErrors);
          return true;
        }

        if (allowBaseTypeCast && (IsConversionCompatible(normalizedA, normalizedB) || IsConversionCompatible(normalizedB, normalizedA))) {
          return true;
        }

        // neither A :> B nor B :> A is possible
        if (reportErrors) {
          ReportError(tok, errorFormatString, a, b);
        }
        return true;
      }

      if (!allowBaseTypeCast) {
        if ((normalizedA != null && normalizedA.IsLeafType()) || (normalizedB != null && normalizedB.IsRootType())) {
          // use B :> A
          Constraints.DebugPrint($"    DEBUG: turning ~~ into {b} :> {a}");
          Constraints.AddSubtypeConstraint(b, a, tok, errorFormatString, null, reportErrors);
          return true;
        } else if ((normalizedA != null && normalizedA.IsRootType()) || (normalizedB != null && normalizedB.IsLeafType())) {
          // use A :> B
          Constraints.DebugPrint($"    DEBUG: turning ~~ into {a} :> {b}");
          Constraints.AddSubtypeConstraint(a, b, tok, errorFormatString, null, reportErrors);
          return true;
        }
      }

      if (normalizedA != null && normalizedB != null && normalizedA.Decl == normalizedB.Decl) {
        // Here is where we approximate the answer. We'll only constrain that variant type parameters are *comparable*, not that
        // they are consistently comparable. For example, if ptA is C<A0, A1> and ptB is C<B0, A1> and C is declared as C<+T, +U>,
        // then "comparable types" says
        //     (A0 ::> B0 and A1 ::> B1)  or  (B0 ::> A0 and B1 ::> A1)
        // but we will use only
        //     (A0 ::> B0 or B0 ::> A0)  and  (A1 ::> B1 or B1 ::> A1)
        Contract.Assert(normalizedA.Decl.TypeArgs.Count == normalizedA.Arguments.Count);
        Contract.Assert(normalizedA.Arguments.Count == normalizedB.Arguments.Count);
        for (var i = 0; i < normalizedA.Decl.TypeArgs.Count; i++) {
          var aa = normalizedA.Arguments[i];
          var bb = normalizedB.Arguments[i];
          var msgFormat = $"{errorFormatString} (type argument {i})"; // TODO: this should be improved to use ptA/ptB
          if (normalizedA.Decl.TypeArgs[i].Variance == TypeParameter.TPVariance.Non) {
            Constraints.AddEqualityConstraint(aa, bb, tok, msgFormat, null, reportErrors);
          } else {
            Constraints.AddGuardedConstraint(() => ApproximateComparableConstraints(aa, bb, tok, false, msgFormat, reportErrors));
          }
        }

        return true;
      }

      // not enough information to determine
      return false;
    }

    /// <summary>
    /// For every declaration in "declarations", resolve names and determine pre-types.
    /// </summary>
    public static void ResolveDeclarations(List<TopLevelDecl> declarations, ModuleResolver resolver, bool firstPhaseOnly = false) {
      // Each (top-level or member) declaration is done in two phases.
      //
      // The goal of the first phase is to fill in the pre-types in the declaration's signature (and, if the declaration is a
      // type with a base type or with parent traits, inherit the members from the base and parent types). For many declarations,
      // this is as easy as calling PreType2Type on each type that appears in the declaration's signature.
      // Since the base type of a newtype or subset type and the type of a const may be omitted in the program text,
      // obtaining the pre-type for these 3 declarations requires doing resolution. It is not clear a-priori which
      // order to process the (first phase of the) declarations in, so that the necessary pre-type information is
      // available when the first phase of a declaration needs it. Therefore, the order is determined lazily.
      //
      // In more detail, for this first phase, the declarations are processed in the given order. When such processing
      // is started for a declaration, the declaration is pushed onto a stack, and when the processing of the first
      // phase is completed, the declaration is popped off the stack and added to a set of first-phase-finished
      // declarations. If the processing requires pre-type information for a declaration whose processing has not
      // yet started, processing continues recursively with it. If the processing for the other declaration is ongoing,
      // then a cyclic-dependency error is reported.
      //
      // When the first-phase processing is finished for all the declarations, the second-phase processing is done
      // for each declaration, in the order given.

      var allDeclarations = AllTopLevelOrMemberDeclarations(declarations).ToList();
      var preTypeInferenceModuleState = new PreTypeInferenceModuleState(allDeclarations, resolver.SystemModuleManager.PreTypeBuiltins);
      foreach (var d in allDeclarations) {
        Contract.Assert(resolver.VisibleInScope(d));
        ResolvePreTypeSignature(d, preTypeInferenceModuleState, resolver);
      }

      if (!firstPhaseOnly) {
        var basicPreTypeResolver = new PreTypeResolver(resolver, preTypeInferenceModuleState);
        foreach (var d in allDeclarations) {
          basicPreTypeResolver.ResolveDeclarationBody(d);
        }
        basicPreTypeResolver.Constraints.AssertThatStateIsClear();
      }
    }

    void ResolvePreTypeSignature(Declaration d) {
      ResolvePreTypeSignature(d, preTypeInferenceModuleState, resolver);
    }

    /// <summary>
    /// This method resolves the pre-types the signature of declaration "d".
    /// If the declaration is a newtype (and thus has a base type) or extends some traits, then the members from the base type
    /// and parent types are inherited.
    /// </summary>
    private static void ResolvePreTypeSignature(Declaration d, PreTypeInferenceModuleState preTypeInferenceModuleState, ModuleResolver resolver) {
      var preTypeResolver = new PreTypeResolver(resolver, preTypeInferenceModuleState);
      var previousErrorCount = preTypeResolver.ErrorCount;

      // The "allTypeParameters" scope is stored in "resolver", and there's only one such "resolver". Since
      // "ResolvePreTypeSignature" is recursive, a simple "PushMarker()" would still leave previous type parameters
      // in the scope. Instead, we create a whole new "Scope<TypeParameter>" here. (This makes the "PushMarker()"
      // and "PopMarker()" unnecessary, but they're included here for good style.)
      var oldAllTypeParameters = resolver.allTypeParameters;
      resolver.allTypeParameters = new Scope<TypeParameter>(resolver.Options);
      resolver.allTypeParameters.PushMarker();

      if (d is TopLevelDecl topLevelDecl) {
        preTypeResolver.ResolveTypeParameters(topLevelDecl.TypeArgs, false, topLevelDecl);
      } else {
        var memberDecl = (MemberDecl)d;
        preTypeResolver.ResolveTypeParameters(memberDecl.EnclosingClass.TypeArgs, false, memberDecl.EnclosingClass);
        if (memberDecl is Method method) {
          preTypeResolver.ResolveTypeParameters(method.TypeArgs, false, method);
        } else if (memberDecl is Function function) {
          preTypeResolver.ResolveTypeParameters(function.TypeArgs, false, function);
        }
      }

      preTypeResolver.ResolveDeclarationSignature(d);
      preTypeResolver.Constraints.AssertThatStateIsClear();

      resolver.allTypeParameters.PopMarker();
      resolver.allTypeParameters = oldAllTypeParameters;

      if (d is TopLevelDeclWithMembers topLevelDeclWithMembers) {
        DPreType basePreType = null;
        if (preTypeResolver.ErrorCount == previousErrorCount && topLevelDeclWithMembers is NewtypeDecl newtypeDecl) {
          basePreType = newtypeDecl.BasePreType.Normalize() as DPreType;
        }
        resolver.RegisterInheritedMembers(topLevelDeclWithMembers, basePreType);
      }
    }

    static IEnumerable<Declaration> AllTopLevelOrMemberDeclarations(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        yield return d;
        /*
        if (d is ClassLikeDecl { NonNullTypeDecl: { } nonNullTypeDecl }) {
          yield return nonNullTypeDecl;
        }
        */
        if (d is TopLevelDeclWithMembers cl) {
          foreach (var member in cl.Members) {
            yield return member;
          }
        }
      }
    }

    /// <summary>
    /// Assumes that the type parameters in scope for "d" have been pushed.
    /// </summary>
    public void ResolveDeclarationSignature(Declaration d) {
      Contract.Requires(d is TopLevelDecl or MemberDecl);

      if (!preTypeInferenceModuleState.StillNeedsPreTypeSignature.Contains(d)) {
        // already processed
        return;
      }

      if (preTypeInferenceModuleState.InFirstPhase.Contains(d)) {
        var cycle = Util.Comma(" -> ", preTypeInferenceModuleState.InFirstPhase, d => d.ToString());
        ReportError(d, $"Cyclic dependency among declarations: {d} -> {cycle}");
      } else {
        preTypeInferenceModuleState.InFirstPhase.Push(d);
        FillInPreTypesInSignature(d);
        preTypeInferenceModuleState.InFirstPhase.Pop();
      }

      preTypeInferenceModuleState.StillNeedsPreTypeSignature.Remove(d);
    }

    /// <summary>
    /// Assumes the type parameters in scope for "declaration" have been pushed.
    /// </summary>
    public void FillInPreTypesInSignature(Declaration declaration) {
      PreType CreateTemporaryPreTypeProxy() {
        return CreatePreTypeProxy("temporary proxy until after cyclicity tests have completed");
      }

      void ComputePreTypeField(Field field) {
        Contract.Assume(field.PreType == null); // precondition
        field.PreType = CreateTemporaryPreTypeProxy();
        field.PreType = Type2PreType(field.Type);
        if (field is ConstantField cfield) {
          var parent = (TopLevelDeclWithMembers)cfield.EnclosingClass;
          Contract.Assert(currentClass == null);
          currentClass = parent;

          ResolveConstRHS(cfield, true);

          Contract.Assert(currentClass == parent);
          currentClass = null;
        }
      }

      void ComputePreTypeFormal(Formal formal) {
        Contract.Assume(formal.PreType == null); // precondition
        formal.PreType = CreateTemporaryPreTypeProxy();
        formal.PreType = Type2PreType(formal.Type);
      }

      void ComputePreTypeFunction(Function function) {
        function.Ins.ForEach(ComputePreTypeFormal);
        if (function.Result != null) {
          ComputePreTypeFormal(function.Result);
        } else if (function.ByMethodDecl != null) {
          // The by-method out-parameter is not the same as the one given in the function declaration, since the
          // function declaration didn't give one.
          function.ByMethodDecl.Outs.ForEach(ComputePreTypeFormal);
        }
        function.ResultPreType = CreateTemporaryPreTypeProxy();
        function.ResultPreType = Type2PreType(function.ResultType);
      }

      void ComputePreTypeMethod(Method method) {
        method.Ins.ForEach(ComputePreTypeFormal);
        method.Outs.ForEach(ComputePreTypeFormal);
      }

      if (declaration is SubsetTypeDecl std) {
        std.Var.PreType = CreateTemporaryPreTypeProxy();
        std.Var.PreType = Type2PreType(std.Var.Type);
        ResolveConstraintAndWitness(std, true);
      } else if (declaration is NewtypeDecl nd) {
        nd.BasePreType = CreateTemporaryPreTypeProxy();
        if (nd.Var != null) {
          nd.Var.PreType = nd.BasePreType;
        }
        nd.BasePreType = Type2PreType(nd.BaseType);
        if (nd.Var != null) {
          Contract.Assert(object.ReferenceEquals(nd.BaseType, nd.Var.Type));
          nd.Var.PreType = nd.BasePreType;
        }
        var onProxyAction = () => {
          resolver.ReportError(ResolutionErrors.ErrorId.r_newtype_base_undetermined, nd.tok,
            $"base type of {nd.WhatKindAndName} is not fully determined; add an explicit type for bound variable '{nd.Var.Name}'");
        };
        if (resolver.Options.Get(CommonOptionBag.GeneralNewtypes)) {
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IsNewtypeBaseTypeGeneral, nd.BasePreType, nd.tok,
            $"a newtype ('{nd.Name}') must be based on some non-reference, non-trait, non-arrow, non-ORDINAL, non-datatype type (got {{0}})",
            onProxyAction);
        } else {
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IsNewtypeBaseTypeLegacy, nd.BasePreType, nd.tok,
            $"a newtype ('{nd.Name}') must be based on some numeric type (got {{0}})", onProxyAction);
        }
        ResolveConstraintAndWitness(nd, true);

      } else if (declaration is IteratorDecl iter) {
        // Note, iter.Ins are reused with the parameters of the iterator's automatically generated _ctor, and
        // the iter.OutsFields are shared with the automatically generated fields of the iterator class. To avoid
        // computing their pre-types twice, we omit their pre-type computations here and instead do them in
        // the _ctor Method and for each Field of the iterator class.
        iter.Outs.ForEach(ComputePreTypeFormal);
      } else if (declaration is DatatypeDecl dtd) {
        foreach (var ctor in dtd.Ctors) {
          ctor.Formals.ForEach(ComputePreTypeFormal);
          ComputePreTypeField(ctor.QueryField);
          foreach (var dtor in ctor.Destructors) {
            // The following "if" condition makes sure ComputePreTypeField is called just once (since a destructor
            // can be shared among several constructors).
            if (dtor.EnclosingCtors[0] == ctor) {
              ComputePreTypeField(dtor);
            }
          }
        }
      } else if (declaration is TopLevelDeclWithMembers or ValuetypeDecl or TypeSynonymDecl or ModuleDecl) {
        // nothing to do
      } else if (declaration is Field field) {
        ComputePreTypeField(field);
      } else if (declaration is Function function) {
        if (function.ResultType is SelfType) {
          // This is a special case that, with the legacy type inference, handled the .Rotate{Left, Right} method of
          // bitvector types. That's now handled in a different way, which does not use SelfType.
        } else {
          ComputePreTypeFunction(function);
          if (function is ExtremePredicate { PrefixPredicate: { } prefixPredicate }) {
            ComputePreTypeFunction(prefixPredicate);
          }
        }
      } else if (declaration is Method method) {
        ComputePreTypeMethod(method);
        if (method is ExtremeLemma { PrefixLemma: { } prefixLemma }) {
          ComputePreTypeMethod(prefixLemma);
        }
      } else {
        Contract.Assert(false); // unexpected declaration
      }
    }

    public void ResolveDeclarationBody(Declaration d) {
      Contract.Requires(d is TopLevelDecl or MemberDecl);

      resolver.allTypeParameters.PushMarker();

      if (d is TopLevelDecl topLevelDecl) {
        ResolveTypeParameters(topLevelDecl.TypeArgs, false, topLevelDecl);
        ResolveTopLevelDeclaration(topLevelDecl);
      } else {
        var member = (MemberDecl)d;
        var parent = (TopLevelDeclWithMembers)member.EnclosingClass;
        ResolveTypeParameters(parent.TypeArgs, false, parent);
        Contract.Assert(currentClass == null);
        currentClass = parent;
        ResolveMember(member);
        Contract.Assert(currentClass == parent);
        currentClass = null;
      }

      resolver.allTypeParameters.PopMarker();
    }

    /// <summary>
    /// Resolve declaration "d".
    ///
    /// This method assumes type parameters have been pushed.
    /// </summary>
    private void ResolveTopLevelDeclaration(TopLevelDecl d) {
      if (d is not IteratorDecl) {
        // Note, attributes of iterators are resolved by ResolveIterator, after registering any names in the iterator signature
        scope.PushMarker();
        Contract.Assert(currentClass == null);
        scope.AllowInstance = false;
        ResolveAttributes(d, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false), true);
        scope.PopMarker();
      }

      if (d is NewtypeDecl newtypeDecl) {
        ResolveConstraintAndWitness(newtypeDecl, false);
      } else if (d is SubsetTypeDecl subsetTypeDecl) {
        ResolveConstraintAndWitness(subsetTypeDecl, false);
      } else if (d is IteratorDecl iter) {
        // Note, attributes of iterators are resolved by ResolveIterator, after registering any names in the iterator signature.
        // The following method generates the iterator's members, which in turn are resolved below.
        ResolveIterator(iter);
      } else if (d is DatatypeDecl dt) {
        // resolve any default parameters
        foreach (var ctor in dt.Ctors) {
          scope.PushMarker();
          scope.AllowInstance = false;
          ctor.Formals.ForEach(p => ScopePushAndReport(p, "destructor", false));
          ResolveAttributes(ctor, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false), true);
          ResolveParameterDefaultValues(ctor.Formals, dt);
          scope.PopMarker();
        }
      }
    }

    void ResolveTypeParameters(List<TypeParameter> tparams, bool emitErrors, TypeParameter.ParentType parent) {
      Contract.Requires(tparams != null);
      Contract.Requires(parent != null);
      // push non-duplicated type parameter names
      int index = 0;
      foreach (TypeParameter tp in tparams) {
        if (emitErrors) {
          // we're seeing this TypeParameter for the first time
          tp.Parent = parent;
          tp.PositionalIndex = index;
        }
        var r = resolver.allTypeParameters.Push(tp.Name, tp);
        if (emitErrors) {
          if (r == Scope<TypeParameter>.PushResult.Duplicate) {
            ReportError(tp, "Duplicate type-parameter name: {0}", tp.Name);
          } else if (r == Scope<TypeParameter>.PushResult.Shadow) {
            ReportWarning(tp.tok, "Shadowed type-parameter name: {0}", tp.Name);
          }
        }
      }
    }

    public void ResolveAttributes(IAttributeBearingDeclaration attributeHost, ResolutionContext opts, bool solveConstraints) {
      Contract.Requires(attributeHost != null);
      Contract.Requires(opts != null);

      // order does not matter much for resolution, so resolve them in reverse order
      foreach (var attr in attributeHost.Attributes.AsEnumerable()) {
        if (attributeHost != null && attr is UserSuppliedAttributes usa) {
#if TODO          
          usa.Recognized = resolver.IsRecognizedAttribute(usa, attributeHost); // TODO: this could be done in a later resolution pass
#endif
        }
        if (attr.Args != null) {
          foreach (var arg in attr.Args) {
            if (Attributes.Contains(attributeHost.Attributes, "opaque_reveal") && attr.Name is "revealedFunction" && arg is NameSegment nameSegment) {
              ResolveNameSegment(nameSegment, true, null, opts, false, specialOpaqueHackAllowance: true);
            } else {
              ResolveExpression(arg, opts);
            }
          }
          if (solveConstraints) {
            Constraints.SolveAllTypeConstraints($"attribute of {attributeHost.ToString()}");
          }
        }
      }
    }

    void ResolveConstraintAndWitness(RedirectingTypeDecl dd, bool initialResolutionPass) {
      Contract.Requires(dd != null);
      Contract.Requires(dd.Constraint != null);

      if (dd.Var == null) {
        if (initialResolutionPass) {
          Constraints.SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' constraint");
        }
      } else {
        if (initialResolutionPass == dd.Var.Type is TypeProxy) {
          scope.PushMarker();
          scope.AllowInstance = false;
          ScopePushExpectSuccess(dd.Var, dd.WhatKind + " variable", false);
          ResolveExpression(dd.Constraint, new ResolutionContext(new CodeContextWrapper(dd, true), false));
          ConstrainTypeExprBool(dd.Constraint, dd.WhatKind + " constraint must be of type bool (instead got {0})");
          scope.PopMarker();
          Constraints.SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' constraint");
        } else {
          Constraints.SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' constraint");
        }
      }

      if (!initialResolutionPass && dd.Witness != null) {
        var codeContext = new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
        scope.PushMarker();
        scope.AllowInstance = false;
        ResolveExpression(dd.Witness, new ResolutionContext(codeContext, false));
        scope.PopMarker();
        AddSubtypeConstraint(dd.Var.PreType, dd.Witness.PreType, dd.Witness.tok, "witness expression must have type '{0}' (got '{1}')");
        Constraints.SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' witness");
      }
    }

    /// <summary>
    /// Assumes the type parameters in scope for "cfield" have been pushed.
    /// Assumes that "currentClass" has been set to the parent of "cfield".
    /// </summary>
    void ResolveConstRHS(ConstantField cfield, bool initialResolutionPass) {
      if (cfield.Rhs != null && initialResolutionPass == cfield.Type is TypeProxy) {
        var opts = new ResolutionContext(cfield, false);
        scope.PushMarker();
        if (cfield.IsStatic) {
          scope.AllowInstance = false;
        }
        ResolveExpression(cfield.Rhs, opts);
        scope.PopMarker();
        AddSubtypeConstraint(cfield.PreType, cfield.Rhs.PreType, cfield.Tok, "RHS (of type {1}) not assignable to LHS (of type {0})");
        Constraints.SolveAllTypeConstraints($"{cfield.WhatKind} '{cfield.Name}' constraint");
      }
    }

    void ResolveParameterDefaultValues(List<Formal> formals, ICodeContext codeContext) {
      Contract.Requires(formals != null);
      Contract.Requires(codeContext != null);

      var dependencies = new Graph<IVariable>();
      var allowMoreRequiredParameters = true;
      var allowNamelessParameters = true;
      foreach (var formal in formals) {
        var d = formal.DefaultValue;
        if (d != null) {
          allowMoreRequiredParameters = false;
          ResolveExpression(d, new ResolutionContext(codeContext, codeContext is TwoStateFunction || codeContext is TwoStateLemma));
          AddSubtypeConstraint(Type2PreType(formal.Type), d.PreType, d.tok, "default-value expression (of type '{1}') is not assignable to formal (of type '{0}')");
          foreach (var v in ModuleResolver.FreeVariables(d)) {
            dependencies.AddEdge(formal, v);
          }
        } else if (!allowMoreRequiredParameters) {
          ReportError(formal.tok, "a required parameter must precede all optional parameters");
        }
        if (!allowNamelessParameters && !formal.HasName) {
          ReportError(formal.tok, "a nameless parameter must precede all nameonly parameters");
        }
        if (formal.IsNameOnly) {
          allowNamelessParameters = false;
        }
      }
      Constraints.SolveAllTypeConstraints($"parameter default values of {codeContext.FullSanitizedName}");

      foreach (var cycle in dependencies.AllCycles()) {
        var cy = Util.Comma(" -> ", cycle, v => v.Name) + " -> " + cycle[0].Name;
        ReportError(cycle[0].Tok, $"default-value expressions for parameters contain a cycle: {cy}");
      }
    }

    /// <summary>
    /// Resolve declaration "member", assuming that the member's pre-type signature has already been resolved.
    ///
    /// Type constraints are solved here.
    ///
    /// This method assumes type parameters of the enclosing type have been pushed.
    /// Also assumes that "currentClass" has been set to the parent of "member".
    /// </summary>
    void ResolveMember(MemberDecl member) {
      Contract.Requires(member != null);
      Contract.Requires(currentClass != null);

      if (member is ConstantField cfield) {
        scope.PushMarker();
        if (cfield.IsStatic) {
          scope.AllowInstance = false;
        }
        ResolveAttributes(member, new ResolutionContext(new NoContext(currentClass.EnclosingModuleDefinition), false), true);
        scope.PopMarker();
        ResolveConstRHS(cfield, false);

      } else if (member is Field) {
        ResolveAttributes(member, new ResolutionContext(new NoContext(currentClass.EnclosingModuleDefinition), false), true);

      } else if (member is Function f) {
        var ec = ErrorCount;
        resolver.allTypeParameters.PushMarker();
        ResolveTypeParameters(f.TypeArgs, false, f);
        ResolveFunction(f);
        resolver.allTypeParameters.PopMarker();

        if (f is ExtremePredicate extremePredicate && extremePredicate.PrefixPredicate != null && ec == ErrorCount) {
          var ff = extremePredicate.PrefixPredicate;
          resolver.allTypeParameters.PushMarker();
          ResolveTypeParameters(ff.TypeArgs, false, ff);
          ResolveFunction(ff);
          resolver.allTypeParameters.PopMarker();
        }

      } else if (member is Method m) {
        var ec = ErrorCount;
        resolver.allTypeParameters.PushMarker();
        ResolveTypeParameters(m.TypeArgs, false, m);
        ResolveMethod(m);
        resolver.allTypeParameters.PopMarker();

        if (m is ExtremeLemma em && em.PrefixLemma != null && ec == ErrorCount) {
          var mm = em.PrefixLemma;
          resolver.allTypeParameters.PushMarker();
          ResolveTypeParameters(mm.TypeArgs, false, mm);
          ResolveMethod(mm);
          resolver.allTypeParameters.PopMarker();
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Requires(currentClass != null);
      Contract.Ensures(currentClass == null);

      var initialErrorCount = ErrorCount;

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      scope.PushMarker();
      scope.AllowInstance = false;  // disallow 'this' from use, which means that the special fields and methods added are not accessible in the syntactically given spec
      iter.Ins.ForEach(p => ScopePushAndReport(p, "in-parameter", false));
      ResolveParameterDefaultValues(iter.Ins, iter);

      // In-parameters (but not "this" and yield parameters) are in scope for the iterator's attributes.
      ResolveAttributes(iter, new ResolutionContext(iter, false), true);

      // Start resolving specification...
      // we start with the decreases clause, because the _decreases<n> fields were only given type proxies before; we'll know
      // the types only after resolving the decreases clause (and it may be that some of resolution has already seen uses of
      // these fields; so, with no further ado, here we go
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      ResolveAttributes(iter.Decreases, new ResolutionContext(iter, false), false);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        ResolveExpression(e, new ResolutionContext(iter, false));
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        // If the following type constraint does not hold, then: Bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
        AddSubtypeConstraint(d.PreType, e.PreType, e.tok, "type of field '" + d.Name + "' is {1}, but has been constrained elsewhere to be of type {0}");
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpression(fe, FrameExpressionUse.Reads, iter);
      }
      ResolveAttributes(iter.Modifies, new ResolutionContext(iter, false), false);
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpression(fe, FrameExpressionUse.Modifies, iter);
      }
      foreach (AttributedExpression e in iter.Requires) {
        ResolveAttributes(e, new ResolutionContext(iter, false), false);
        ResolveExpression(e.E, new ResolutionContext(iter, false));
        ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
      }

      scope.PopMarker();  // for the in-parameters

      // We resolve the rest of the specification in an instance context.  So mentions of the in- or yield-parameters
      // get resolved as field dereferences (with an implicit "this")
      scope.PushMarker();
      currentClass = iter;
      Contract.Assert(scope.AllowInstance);

      foreach (AttributedExpression e in iter.YieldRequires) {
        ResolveAttributes(e, new ResolutionContext(iter, false), false);
        ResolveExpression(e.E, new ResolutionContext(iter, false));
        ConstrainTypeExprBool(e.E, "Yield precondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.YieldEnsures) {
        ResolveAttributes(e, new ResolutionContext(iter, true), false);
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        ConstrainTypeExprBool(e.E, "Yield postcondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.Ensures) {
        ResolveAttributes(e, new ResolutionContext(iter, true), false);
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
      }
      Constraints.SolveAllTypeConstraints($"specification of iterator '{iter.Name}'");

      var postSpecErrorCount = ErrorCount;

      // Resolve body
      if (iter.Body != null) {
        dominatingStatementLabels.PushMarker();
        foreach (var req in iter.Requires) {
          if (req.Label != null) {
            if (dominatingStatementLabels.Find(req.Label.Name) != null) {
              ReportError(req.Label.Tok, "assert label shadows a dominating label");
            } else {
              var rr = dominatingStatementLabels.Push(req.Label.Name, req.Label);
              Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
            }
          }
        }
        ResolveBlockStatement(iter.Body, ResolutionContext.FromCodeContext(iter));
        dominatingStatementLabels.PopMarker();
        Constraints.SolveAllTypeConstraints($"body of iterator '{iter.Name}'");
      }

      currentClass = null;
      scope.PopMarker();  // pop off the AllowInstance setting

      if (postSpecErrorCount == initialErrorCount) {
        iter.CreateIteratorMethodSpecs(resolver);
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed.
    /// Also assumes that "currentClass" has been set to the parent of "f".
    /// </summary>
    void ResolveFunction(Function f) {
      Contract.Requires(f != null);

      f.ResolveNewOrOldPart(this);

      // make note of the warnShadowing attribute
      bool warnShadowingOption = resolver.Options.WarnShadowing;  // save the original warnShadowing value
      bool warnShadowing = true;
      // take care of the warnShadowing attribute
      if (Attributes.ContainsBool(f.Attributes, "warnShadowing", ref warnShadowing)) {
        resolver.Options.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }

      scope.PushMarker();
      if (f.IsStatic) {
        scope.AllowInstance = false;
      }

      foreach (Formal p in f.Ins) {
        ScopePushAndReport(p, "parameter", false);
      }
      ResolveParameterDefaultValues(f.Ins, f);

      foreach (var req in f.Req) {
        ResolveAttributes(req, new ResolutionContext(f, f is TwoStateFunction), false);
        Expression r = req.E;
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction));
        ConstrainTypeExprBool(r, "Precondition must be a boolean (got {0})");
      }

      ResolveAttributes(f.Reads, new ResolutionContext(f, f is TwoStateFunction), false);
      foreach (FrameExpression fr in f.Reads.Expressions) {
        ResolveFrameExpression(fr, FrameExpressionUse.Reads, f);
      }

      scope.PushMarker();
      if (f.Result != null) {
        ScopePushAndReport(f.Result, "function result", false); // function return only visible in post-conditions
      }
      foreach (var ens in f.Ens) {
        ResolveAttributes(ens, new ResolutionContext(f, f is TwoStateFunction), false);
        Expression r = ens.E;
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction) with { InFunctionPostcondition = true });
        ConstrainTypeExprBool(r, "Postcondition must be a boolean (got {0})");
      }
      // resolve attributes on the function itself, now that in-parameters and any result name are part of the scope
      ResolveAttributes(f, new ResolutionContext(f, f is TwoStateFunction), true);
      scope.PopMarker(); // function result name

      ResolveAttributes(f.Decreases, new ResolutionContext(f, f is TwoStateFunction), false);
      foreach (Expression r in f.Decreases.Expressions) {
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction));
        // any type is fine
      }

      Constraints.SolveAllTypeConstraints($"specification of {f.WhatKind} '{f.Name}'");

      if (f.ByMethodBody != null) {
        // The following conditions are assured by the parser and other callers of the Function constructor
        Contract.Assert(f.Body != null);
        Contract.Assert(!f.IsGhost);
      }
      if (f.Body != null) {
        var prevErrorCount = ErrorCount;
        ResolveExpression(f.Body, new ResolutionContext(f, f is TwoStateFunction));
        AddSubtypeConstraint(Type2PreType(f.ResultType), f.Body.PreType, f.tok, "Function body type mismatch (expected {0}, got {1})");
        Constraints.SolveAllTypeConstraints($"body of {f.WhatKind} '{f.Name}'");
      }

      scope.PopMarker();

      if (f.ByMethodBody != null) {
        var method = f.ByMethodDecl;
        Contract.Assert(method != null); // this should have been filled in by now
        ResolveMethod(method);
      }

      resolver.Options.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
    }

    /// <summary>
    /// Assumes type parameters have already been pushed.
    /// Also assumes that "currentClass" has been set to the parent of "m".
    /// </summary>
    void ResolveMethod(Method m) {
      Contract.Requires(m != null);

      m.ResolveNewOrOldPart(this);

      try {
        currentMethod = m;

        bool warnShadowingOption = resolver.Options.WarnShadowing;  // save the original warnShadowing value
        bool warnShadowing = true;
        // take care of the warnShadowing attribute
        if (Attributes.ContainsBool(m.Attributes, "warnShadowing", ref warnShadowing)) {
          resolver.Options.WarnShadowing = warnShadowing;  // set the value according to the attribute
        }

        // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
        scope.PushMarker();
        if (m.IsStatic || m is Constructor) {
          scope.AllowInstance = false;
        }
        foreach (Formal p in m.Ins) {
          ScopePushAndReport(p, "in-parameter", false);
        }
        ResolveParameterDefaultValues(m.Ins, m);

        // Start resolving specification...
        foreach (AttributedExpression e in m.Req) {
          ResolveAttributes(e, new ResolutionContext(m, m is TwoStateLemma), false);
          ResolveExpression(e.E, new ResolutionContext(m, m is TwoStateLemma));
          ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
        }

        ResolveAttributes(m.Reads, new ResolutionContext(m, false), false);
        foreach (FrameExpression fe in m.Reads.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Reads, m);
        }

        ResolveAttributes(m.Mod, new ResolutionContext(m, false), false);
        foreach (FrameExpression fe in m.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, m);
        }

        ResolveAttributes(m.Decreases, new ResolutionContext(m, false), false);
        foreach (Expression e in m.Decreases.Expressions) {
          ResolveExpression(e, new ResolutionContext(m, m is TwoStateLemma));
          // any type is fine
        }

        if (m is Constructor) {
          scope.PopMarker();
          // start the scope again, but this time allowing instance
          scope.PushMarker();
          foreach (Formal p in m.Ins) {
            ScopePushAndReport(p, "in-parameter", false);
          }
        }

        // Add out-parameters to a new scope that will also include the outermost-level locals of the body
        // Don't care about any duplication errors among the out-parameters, since they have already been reported
        scope.PushMarker();
        if (m is ExtremeLemma && m.Outs.Count != 0) {
          ReportError(m.Outs[0].tok, "{0}s are not allowed to have out-parameters", m.WhatKind);
        } else {
          foreach (Formal p in m.Outs) {
            ScopePushAndReport(p, "out-parameter", false);
          }
        }

        // ... continue resolving specification
        foreach (AttributedExpression e in m.Ens) {
          ResolveAttributes(e, new ResolutionContext(m, true), false);
          ResolveExpression(e.E, new ResolutionContext(m, true));
          ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
        }
        Constraints.SolveAllTypeConstraints($"specification of {m.WhatKind} '{m.Name}'");

        // Resolve body
        if (m.Body != null) {
          if (m is ExtremeLemma { PrefixLemma: { } } com) {
            // The body may mentioned the implicitly declared parameter _k.  Throw it into the
            // scope before resolving the body.
            var k = com.PrefixLemma.Ins[0];
            ScopePushExpectSuccess(k, "_k parameter", false);
          }

          dominatingStatementLabels.PushMarker();
          foreach (var req in m.Req) {
            if (req.Label != null) {
              if (dominatingStatementLabels.Find(req.Label.Name) != null) {
                ReportError(req.Label.Tok, "assert label shadows a dominating label");
              } else {
                var rr = dominatingStatementLabels.Push(req.Label.Name, req.Label);
                Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
              }
            }
          }
          ResolveBlockStatement(m.Body, ResolutionContext.FromCodeContext(m));
          dominatingStatementLabels.PopMarker();
          Constraints.SolveAllTypeConstraints($"body of {m.WhatKind} '{m.Name}'");
        }

        // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for greatest lemmas)
        ResolveAttributes(m, new ResolutionContext(m, m is TwoStateLemma), true);

        resolver.Options.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
        scope.PopMarker();  // for the out-parameters and outermost-level locals
        scope.PopMarker();  // for the in-parameters
      }
      finally {
        currentMethod = null;
      }
    }

    void ResolveFrameExpression(FrameExpression fe, FrameExpressionUse use, ICodeContext codeContext) {
      Contract.Requires(fe != null);
      Contract.Requires(codeContext != null);
      var resolutionContext = new ResolutionContext(codeContext, codeContext is TwoStateLemma || use == FrameExpressionUse.Unchanged);
      ResolveExpression(fe.E, resolutionContext);
      Constraints.AddGuardedConstraint(() => {
        DPreType dp = fe.E.PreType.NormalizeWrtScope() as DPreType;
        if (dp == null) {
          // no information yet
          return false;
        }
        // A FrameExpression is allowed to have one of the following types:
        //     C
        //     collection<C>
        // where C is a reference type and collection is set, iset, seq, or multiset.
        // In a reads clause, a FrameExpression is additionally allowed to have type
        //     ... ~> collection<C>
        // A FrameExpression can also specify a field name using the syntax FE`fieldName,
        // which is allowed if fieldName is a field of C.
        var hasArrowType = false;
        var hasCollectionType = false;
        if (use == FrameExpressionUse.Reads && DPreType.IsArrowType(dp.Decl)) {
          hasArrowType = true;
          dp = dp.Arguments.Last().Normalize() as DPreType;
          if (dp == null) {
            // function's image type not yet known
            return false;
          }
        }

        if (dp.UrAncestor(this) is DPreType {
          Decl.Name: PreType.TypeNameSet or PreType.TypeNameIset or PreType.TypeNameSeq or PreType.TypeNameMultiset
        } dpAncestor) {
          hasCollectionType = true;
          var elementType = dpAncestor.Arguments[0].Normalize();
          dp = elementType as DPreType;
          if (dp == null) {
            // element type not yet known
            Constraints.AddDefaultAdvice(elementType, CommonAdvice.Target.Object);
            return false;
          }
        }

        if (!DPreType.IsReferenceTypeDecl(dp.Decl) || (hasArrowType && !hasCollectionType)) {
          var expressionMustDenoteObject = "expression must denote an object";
          var collection = "a set/iset/multiset/seq of objects";
          var instead = "(instead got {0})";
          var errorMsgFormat = use switch {
            FrameExpressionUse.Reads =>
              $"a reads-clause {expressionMustDenoteObject}, {collection}, or a function to {collection} {instead}",
            FrameExpressionUse.Modifies =>
              $"a modifies-clause {expressionMustDenoteObject} or {collection} {instead}",
            FrameExpressionUse.Unchanged =>
              $"an unchanged {expressionMustDenoteObject} or {collection} {instead}",
            _ => throw new ArgumentOutOfRangeException(nameof(use), use, null)
          };
          ReportError(fe.E.tok, errorMsgFormat, fe.E.PreType);
        }

        if (fe.FieldName != null) {
          var (member, tentativeReceiverType) = FindMember(fe.E.tok, dp, fe.FieldName, resolutionContext);
          Contract.Assert((member == null) == (tentativeReceiverType == null)); // follows from contract of FindMember
          if (member == null) {
            // error has already been reported by FindMember
          } else if (!(member is Field)) {
            ReportError(fe.E, "member {0} in type {1} does not refer to a field", fe.FieldName, tentativeReceiverType.Decl.Name);
          } else if (member is ConstantField) {
            ReportError(fe.E, "expression is not allowed to refer to constant field {0}", fe.FieldName);
          } else {
            fe.Field = (Field)member;
          }
        }

        return true;
      });
    }

    // ---------------------------------------- Utilities ----------------------------------------

    public Dictionary<TypeParameter, PreType> BuildPreTypeArgumentSubstitute(Dictionary<TypeParameter, PreType> typeArgumentSubstitutions, DPreType/*?*/ receiverTypeBound = null) {
      Contract.Requires(typeArgumentSubstitutions != null);

      var subst = new Dictionary<TypeParameter, PreType>();
      foreach (var entry in typeArgumentSubstitutions) {
        subst.Add(entry.Key, entry.Value);
      }

      if (receiverTypeBound?.Decl is TopLevelDeclWithMembers cl) {
        foreach (var entry in cl.ParentFormalTypeParametersToActuals) {
          var v = Type2PreType(entry.Value).Substitute(subst);
          subst.Add(entry.Key, v);
        }
      }

      return subst;
    }

    // ---------------------------------------- Migration sanity checks ----------------------------------------

    public void SanityCheckOldAndNewInference(List<TopLevelDecl> declarations) {
      var visitor = new PreTypeSanityChecker(this);
      foreach (var decl in declarations) {
        foreach (var attr in decl.Attributes.AsEnumerable()) {
          visitor.Visit(attr.Args);
        }
        if (decl is RedirectingTypeDecl rtd) {
          if (rtd.Constraint != null) {
            visitor.Visit(rtd.Constraint);
          }
          if (rtd.Witness != null) {
            visitor.Visit(rtd.Witness);
          }
        } else if (decl is IteratorDecl iter) {
          visitor.Visit(iter);
        } else if (decl is TopLevelDeclWithMembers md) {
          foreach (var member in md.Members) {
            if (member is ConstantField cfield && cfield.Rhs != null) {
              visitor.Visit(cfield.Rhs);
            } else if (member is Function f) {
              visitor.Visit(f);
              if (f is ExtremePredicate extremePredicate) {
                visitor.Visit(extremePredicate.PrefixPredicate);
              }
            } else if (member is Method m) {
              visitor.Visit(m);
              if (m is ExtremeLemma extremeLemma) {
                visitor.Visit(extremeLemma.PrefixLemma);
              }
            }
          }
        }
      }
    }

    class PreTypeSanityChecker : BottomUpVisitor {
      private PreTypeResolver preTypeResolver;

      public PreTypeSanityChecker(PreTypeResolver preTypeResolver) {
        this.preTypeResolver = preTypeResolver;
      }

      protected override void VisitOneExpr(Expression expr) {
        // compare expr.PreType and expr.Type
        if (expr.PreType == null) {
          preTypeResolver.ReportWarning(expr.tok, $"sanity check WARNING: no pre-type was computed");
        } else if (expr.Type == null) {
          preTypeResolver.ReportError(expr.tok, $"SANITY CHECK FAILED: .PreType is '{expr.PreType}' but .Type is null");
        } else if (PreType.Same(expr.PreType, preTypeResolver.Type2PreType(expr.Type))) {
          // all is cool
        } else if (expr.PreType is UnusedPreType && expr.Type is TypeProxy) {
          // this is expected
        } else {
          preTypeResolver.ReportError(expr.tok, $"SANITY CHECK FAILED: pre-type '{expr.PreType}' does not correspond to type '{expr.Type}'");
        }
      }
    }
  }
}
