//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny {
  public abstract class ResolverPass {
    protected readonly Resolver resolver;

    protected ResolverPass(Resolver resolver) {
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
      resolver.Reporter.Error(MessageSource.Resolver, tok, "PRE-TYPE: " + msg, args);
    }

    public void ReportWarning(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Warning(MessageSource.Resolver, ErrorRegistry.NoneId, tok, msg, args);
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

    TopLevelDeclWithMembers currentClass;
    Method currentMethod;

    private readonly Dictionary<string, TopLevelDecl> preTypeBuiltins = new();

    TopLevelDecl BuiltInTypeDecl(string name) {
      Contract.Requires(name != null);
      if (preTypeBuiltins.TryGetValue(name, out var decl)) {
        return decl;
      }
      if (IsArrayName(name, out var dims)) {
        // make sure the array class has been created
        var at = resolver.builtIns.ArrayType(Token.NoToken, dims,
          new List<Type> { new InferredTypeProxy() }, true);
        decl = resolver.builtIns.arrayTypeDecls[dims];
      } else if (IsBitvectorName(name, out var width)) {
        var bvDecl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, t => t.IsBitVectorType,
          typeArgs => new BitvectorType(resolver.Options, width));
        preTypeBuiltins.Add(name, bvDecl);
        AddRotateMember(bvDecl, "RotateLeft", width);
        AddRotateMember(bvDecl, "RotateRight", width);
        return bvDecl;
      } else {
        foreach (var valueTypeDecl in resolver.valuetypeDecls) {
          if (valueTypeDecl.Name == name) {
            // bool, int, real, ORDINAL, map, imap
            decl = valueTypeDecl;
            break;
          }
        }
        if (decl == null) {
          if (name == "set" || name == "seq" || name == "multiset") {
            var variances = new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Strict };
            decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, variances, _ => false, null);
          } else if (name == "iset") {
            var variances = new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Permissive };
            decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, variances, _ => false, null);
          } else {
            decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, _ => false, null);
          }
        }
      }
      preTypeBuiltins.Add(name, decl);
      return decl;
    }

    public void AddRotateMember(ValuetypeDecl enclosingType, string name, int width) {
      var argumentType = resolver.builtIns.Nat();
      var formals = new List<Formal> {
        new Formal(Token.NoToken, "w", argumentType, true, false, null, false) {
          PreType = Type2PreType(argumentType)
        }
      };
      var resultType = new BitvectorType(resolver.Options, width);
      var rotateMember = new SpecialFunction(RangeToken.NoToken, name, resolver.builtIns.SystemModule, false, false,
        new List<TypeParameter>(), formals, resultType,
        new List<AttributedExpression>(), new List<FrameExpression>(), new List<AttributedExpression>(),
        new Specification<Expression>(new List<Expression>(), null), null, null, null) {
        EnclosingClass = enclosingType,
        ResultPreType = Type2PreType(resultType)
      };
      rotateMember.AddVisibilityScope(resolver.builtIns.SystemModule.VisibilityScope, false);
      enclosingType.Members.Add(name, rotateMember);
    }

    TopLevelDecl BuiltInArrowTypeDecl(int arity) {
      Contract.Requires(0 <= arity);
      var name = $"{arity}~>";
      if (!preTypeBuiltins.TryGetValue(name, out var decl)) {
        var variances = new List<TypeParameter.TPVarianceSyntax>();
        for (var i = 0; i < arity; i++) {
          variances.Add(TypeParameter.TPVarianceSyntax.Contravariance);
        }
        variances.Add(TypeParameter.TPVarianceSyntax.Covariant_Strict);
        decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, variances, _ => false,
          typeArguments => new ArrowType(Token.NoToken,
            typeArguments.GetRange(0, typeArguments.Count - 1),
            typeArguments.Last()));
        preTypeBuiltins.Add(name, decl);
      }
      return decl;
    }

    DPreType BuiltInArrowType(List<PreType> inPreTypes, PreType resultPreType) {
      return new DPreType(BuiltInArrowTypeDecl(inPreTypes.Count), Util.Snoc(inPreTypes, resultPreType));
    }

    DPreType BuiltInArrayType(int dims, PreType elementPreType) {
      Contract.Requires(1 <= dims);
      var arrayName = dims == 1 ? "array" : $"array{dims}";
      return new DPreType(BuiltInTypeDecl(arrayName), new List<PreType>() { elementPreType });
    }

    private int typeProxyCount = 0; // used to give each PreTypeProxy a unique ID

    private readonly List<(PreTypeProxy, string)> allPreTypeProxies = new();

    public PreType CreatePreTypeProxy(string description = null) {
      var proxy = new PreTypeProxy(typeProxyCount++);
      allPreTypeProxies.Add((proxy, description));
      return proxy;
    }

    public enum Type2PreTypeOption { GoodForInference, GoodForPrinting, GoodForBoth }

    public PreType Type2PreType(Type type, string description = null, Type2PreTypeOption option = Type2PreTypeOption.GoodForBoth) {
      Contract.Requires(type != null);

      type = type.Normalize();
      if (type is TypeProxy) {
        return CreatePreTypeProxy(description ?? $"from type proxy {type}");
      }

      DPreType printablePreType = null;
      if (option != Type2PreTypeOption.GoodForInference) {
        var printableDecl = Type2PreTypeDecl(type);
        var printableArguments = type.TypeArgs.ConvertAll(ty => Type2PreType(ty, null, Type2PreTypeOption.GoodForPrinting));
        printablePreType = new DPreType(printableDecl, printableArguments, null);
        if (option == Type2PreTypeOption.GoodForPrinting) {
          return printablePreType;
        }
      }

      type = type.NormalizeExpand();
      var decl = Type2PreTypeDecl(type);
      var arguments = type.TypeArgs.ConvertAll(ty => Type2PreType(ty, null, Type2PreTypeOption.GoodForInference));
      return new DPreType(decl, arguments, printablePreType);
    }

    TopLevelDecl Type2PreTypeDecl(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(type is NonProxyType and not SelfType);
      TopLevelDecl decl;
      if (type is BoolType) {
        decl = BuiltInTypeDecl("bool");
      } else if (type is CharType) {
        decl = BuiltInTypeDecl("char");
      } else if (type is IntType) {
        decl = BuiltInTypeDecl("int");
      } else if (type is RealType) {
        decl = BuiltInTypeDecl("real");
      } else if (type is BigOrdinalType) {
        decl = BuiltInTypeDecl("ORDINAL");
      } else if (type is BitvectorType bitvectorType) {
        decl = BuiltInTypeDecl("bv" + bitvectorType.Width);
      } else if (type is CollectionType) {
        var name =
          type is SetType st ? (st.Finite ? "set" : "iset") :
          type is MultiSetType ? "multiset" :
          type is MapType mt ? (mt.Finite ? "map" : "imap") :
          "seq";
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
    /// Returns the non-newtype ancestor of "cecl".
    /// </summary>
    public static TopLevelDecl AncestorDecl(TopLevelDecl decl) {
      while (decl is NewtypeDecl newtypeDecl) {
        var parent = newtypeDecl.BasePreType.Normalize();
        decl = ((DPreType)parent).Decl;
      }
      return decl;
    }

    [CanBeNull]
    public static string/*?*/ AncestorName(PreType preType) {
      var dp = preType.Normalize() as DPreType;
      return dp == null ? null : AncestorDecl(dp.Decl).Name;
    }

    /// <summary>
    /// Returns the non-newtype ancestor of "preType".
    /// </summary>
    public DPreType NewTypeAncestor(DPreType preType) {
      Contract.Requires(preType != null);
      while (preType.Decl is NewtypeDecl newtypeDecl) {
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

    /// <summary>
    /// AllParentTraits(decl) is like decl.ParentTraits, but also returns "object" is "decl" is a reference type.
    /// </summary>
    public IEnumerable<Type> AllParentTraits(TopLevelDeclWithMembers decl) {
      foreach (var parentType in decl.ParentTraits) {
        yield return parentType;
      }
      if (DPreType.IsReferenceTypeDecl(decl)) {
        if (decl is TraitDecl trait && trait.IsObjectTrait) {
          // don't return object itself
        } else {
          yield return resolver.builtIns.ObjectQ();
        }
      }
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
    /// An ancestor
    void ComputeAncestors(TopLevelDecl d, ISet<TopLevelDecl> ancestors) {
      if (!ancestors.Contains(d)) {
        ancestors.Add(d);
        if (d is TopLevelDeclWithMembers dm) {
          dm.ParentTraitHeads.ForEach(parent => ComputeAncestors(parent, ancestors));
        }
        if (d is ClassDecl cl && cl.IsObjectTrait) {
          // we're done
        } else if (DPreType.IsReferenceTypeDecl(d)) {
          // object is also a parent type
          ComputeAncestors(resolver.builtIns.ObjectDecl, ancestors);
        }
      }
    }

    int Height(TopLevelDecl d) {
      if (d is TopLevelDeclWithMembers md && md.ParentTraitHeads.Count != 0) {
        return md.ParentTraitHeads.Max(Height) + 1;
      } else if (d is ClassDecl cl && cl.IsObjectTrait) {
        // object is at height 0
        return 0;
      } else if (DPreType.IsReferenceTypeDecl(d)) {
        // any other reference type implicitly has "object" as a parent, so the height is 1
        return 1;
      } else {
        return 0;
      }
    }

    /// <summary>
    /// Return "true" if "super" is a super-(pre)type of "sub".
    /// Otherwise, return "false".
    /// Note, if either "super" or "sub" contains a type proxy, then "false" is returned.
    /// </summary>
    public bool IsSuperPreTypeOf(DPreType super, DPreType sub) {
      var subAncestors = new HashSet<TopLevelDecl>();
      ComputeAncestors(sub.Decl, subAncestors);
      if (!subAncestors.Contains(super.Decl)) {
        return false;
      }
      var s = sub.AsParentType(super.Decl, this);
      var n = super.Decl.TypeArgs.Count;
      Contract.Assert(super.Arguments.Count == n);
      Contract.Assert(s.Arguments.Count == n);
      for (var i = 0; i < n; i++) {
        var superI = super.Arguments[i].Normalize() as DPreType;
        var subI = s.Arguments[i].Normalize() as DPreType;
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
      if (name.StartsWith("bv")) {
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
      if (name.StartsWith("array")) {
        var dims = name.Substring(5);
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

    public PreTypeResolver(Resolver resolver)
      : base(resolver) {
      Contract.Requires(resolver != null);
      scope = new Scope<IVariable>(resolver.Options);
      enclosingStatementLabels = new Scope<Statement>(resolver.Options);
      dominatingStatementLabels = new Scope<Label>(resolver.Options);
    }

    void ScopePushAndReport(IVariable v, string kind, bool assignPreType = true) {
      Contract.Requires(scope != null);
      Contract.Requires(v != null);
      Contract.Requires(kind != null);
      if (assignPreType) {
        Contract.Assert(v.PreType == null);
        v.PreType = Type2PreType(v.Type, $"type of identifier '{v.Name}'");
        Contract.Assert(v.PreType is not DPreType dp || dp.Decl != null); // sanity check that the .Decl field was set
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

#if THIS_COMES_LATER
    public void PostResolveChecks(List<TopLevelDecl> declarations) {
      Contract.Requires(declarations != null);
      foreach (TopLevelDecl topd in declarations) {
        TopLevelDecl d = topd is ClassDecl ? ((ClassDecl)topd).NonNullTypeDecl : topd;

        if (ErrorCount == prevErrorCount) {
          // Check type inference, which also discovers bounds, in newtype/subset-type constraints and const declarations
          foreach (TopLevelDecl topd in declarations) {
            TopLevelDecl d = topd is ClassDecl ? ((ClassDecl)topd).NonNullTypeDecl : topd;
            if (topd is TopLevelDeclWithMembers cl) {
              foreach (var member in cl.Members) {
                if (member is ConstantField field && field.Rhs != null) {
                  // make sure initialization only refers to constant field or literal expression
                  if (CheckIsConstantExpr(field, field.Rhs)) {
                    AddAssignableConstraint(field.tok, field.Type, field.Rhs.Type,
                      "type for constant '" + field.Name + "' is '{0}', but its initialization value type is '{1}'");
                  }
                  
                }
              }
            }
          }
        }

      }
    }
#endif
    
    /// <summary>
    /// For every declaration in "declarations", resolve names and determine pre-types.
    /// </summary>
    public void ResolveDeclarations(List<TopLevelDecl> declarations, string moduleName) {
      Contract.Requires(declarations != null);

      // Proceed in three phases, each of which does a complete pass over the top-level
      // declarations and the member declarations therein.
      //   0. Compute the pre-type of the types occurring in the signatures of all top-level
      //      and member declarations, compute the pre-type.
      //   1. Process name resolution and type checking _together_ for
      //        - the constraints in redirecting types (newtypes and subset types)
      //        - the right-hand side of const declarations
      //      Solves these constraints together.
      //      TODO: Then, do another cyclicity check among the redirecting types
      //   2. Process name resolution and type check for all other declarations.
      //      These are done individually, since there's no reason to process them together.

      // Phase 0
      FillInPreTypesInSignatures(declarations);

      // Phases 1 and 2
      for (var initialResolutionPass = true;;) {
        foreach (var d in declarations) {
          Contract.Assert(resolver.VisibleInScope(d));

          resolver.allTypeParameters.PushMarker();
          ResolveTypeParameters(d.TypeArgs, false, d);

          ResolveTopLevelDeclaration(d, initialResolutionPass);
          if (d is ClassDecl classDecl && !classDecl.IsDefaultClass) {
            ResolveTopLevelDeclaration(classDecl.NonNullTypeDecl, initialResolutionPass);
          }

          if (d is TopLevelDeclWithMembers dm) {
            currentClass = dm;
            foreach (var member in dm.Members) {
              Contract.Assert(resolver.VisibleInScope(member));
              ResolveMember(member, initialResolutionPass);
            }
            currentClass = null;
          }

          resolver.allTypeParameters.PopMarker();
        }

        if (initialResolutionPass) {
          var ec = ErrorCount;
          SolveAllTypeConstraints($"initial resolution pass in module '{moduleName}'");
          // TODO: do another cyclicity test for redirecting types here
          if (ec == ErrorCount) {
            initialResolutionPass = false;
            continue;
          }
        }
        break;
      }
    }

    private void FillInPreTypesInSignatures(List<TopLevelDecl> declarations) {
      void ComputePreType(Formal formal) {
        Contract.Assume(formal.PreType == null); // precondition
        formal.PreType = Type2PreType(formal.Type);
      }

      void ComputePreTypeField(Field field) {
        Contract.Assume(field.PreType == null); // precondition
        field.PreType = Type2PreType(field.Type);
      }

      void ComputePreTypeFunction(Function function) {
        function.Formals.ForEach(ComputePreType);
        if (function.Result != null) {
          function.Result.PreType = Type2PreType(function.Result.Type);
        }
        function.ResultPreType = Type2PreType(function.ResultType);
      }

      void ComputePreTypeMethod(Method method) {
        method.Ins.ForEach(ComputePreType);
        method.Outs.ForEach(ComputePreType);
      }

      foreach (var d in declarations) {
        if (d is SubsetTypeDecl std) {
          std.Var.PreType = Type2PreType(std.Var.Type);
        } else if (d is NewtypeDecl nd) {
          nd.BasePreType = Type2PreType(nd.BaseType);
          if (nd.Var != null) {
            Contract.Assert(object.ReferenceEquals(nd.BaseType, nd.Var.Type));
            nd.Var.PreType = nd.BasePreType;
          }
        } else if (d is IteratorDecl iter) {
          iter.Ins.ForEach(ComputePreType);
          iter.Outs.ForEach(ComputePreType);
          iter.OutsFields.ForEach(ComputePreTypeField);
        } else if (d is DatatypeDecl dtd) {
          foreach (var ctor in dtd.Ctors) {
            ctor.Formals.ForEach(ComputePreType);
          }
        } else if (d is ClassDecl cl && !cl.IsDefaultClass) {
          var nntd = cl.NonNullTypeDecl;
          nntd.Var.PreType = Type2PreType(nntd.Var.Type);
        }

        if (d is TopLevelDeclWithMembers md) {
          foreach (var m in md.Members) {
            if (m is Field field) {
              ComputePreTypeField(field);
            } else if (m is Function function) {
              ComputePreTypeFunction(function);
              if (function is ExtremePredicate extremePredicate) {
                ComputePreTypeFunction(extremePredicate.PrefixPredicate);
              }
            } else {
              var method = (Method)m;
              ComputePreTypeMethod(method);
              if (method is ExtremeLemma extremeLemma) {
                ComputePreTypeMethod(extremeLemma.PrefixLemma);
              }
            }
          }
        }
      }
    }

    /// <summary>
    /// Resolve declaration "d", depending on the value of "initialResolutionPass". The reason for this
    /// division of labor is that certain declarations support type inference in their signature, so those
    /// declarations processed before any other parts of the declarations are processed.
    ///
    /// If "d" is a newtype or subtype declaration, then
    ///     if "initialResolutionPass", then resolve the declaration's constraint (if any);
    ///     ///     but don't solve the constraints;
    ///     otherwise, resolve everything else about the declaration (including any witness expression and
    ///     any attributes).
    /// If "d" is a const declaration, then
    ///     if "initialResolutionPass", then resolve the declaration's RHS (if any);
    ///     otherwise, resolve everything else about the declaration (including any attributes).
    /// For any other kind of declaration, then
    ///     if "initialResolutionPass", then do nothing;
    ///     otherwise, resolve everything in the declaration.
    ///
    /// If "initialResolutionPass", then type constraints are generated, but not solved; instead, they
    /// are solved by the caller at the end of the initial resolution pass.
    /// If "initialResolutionPass" is false, then the type constraints are solved here.
    ///
    /// This method assumes type parameters have been pushed.
    /// </summary>
    private void ResolveTopLevelDeclaration(TopLevelDecl d, bool initialResolutionPass) {
      if (!initialResolutionPass && !(d is IteratorDecl)) {
        // Note, attributes of iterators are resolved by ResolveIterator, after registering any names in the iterator signature
        ResolveAttributes(d, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false), true);
      }

      if (d is NewtypeDecl newtypeDecl) {
        ResolveConstraintAndWitness(newtypeDecl, initialResolutionPass);
      } else if (d is SubsetTypeDecl subsetTypeDecl) {
        ResolveConstraintAndWitness(subsetTypeDecl, initialResolutionPass);
      } else if (initialResolutionPass) {
        // nothing else to do in this pass
      } else if (d is IteratorDecl iter) {
        // Note, attributes of iterators are resolved by ResolveIterator, after registering any names in the iterator signature.
        // The following method generates the iterator's members, which in turn are resolved below.
        ResolveIterator(iter);
      } else if (d is DatatypeDecl dt) {
        foreach (var ctor in dt.Ctors) {
          ResolveAttributes(ctor, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false), true);
        }
        // resolve any default parameters
        foreach (var ctor in dt.Ctors) {
          scope.PushMarker();
          scope.AllowInstance = false;
          ctor.Formals.ForEach(p => ScopePushAndReport(p, "destructor", false));
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
    
    void ResolveAttributes(IAttributeBearingDeclaration attributeHost, ResolutionContext opts, bool solveConstraints) {
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
          attr.Args.ForEach(arg => ResolveExpression(arg, opts));
          if (solveConstraints) {
            SolveAllTypeConstraints($"attribute of {attributeHost.ToString()}");
          }
        }
      }
    }

    void ResolveConstraintAndWitness(RedirectingTypeDecl dd, bool initialResolutionPass) {
      Contract.Requires(dd != null);
      Contract.Requires(dd.Constraint != null);

      if (initialResolutionPass) {
        if (dd.Var != null) {
          scope.PushMarker();
          ScopePushExpectSuccess(dd.Var, dd.WhatKind + " variable", false);
          ResolveExpression(dd.Constraint, new ResolutionContext(new CodeContextWrapper(dd, true), false));
          ConstrainTypeExprBool(dd.Constraint, dd.WhatKind + " constraint must be of type bool (instead got {0})");
          scope.PopMarker();
          // don't solve the type constraints here
        }
      } else if (dd.Witness != null) {
        var codeContext = new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
        ResolveExpression(dd.Witness, new ResolutionContext(codeContext, false));
        AddSubtypeConstraint(dd.Var.PreType, dd.Witness.PreType, dd.Witness.tok, "witness expression must have type '{0}' (got '{1}')");
        SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' witness");
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
          AddSubtypeConstraint(Type2PreType(formal.Type), Type2PreType(d.Type), d.tok, "default-value expression (of type '{1}') is not assignable to formal (of type '{0}')");
          foreach (var v in Resolver.FreeVariables(d)) {
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
      SolveAllTypeConstraints($"parameter default values of {codeContext.FullSanitizedName}");

      foreach (var cycle in dependencies.AllCycles()) {
        var cy = Util.Comma(" -> ", cycle, v => v.Name) + " -> " + cycle[0].Name;
        ReportError(cycle[0].Tok, $"default-value expressions for parameters contain a cycle: {cy}");
      }
    }

    /// <summary>
    /// Resolve declaration "member", depending on the value of "initialResolutionPass". The reason for this
    /// division of labor is that certain declarations support type inference in their signature, so those
    /// declarations processed before any other parts of the declarations are processed.
    ///
    /// If "member" is a const declaration, then
    ///     if "initialResolutionPass", then generate the constraints for resolving the declaration's RHS (if any);
    ///     otherwise, resolve everything else about the declaration (including any attributes).
    /// For any other kind of declaration,
    ///     if "initialResolutionPass", then do nothing;
    ///     otherwise, resolve everything in the declaration.
    ///
    /// If "initialResolutionPass", then type constraints are generated, but not solved; instead, they
    /// are solved by the caller at the end of the initial resolution pass.
    /// If "initialResolutionPass" is false, then the type constraints are solved here.
    ///
    /// This method assumes type parameters of the enclosing type have been pushed.
    /// </summary>
    void ResolveMember(MemberDecl member, bool initialResolutionPass) {
      Contract.Requires(member != null);
      Contract.Requires(currentClass != null);

      if (initialResolutionPass) {
        if (member is ConstantField constantField && constantField.Rhs != null) {
          var opts = new ResolutionContext(constantField, false);
          ResolveExpression(constantField.Rhs, opts);
        }
        return;
      }
      
      ResolveAttributes(member, new ResolutionContext(new NoContext(currentClass.EnclosingModuleDefinition), false), true);

      if (member is Field) {
        // nothing else to do

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

      // Start resolving specification...
      // we start with the decreases clause, because the _decreases<n> fields were only given type proxies before; we'll know
      // the types only after resolving the decreases clause (and it may be that some of resolution has already seen uses of
      // these fields; so, with no further ado, here we go
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        ResolveExpression(e, new ResolutionContext(iter, false));
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        // If the following type constraint does not hold, then: Bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
        AddSubtypeConstraint(Type2PreType(d.Type), e.PreType, e.tok, "type of field '" + d.Name + "' is {1}, but has been constrained elsewhere to be of type {0}");
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpression(fe, FrameExpressionUse.Reads, iter);
      }
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpression(fe, FrameExpressionUse.Modifies, iter);
      }
      foreach (AttributedExpression e in iter.Requires) {
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
        ResolveExpression(e.E, new ResolutionContext(iter, false));
        ConstrainTypeExprBool(e.E, "Yield precondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.YieldEnsures) {
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        ConstrainTypeExprBool(e.E, "Yield postcondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.Ensures) {
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
      }
      SolveAllTypeConstraints($"specification of iterator '{iter.Name}'");

      ResolveAttributes(iter, new ResolutionContext(iter, false), true);

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
        SolveAllTypeConstraints($"body of iterator '{iter.Name}'");
      }

      currentClass = null;
      scope.PopMarker();  // pop off the AllowInstance setting

      if (postSpecErrorCount == initialErrorCount) {
        iter.CreateIteratorMethodSpecs(resolver);
      }
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveFunction(Function f) {
      Contract.Requires(f != null);

      bool warnShadowingOption = resolver.Options.WarnShadowing;  // save the original warnShadowing value
      bool warnShadowing = false;

      scope.PushMarker();
      if (f.IsStatic) {
        scope.AllowInstance = false;
      }

      if (f.IsGhost) {
        // TODO: the following could be done in a different resolver pass
        foreach (TypeParameter p in f.TypeArgs) {
          if (p.SupportsEquality) {
            ReportWarning(p.tok,
              $"type parameter {p.Name} of ghost {f.WhatKind} {f.Name} is declared (==), which is unnecessary because the {f.WhatKind} doesn't contain any compiled code");
          }
        }
      }

      foreach (Formal p in f.Formals) {
        ScopePushAndReport(p, "parameter", false);
      }
      ResolveAttributes(f, new ResolutionContext(f, false), true);
      // take care of the warnShadowing attribute
      if (Attributes.ContainsBool(f.Attributes, "warnShadowing", ref warnShadowing)) {
        resolver.Options.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }
      ResolveParameterDefaultValues(f.Formals, f);
      foreach (AttributedExpression e in f.Req) {
        ResolveAttributes(e, new ResolutionContext(f, f is TwoStateFunction), false);
        Expression r = e.E;
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction));
        ConstrainTypeExprBool(r, "Precondition must be a boolean (got {0})");
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpression(fr, FrameExpressionUse.Reads, f);
      }
      foreach (AttributedExpression e in f.Ens) {
        Expression r = e.E;
        if (f.Result != null) {
          scope.PushMarker();
          ScopePushAndReport(f.Result, "function result", false); // function return only visible in post-conditions
        }
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction) with { InFunctionPostcondition = true });
        ConstrainTypeExprBool(r, "Postcondition must be a boolean (got {0})");
        if (f.Result != null) {
          scope.PopMarker();
        }
      }
      ResolveAttributes(f.Decreases, new ResolutionContext(f, f is TwoStateFunction), false);
      foreach (Expression r in f.Decreases.Expressions) {
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction));
        // any type is fine
      }
      SolveAllTypeConstraints($"specification of {f.WhatKind} '{f.Name}'");

      if (f.ByMethodBody != null) {
        // The following conditions are assured by the parser and other callers of the Function constructor
        Contract.Assert(f.Body != null);
        Contract.Assert(!f.IsGhost);
      }
      if (f.Body != null) {
        var prevErrorCount = ErrorCount;
        ResolveExpression(f.Body, new ResolutionContext(f, f is TwoStateFunction));
        AddSubtypeConstraint(Type2PreType(f.ResultType), f.Body.PreType, f.tok, "Function body type mismatch (expected {0}, got {1})");
        SolveAllTypeConstraints($"body of {f.WhatKind} '{f.Name}'");

        if (f.ByMethodBody != null) {
          var method = f.ByMethodDecl;
          Contract.Assert(method != null); // this should have been filled in by now
          ResolveMethod(method);
        }
      }

      scope.PopMarker();

      resolver.Options.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethod(Method m) {
      Contract.Requires(m != null);

      try {
        currentMethod = m;

        bool warnShadowingOption = resolver.Options.WarnShadowing;  // save the original warnShadowing value
        bool warnShadowing = false;
        // take care of the warnShadowing attribute
        if (Attributes.ContainsBool(m.Attributes, "warnShadowing", ref warnShadowing)) {
          resolver.Options.WarnShadowing = warnShadowing;  // set the value according to the attribute
        }

        if (m.IsGhost) {
          foreach (TypeParameter p in m.TypeArgs) {
            if (p.SupportsEquality) {
              ReportWarning(p.tok,
                $"type parameter {p.Name} of ghost {m.WhatKind} {m.Name} is declared (==), which is unnecessary because the {m.WhatKind} doesn't contain any compiled code");
            }
          }
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

        ResolveAttributes(m.Mod, new ResolutionContext(m, false), false);
        foreach (FrameExpression fe in m.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, m);
          if (m.IsLemmaLike) {
            ReportError(fe.tok, "{0}s are not allowed to have modifies clauses", m.WhatKind);
          } else if (m.IsGhost) {
#if TODO
            DisallowNonGhostFieldSpecifiers(fe);
#endif
          }
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
        SolveAllTypeConstraints($"specification of {m.WhatKind} '{m.Name}'");

        // Resolve body
        if (m.Body != null) {
          var com = m as ExtremeLemma;
          if (com != null && com.PrefixLemma != null) {
            // The body may mentioned the implicitly declared parameter _k.  Throw it into the
            // scope before resolving the body.
            var k = com.PrefixLemma.Ins[0];
            ScopePushExpectSuccess(k, "_k parameter");
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
          SolveAllTypeConstraints($"body of {m.WhatKind} '{m.Name}'");
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
      ResolveExpression(fe.E, new ResolutionContext(codeContext, codeContext is TwoStateLemma || use == FrameExpressionUse.Unchanged));
      AddGuardedConstraint(() => {
        DPreType dp = fe.E.PreType.Normalize() as DPreType;
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
        if (dp.Decl.Name == "set" || dp.Decl.Name == "iset" || dp.Decl.Name == "seq" || dp.Decl.Name == "multiset") {
          hasCollectionType = true;
          dp = dp.Arguments[0].Normalize() as DPreType;
          if (dp == null) {
            // element type not yet known
            return false;
          }
        }

        if (!DPreType.IsReferenceTypeDecl(dp.Decl) || (hasArrowType && !hasCollectionType)) {
          var expressionMustDenoteObject = "expression must denote an object";
          var collection = "a set/iset/multiset/seq of objects";
          var instead =  "(instead got {0})";
          var errorMsgFormat = use switch {
            FrameExpressionUse.Reads =>
              $"a reads-clause {expressionMustDenoteObject}, {collection}, or a function to {collection} {instead}",
            FrameExpressionUse.Modifies =>
              $"a modifies-clause {expressionMustDenoteObject} or {collection} {instead}",
            FrameExpressionUse.Unchanged =>
              $"an unchanged {expressionMustDenoteObject} or {collection} {instead}"
          };
          ReportError(fe.E.tok, errorMsgFormat, fe.E.PreType);
        }

        if (fe.FieldName != null) {
          var (member, tentativeReceiverType) = FindMember(fe.E.tok, dp, fe.FieldName);
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

#if SOON
      if (SelfTypeSubstitution != null) {
        foreach (var entry in SelfTypeSubstitution) {
          subst.Add(entry.Key, entry.Value);
        }
      }
#endif

#if SOON
      if (receiverTypeBound != null) {
        TopLevelDeclWithMembers cl;
        var udt = receiverTypeBound?.AsNonNullRefType;
        if (udt != null) {
          cl = (TopLevelDeclWithMembers)((NonNullTypeDecl)udt.ResolvedClass).ViewAsClass;
        } else {
          udt = receiverTypeBound.NormalizeExpand() as UserDefinedType;
          cl = udt?.ResolvedClass as TopLevelDeclWithMembers;
        }
        if (cl != null) {
          foreach (var entry in cl.ParentFormalTypeParametersToActuals) {
            var v = entry.Value.Substitute(subst);
            subst.Add(entry.Key, v);
          }
        }
      }
#endif

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
