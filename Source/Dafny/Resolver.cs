#define TI_DEBUG_PRINT
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny
{
  public class Resolver
  {
    readonly BuiltIns builtIns;

    ErrorReporter reporter;
    ModuleSignature moduleInfo = null;

    private bool RevealedInScope(Declaration d) {
      Contract.Requires(d != null);
      Contract.Requires(moduleInfo != null);
      Contract.Requires(moduleInfo.VisibilityScope != null);

      return useCompileSignatures || d.IsRevealedInScope(moduleInfo.VisibilityScope);
    }

    private bool VisibleInScope(Declaration d) {
      Contract.Requires(d != null);
      Contract.Requires(moduleInfo != null);
      Contract.Requires(moduleInfo.VisibilityScope != null);

      return useCompileSignatures || d.IsVisibleInScope(moduleInfo.VisibilityScope);
    }

    FreshIdGenerator defaultTempVarIdGenerator;
    string FreshTempVarName(string prefix, ICodeContext context) {
      var decl = context as Declaration;
      if (decl != null) {
        return decl.IdGenerator.FreshId(prefix);
      }
      // TODO(wuestholz): Is the following code ever needed?
      if (defaultTempVarIdGenerator == null) {
        defaultTempVarIdGenerator = new FreshIdGenerator();
      }
      return defaultTempVarIdGenerator.FreshId(prefix);
    }

    interface IAmbiguousThing<Thing>
    {
      /// <summary>
      /// Returns a plural number of non-null Thing's
      /// </summary>
      ISet<Thing> Pool { get; }
    }
    class AmbiguousThingHelper<Thing> where Thing : class
    {
      public static Thing Create(ModuleDefinition m, Thing a, Thing b, IEqualityComparer<Thing> eq, out ISet<Thing> s) {
        Contract.Requires(a != null);
        Contract.Requires(b != null);
        Contract.Requires(eq != null);
        Contract.Ensures(Contract.Result<Thing>() != null || (Contract.ValueAtReturn(out s) != null || 2 <= Contract.ValueAtReturn(out s).Count));
        s = null;
        if (eq.Equals(a, b)) {
          return a;
        }
        ISet<Thing> sa = a is IAmbiguousThing<Thing> ? ((IAmbiguousThing<Thing>)a).Pool : new HashSet<Thing>() { a };
        ISet<Thing> sb = b is IAmbiguousThing<Thing> ? ((IAmbiguousThing<Thing>)b).Pool : new HashSet<Thing>() { b };
        var union = new HashSet<Thing>(sa.Union(sb, eq));
        if (sa.Count == union.Count) {
          // sb is a subset of sa
          return a;
        } else if (sb.Count == union.Count) {
          // sa is a subset of sb
          return b;
        } else {
          s = union;
          Contract.Assert(2 <= s.Count);
          return null;
        }
      }
      public static string Name(ISet<Thing> s, Func<Thing, string> name) {
        Contract.Requires(s != null);
        Contract.Requires(s.Count != 0);
        string nm = null;
        foreach (var thing in s) {
          string n = name(thing);
          if (nm == null) {
            nm = n;
          } else {
            nm += "/" + n;
          }
        }
        return nm;
      }
      public static string ModuleNames(IAmbiguousThing<Thing> amb, Func<Thing, string> moduleName) {
        Contract.Requires(amb != null);
        Contract.Ensures(Contract.Result<string>() != null);
        string nm = null;
        foreach (var d in amb.Pool) {
          if (nm == null) {
            nm = moduleName(d);
          } else {
            nm += ", " + moduleName(d);
          }
        }
        return nm;
      }
    }

    public class AmbiguousTopLevelDecl : TopLevelDecl, IAmbiguousThing<TopLevelDecl>  // only used with "classes"
    {
      public static TopLevelDecl Create(ModuleDefinition m, TopLevelDecl a, TopLevelDecl b) {
        ISet<TopLevelDecl> s;
        var t = AmbiguousThingHelper<TopLevelDecl>.Create(m, a, b, new Eq(), out s);
        return t ?? new AmbiguousTopLevelDecl(m, AmbiguousThingHelper<TopLevelDecl>.Name(s, tld => tld.Name), s);
      }
      class Eq : IEqualityComparer<TopLevelDecl>
      {
        public bool Equals(TopLevelDecl d0, TopLevelDecl d1) {
          // We'd like to resolve any AliasModuleDecl to whatever module they refer to.
          // It seems that the only way to do that is to look at alias.Signature.ModuleDef,
          // but that is a ModuleDefinition, which is not a TopLevelDecl.  Therefore, we
          // convert to a ModuleDefinition anything that might refer to something that an
          // AliasModuleDecl can refer to; this is AliasModuleDecl and LiteralModuleDecl.
          object a = d0 is ModuleDecl ? ((ModuleDecl)d0).Dereference() : d0;
          object b = d1 is ModuleDecl ? ((ModuleDecl)d1).Dereference() : d1;
          return a == b;
        }
        public int GetHashCode(TopLevelDecl d) {
          object a = d is ModuleDecl ? ((ModuleDecl)d).Dereference() : d;
          return a.GetHashCode();
        }
      }

      public override string WhatKind { get { return Pool.First().WhatKind; } }
      readonly ISet<TopLevelDecl> Pool = new HashSet<TopLevelDecl>();
      ISet<TopLevelDecl> IAmbiguousThing<TopLevelDecl>.Pool { get { return Pool; } }
      private AmbiguousTopLevelDecl(ModuleDefinition m, string name, ISet<TopLevelDecl> pool)
        : base(pool.First().tok, name, m, new List<TypeParameter>(), null) {
        Contract.Requires(name != null);
        Contract.Requires(pool != null && 2 <= pool.Count);
        Pool = pool;
      }
      public string ModuleNames() {
        return AmbiguousThingHelper<TopLevelDecl>.ModuleNames(this, d => d.Module.Name);
      }
    }

    class AmbiguousMemberDecl : MemberDecl, IAmbiguousThing<MemberDecl>  // only used with "classes"
    {
      public static MemberDecl Create(ModuleDefinition m, MemberDecl a, MemberDecl b) {
        ISet<MemberDecl> s;
        var t = AmbiguousThingHelper<MemberDecl>.Create(m, a, b, new Eq(), out s);
        return t ?? new AmbiguousMemberDecl(m, AmbiguousThingHelper<MemberDecl>.Name(s, member => member.Name), s);
      }
      class Eq : IEqualityComparer<MemberDecl>
      {
        public bool Equals(MemberDecl d0, MemberDecl d1) {
          return d0 == d1;
        }
        public int GetHashCode(MemberDecl d) {
          return d.GetHashCode();
        }
      }

      public override string WhatKind { get { return Pool.First().WhatKind; } }
      readonly ISet<MemberDecl> Pool = new HashSet<MemberDecl>();
      ISet<MemberDecl> IAmbiguousThing<MemberDecl>.Pool { get { return Pool; } }
      private AmbiguousMemberDecl(ModuleDefinition m, string name, ISet<MemberDecl> pool)
        : base(pool.First().tok, name, true, pool.First().IsGhost, null) {
        Contract.Requires(name != null);
        Contract.Requires(pool != null && 2 <= pool.Count);
        Pool = pool;
      }
      public string ModuleNames() {
        return AmbiguousThingHelper<MemberDecl>.ModuleNames(this, d => d.EnclosingClass.Module.Name);
      }
    }


    readonly HashSet<RevealableTypeDecl> revealableTypes = new HashSet<RevealableTypeDecl>();
    //types that have been seen by the resolver - used for constraining type inference during exports

    readonly Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> classMembers = new Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>>();
    readonly Dictionary<DatatypeDecl, Dictionary<string, DatatypeCtor>> datatypeCtors = new Dictionary<DatatypeDecl, Dictionary<string, DatatypeCtor>>();
    enum ValuetypeVariety { Bool = 0, Int, Real, BigOrdinal, Bitvector, Map, IMap, None }  // note, these are ordered, so they can be used as indices into valuetypeDecls
    readonly ValuetypeDecl[] valuetypeDecls;
    private Dictionary<TypeParameter, Type> SelfTypeSubstitution;
    readonly Graph<ModuleDecl> dependencies = new Graph<ModuleDecl>();
    private ModuleSignature systemNameInfo = null;
    private bool useCompileSignatures = false;

    private List<IRewriter> rewriters;
    private RefinementTransformer refinementTransformer;

    public Resolver(Program prog) {
      Contract.Requires(prog != null);

      builtIns = prog.BuiltIns;
      reporter = prog.reporter;

      // Map#Items relies on the two destructors for 2-tuples
      builtIns.TupleType(Token.NoToken, 2, true);
      // Several methods and fields rely on 1-argument arrow types
      builtIns.CreateArrowTypeDecl(1);

      valuetypeDecls = new ValuetypeDecl[] {
        new ValuetypeDecl("bool", builtIns.SystemModule, 0, t => t.IsBoolType, typeArgs => Type.Bool),
        new ValuetypeDecl("int", builtIns.SystemModule, 0, t => t.IsNumericBased(Type.NumericPersuation.Int), typeArgs => Type.Int),
        new ValuetypeDecl("real", builtIns.SystemModule, 0, t => t.IsNumericBased(Type.NumericPersuation.Real), typeArgs => Type.Real),
        new ValuetypeDecl("ORDINAL", builtIns.SystemModule, 0, t => t.IsBigOrdinalType, typeArgs => Type.BigOrdinal),
        new ValuetypeDecl("bv", builtIns.SystemModule, 0, t => t.IsBitVectorType, null),  // "bv" represents a family of classes, so no typeTester or type creator is supplied
        new ValuetypeDecl("map", builtIns.SystemModule, 2, t => t.IsMapType, typeArgs => new MapType(true, typeArgs[0], typeArgs[1])),
        new ValuetypeDecl("imap", builtIns.SystemModule, 2, t => t.IsIMapType, typeArgs => new MapType(false, typeArgs[0], typeArgs[1]))
      };
      builtIns.SystemModule.TopLevelDecls.AddRange(valuetypeDecls);
      // Resolution error handling relies on being able to get to the 0-tuple declaration
      builtIns.TupleType(Token.NoToken, 0, true);

      // Populate the members of the basic types
      var floor = new SpecialField(Token.NoToken, "Floor", SpecialField.ID.Floor, null, false, false, false, Type.Int, null);
      floor.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Real].Members.Add(floor.Name, floor);

      var isLimit = new SpecialField(Token.NoToken, "IsLimit", SpecialField.ID.IsLimit, null, false, false, false, Type.Bool, null);
      isLimit.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isLimit.Name, isLimit);

      var isSucc = new SpecialField(Token.NoToken, "IsSucc", SpecialField.ID.IsSucc, null, false, false, false, Type.Bool, null);
      isSucc.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isSucc.Name, isSucc);

      var limitOffset = new SpecialField(Token.NoToken, "Offset", SpecialField.ID.Offset, null, false, false, false, Type.Int, null);
      limitOffset.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(limitOffset.Name, limitOffset);
      builtIns.ORDINAL_Offset = limitOffset;

      var isNat = new SpecialField(Token.NoToken, "IsNat", SpecialField.ID.IsNat, null, false, false, false, Type.Bool, null);
      isNat.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isNat.Name, isNat);

      // Add "Keys", "Values", and "Items" to map, imap
      foreach (var typeVariety in new [] { ValuetypeVariety.Map, ValuetypeVariety.IMap }) {
        var vtd = valuetypeDecls[(int)typeVariety];
        var isFinite = typeVariety == ValuetypeVariety.Map;

        var r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[0]));
        var keys = new SpecialField(Token.NoToken, "Keys", SpecialField.ID.Keys, null, false, false, false, r, null);

        r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[1]));
        var values = new SpecialField(Token.NoToken, "Values", SpecialField.ID.Values, null, false, false, false, r, null);

        var gt = vtd.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
        var dt = builtIns.TupleType(Token.NoToken, 2, true);
        var tupleType = new UserDefinedType(Token.NoToken, dt.Name, dt, gt);
        r = new SetType(isFinite, tupleType);
        var items = new SpecialField(Token.NoToken, "Items", SpecialField.ID.Items, null, false, false, false, r, null);

        foreach (var memb in new[] { keys, values, items }) {
          memb.EnclosingClass = vtd;
          memb.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
          vtd.Members.Add(memb.Name, memb);
        }
      }


      // The result type of the following bitvector methods is the type of the bitvector itself. However, we're representing all bitvector types as
      // a family of types rolled up in one ValuetypeDecl. Therefore, we use the special SelfType as the result type.
      List<Formal> formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, false) };
      var rotateLeft = new SpecialFunction(Token.NoToken, "RotateLeft", prog.BuiltIns.SystemModule, false, false, false, new List<TypeParameter>(), formals, new SelfType(),
        new List<MaybeFreeExpression>(), new List<FrameExpression>(), new List<MaybeFreeExpression>(), new Specification<Expression>(new List<Expression>(), null), null, null, null);
      rotateLeft.EnclosingClass = valuetypeDecls[(int)ValuetypeVariety.Bitvector];
      rotateLeft.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Bitvector].Members.Add(rotateLeft.Name, rotateLeft);

      formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, false) };
      var rotateRight = new SpecialFunction(Token.NoToken, "RotateRight", prog.BuiltIns.SystemModule, false, false, false, new List<TypeParameter>(), formals, new SelfType(),
        new List<MaybeFreeExpression>(), new List<FrameExpression>(), new List<MaybeFreeExpression>(), new Specification<Expression>(new List<Expression>(), null), null, null, null);
      rotateRight.EnclosingClass = valuetypeDecls[(int)ValuetypeVariety.Bitvector];
      rotateRight.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Bitvector].Members.Add(rotateRight.Name, rotateRight);
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(builtIns != null);
      Contract.Invariant(cce.NonNullElements(dependencies));
      Contract.Invariant(cce.NonNullDictionaryAndValues(classMembers) && Contract.ForAll(classMembers.Values, v => cce.NonNullDictionaryAndValues(v)));
      Contract.Invariant(cce.NonNullDictionaryAndValues(datatypeCtors) && Contract.ForAll(datatypeCtors.Values, v => cce.NonNullDictionaryAndValues(v)));
      Contract.Invariant(!inBodyInitContext || currentMethod is Constructor);
    }

    public ValuetypeDecl AsValuetypeDecl(Type t) {
      Contract.Requires(t != null);
      foreach (var vtd in valuetypeDecls) {
        if (vtd.IsThisType(t)) {
          return vtd;
        }
      }
      return null;
    }

    /// <summary>
    /// Check that now two modules that are being compiled have the same CompileName.
    ///
    /// This could happen if they are given the same name using the 'extern' declaration modifier.
    /// </summary>
    /// <param name="prog">The Dafny program being compiled.</param>
    void CheckDupModuleNames(Program prog) {
      // Check that none of the modules have the same CompileName.
      Dictionary<string, ModuleDefinition> compileNameMap = new Dictionary<string, ModuleDefinition>();
      foreach (ModuleDefinition m in prog.CompileModules) {
        if (m.IsAbstract) {
          // the purpose of an abstract module is to skip compilation
          continue;
        }
        string compileName = m.CompileName;
        ModuleDefinition priorModDef;
        if (compileNameMap.TryGetValue(compileName, out priorModDef)) {
          reporter.Error(MessageSource.Resolver, m.tok,
            "Modules '{0}' and '{1}' both have CompileName '{2}'.",
            priorModDef.tok.val, m.tok.val, compileName);
        } else {
          compileNameMap.Add(compileName, m);
        }
      }
    }
    public void ResolveProgram(Program prog) {
      Contract.Requires(prog != null);
      Type.ResetScopes();

      Type.EnableScopes();
      var origErrorCount = reporter.Count(ErrorLevel.Error); //TODO: This is used further below, but not in the >0 comparisons in the next few lines. Is that right?
      var bindings = new ModuleBindings(null);
      var b = BindModuleNames(prog.DefaultModuleDef, bindings);
      bindings.BindName(prog.DefaultModule.Name, prog.DefaultModule, b);
      if (reporter.Count(ErrorLevel.Error) > 0) { return; } // if there were errors, then the implict ModuleBindings data structure invariant
      // is violated, so Processing dependencies will not succeed.
      ProcessDependencies(prog.DefaultModule, b, dependencies);
      // check for cycles in the import graph
      foreach (var cycle in dependencies.AllCycles()) {
        var cy = Util.Comma(" -> ", cycle, m => m.Name);
        reporter.Error(MessageSource.Resolver, cycle[0], "module definition contains a cycle (note: parent modules implicitly depend on submodules): {0}", cy);
      }
      if (reporter.Count(ErrorLevel.Error) > 0) { return; } // give up on trying to resolve anything else

      // fill in module heights
      List<ModuleDecl> sortedDecls = dependencies.TopologicallySortedComponents();
      int h = 0;
      foreach (ModuleDecl md in sortedDecls) {
        md.Height = h;
        if (md is LiteralModuleDecl) {
          var mdef = ((LiteralModuleDecl)md).ModuleDef;
          mdef.Height = h;
          prog.ModuleSigs.Add(mdef, null);
        }
        h++;
      }

      rewriters = new List<IRewriter>();
      refinementTransformer = new RefinementTransformer(prog);
      rewriters.Add(refinementTransformer);
      rewriters.Add(new AutoContractsRewriter(reporter, builtIns));
      rewriters.Add(new OpaqueFunctionRewriter(this.reporter));
      rewriters.Add(new AutoReqFunctionRewriter(this.reporter));
      rewriters.Add(new TimeLimitRewriter(reporter));
      rewriters.Add(new ForallStmtRewriter(reporter));
      rewriters.Add(new ProvideRevealAllRewriter(this.reporter));

      if (DafnyOptions.O.AutoTriggers) {
        rewriters.Add(new QuantifierSplittingRewriter(reporter));
        rewriters.Add(new TriggerGeneratingRewriter(reporter));
      }

      rewriters.Add(new InductionRewriter(reporter));

      systemNameInfo = RegisterTopLevelDecls(prog.BuiltIns.SystemModule, false);
      prog.CompileModules.Add(prog.BuiltIns.SystemModule);
      RevealAllInScope(prog.BuiltIns.SystemModule.TopLevelDecls, systemNameInfo.VisibilityScope);
      ResolveValuetypeDecls();
      // The SystemModule is constructed with all its members already being resolved. Except for
      // the non-null type corresponding to class types.  They are resolved here:
      var systemModuleClassesWithNonNullTypes = new List<TopLevelDecl>(prog.BuiltIns.SystemModule.TopLevelDecls.Where(d => d is ClassDecl && ((ClassDecl)d).NonNullTypeDecl != null));
      foreach (var cl in systemModuleClassesWithNonNullTypes) {
        var d = ((ClassDecl)cl).NonNullTypeDecl;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        ResolveType(d.tok, d.Rhs, d, ResolveTypeOptionEnum.AllowPrefix, d.TypeArgs);
        allTypeParameters.PopMarker();
      }
      ResolveTopLevelDecls_Core(systemModuleClassesWithNonNullTypes, new Graph<IndDatatypeDecl>(), new Graph<CoDatatypeDecl>());

      var compilationModuleClones = new Dictionary<ModuleDefinition, ModuleDefinition>();
      foreach (var decl in sortedDecls) {
        if (decl is LiteralModuleDecl) {
          // The declaration is a literal module, so it has members and such that we need
          // to resolve. First we do refinement transformation. Then we construct the signature
          // of the module. This is the public, externally visible signature. Then we add in
          // everything that the system defines, as well as any "import" (i.e. "opened" modules)
          // directives (currently not supported, but this is where we would do it.) This signature,
          // which is only used while resolving the members of the module is stored in the (basically)
          // global variable moduleInfo. Then the signatures of the module members are resolved, followed
          // by the bodies.
          var literalDecl = (LiteralModuleDecl)decl;
          var m = literalDecl.ModuleDef;

          var errorCount = reporter.Count(ErrorLevel.Error);
          foreach (var r in rewriters) {
            r.PreResolve(m);
          }

          literalDecl.Signature = RegisterTopLevelDecls(m, true);
          literalDecl.Signature.Refines = refinementTransformer.RefinedSig;

          var sig = literalDecl.Signature;
          // set up environment
          var preResolveErrorCount = reporter.Count(ErrorLevel.Error);

          ResolveModuleExport(literalDecl, sig);
          var good = ResolveModuleDefinition(m, sig);

          if (good && reporter.Count(ErrorLevel.Error) == preResolveErrorCount) {
            // Check that the module export gives a self-contained view of the module.
            CheckModuleExportConsistency(m);
          }

          var tempVis = new VisibilityScope();
          tempVis.Augment(sig.VisibilityScope);
          tempVis.Augment(systemNameInfo.VisibilityScope);
          Type.PushScope(tempVis);

          prog.ModuleSigs[m] = sig;

          foreach (var r in rewriters) {
            if (!good || reporter.Count(ErrorLevel.Error) != preResolveErrorCount) {
              break;
            }
            r.PostResolve(m);
          }
          if (good && reporter.Count(ErrorLevel.Error) == errorCount) {
            m.SuccessfullyResolved = true;
          }
          Type.PopScope(tempVis);

          if (reporter.Count(ErrorLevel.Error) == errorCount && !m.IsAbstract) {
            // compilation should only proceed if everything is good, including the signature (which preResolveErrorCount does not include);
            CompilationCloner cloner = new CompilationCloner(compilationModuleClones);
            var nw = cloner.CloneModuleDefinition(m, m.CompileName + "_Compile");
            compilationModuleClones.Add(m, nw);
            var oldErrorsOnly = reporter.ErrorsOnly;
            reporter.ErrorsOnly = true; // turn off warning reporting for the clone
            // Next, compute the compile signature
            Contract.Assert(!useCompileSignatures);
            useCompileSignatures = true;  // set Resolver-global flag to indicate that Signatures should be followed to their CompiledSignature
            Type.DisableScopes();
            var compileSig = RegisterTopLevelDecls(nw, true);
            compileSig.Refines = refinementTransformer.RefinedSig;
            sig.CompileSignature = compileSig;
            foreach (var exportDecl in sig.ExportSets.Values) {
              exportDecl.Signature.CompileSignature = cloner.CloneModuleSignature(exportDecl.Signature, compileSig);
            }
            // Now we're ready to resolve the cloned module definition, using the compile signature

            ResolveModuleDefinition(nw, compileSig);
            prog.CompileModules.Add(nw);
            useCompileSignatures = false;  // reset the flag
            Type.EnableScopes();
            reporter.ErrorsOnly = oldErrorsOnly;
          }
        } else if (decl is AliasModuleDecl) {
          var alias = (AliasModuleDecl)decl;
          // resolve the path
          ModuleSignature p;
          if (ResolveExport(alias, alias.Root, alias.Module, alias.Path, alias.Exports, out p, reporter)) {
            if (alias.Signature == null) {
              alias.Signature = p;
            }
          } else {
            alias.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
          }
        } else if (decl is ModuleFacadeDecl) {
          var abs = (ModuleFacadeDecl)decl;
          ModuleSignature p;
          if (ResolveExport(abs, abs.Root, abs.Module, abs.Path, abs.Exports, out p, reporter)) {
            abs.OriginalSignature = p;
            abs.Signature = MakeAbstractSignature(p, abs.FullCompileName, abs.Height, prog.ModuleSigs, compilationModuleClones);
          } else {
            abs.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
          }
        } else if (decl is ModuleExportDecl) {
          ((ModuleExportDecl)decl).SetupDefaultSignature();

          Contract.Assert(decl.Signature != null);
          Contract.Assert(decl.Signature.VisibilityScope != null);

        } else { Contract.Assert(false); }
        Contract.Assert(decl.Signature != null);
      }
      if (reporter.Count(ErrorLevel.Error) != origErrorCount) {
        // do nothing else
        return;
      }



      // compute IsRecursive bit for mutually recursive functions and methods
      foreach (var module in prog.Modules()) {
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls)) {
          if (clbl is Function) {
            var fn = (Function)clbl;
            if (!fn.IsRecursive) {  // note, self-recursion has already been determined
              int n = module.CallGraph.GetSCCSize(fn);
              if (2 <= n) {
                // the function is mutually recursive (note, the SCC does not determine self recursion)
                fn.IsRecursive = true;
              }
            }
            if (fn.IsRecursive && fn is FixpointPredicate) {
              // this means the corresponding prefix predicate is also recursive
              var prefixPred = ((FixpointPredicate)fn).PrefixPredicate;
              if (prefixPred != null) {
                prefixPred.IsRecursive = true;
              }
            }
          } else {
            var m = (Method)clbl;
            if (!m.IsRecursive) {  // note, self-recursion has already been determined
              int n = module.CallGraph.GetSCCSize(m);
              if (2 <= n) {
                // the function is mutually recursive (note, the SCC does not determine self recursion)
                m.IsRecursive = true;
              }
            }
          }
        }
        foreach (var r in rewriters) {
          r.PostCyclicityResolve(module);
        }
      }


      // fill in default decreases clauses:  for functions and methods, and for loops
      FillInDefaultDecreasesClauses(prog);
      foreach (var module in prog.Modules()) {
        foreach (var clbl in ModuleDefinition.AllItersAndCallables(module.TopLevelDecls)) {
          Statement body = null;
          if (clbl is Method) {
            body = ((Method)clbl).Body;
          } else if (clbl is IteratorDecl) {
            body = ((IteratorDecl)clbl).Body;
          }
          if (body != null) {
            var c = new FillInDefaultLoopDecreases_Visitor(this, clbl);
            c.Visit(body);
          }
        }
      }
      foreach (var module in prog.Modules()) {
        foreach (var iter in ModuleDefinition.AllIteratorDecls(module.TopLevelDecls)) {
          reporter.Info(MessageSource.Resolver, iter.tok, Printer.IteratorClassToString(iter));
        }
      }
      // fill in other additional information
      foreach (var module in prog.Modules()) {
        foreach (var clbl in ModuleDefinition.AllItersAndCallables(module.TopLevelDecls)) {
          Statement body = null;
          if (clbl is FixpointLemma) {
            body = ((FixpointLemma)clbl).PrefixLemma.Body;
          } else if (clbl is Method) {
            body = ((Method)clbl).Body;
          } else if (clbl is IteratorDecl) {
            body = ((IteratorDecl)clbl).Body;
          }
          if (body != null) {
            var c = new ReportOtherAdditionalInformation_Visitor(this);
            c.Visit(body);
          }
        }
      }

      // Determine, for each function, whether someone tries to adjust its fuel parameter
      foreach (var module in prog.Modules()) {
        CheckForFuelAdjustments(module.tok, module.Attributes, module);
        foreach (var clbl in ModuleDefinition.AllItersAndCallables(module.TopLevelDecls)) {
          Statement body = null;
          if (clbl is Method) {
            body = ((Method)clbl).Body;
            CheckForFuelAdjustments(clbl.Tok, ((Method)clbl).Attributes, module);
          } else if (clbl is IteratorDecl) {
            body = ((IteratorDecl)clbl).Body;
            CheckForFuelAdjustments(clbl.Tok, ((IteratorDecl)clbl).Attributes, module);
          } else if (clbl is Function) {
            CheckForFuelAdjustments(clbl.Tok, ((Function)clbl).Attributes, module);
            var c = new FuelAdjustment_Visitor(this);
            var bodyExpr = ((Function)clbl).Body;
            if (bodyExpr != null) {
              c.Visit(bodyExpr, new FuelAdjustment_Context(module));
            }
          }
          if (body != null) {
            var c = new FuelAdjustment_Visitor(this);
            c.Visit(body, new FuelAdjustment_Context(module));
          }
        }
      }

      Type.DisableScopes();
      CheckDupModuleNames(prog);
    }

    void FillInDefaultDecreasesClauses(Program prog) {
      Contract.Requires(prog != null);

      foreach (var module in prog.Modules()) {
        Contract.Assert(Type.GetScope() != null);
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls)) {
          ICallable m;
          string s;
          if (clbl is FixpointLemma) {
            var prefixLemma = ((FixpointLemma)clbl).PrefixLemma;
            m = prefixLemma;
            s = prefixLemma.Name + " ";
          } else {
            m = clbl;
            s = "";
          }
          var anyChangeToDecreases = FillInDefaultDecreases(m, true);

          if (anyChangeToDecreases || m.InferredDecreases || m is PrefixLemma) {
            bool showIt = false;
            if (m is Function) {
              // show the inferred decreases clause only if it will ever matter, i.e., if the function is recursive
              showIt = ((Function)m).IsRecursive;
            } else if (m is PrefixLemma) {
              // always show the decrease clause, since at the very least it will start with "_k", which the programmer did not write explicitly
              showIt = true;
            } else {
              showIt = ((Method)m).IsRecursive;
            }
            if (showIt) {
              s += "decreases " + Util.Comma(", ", m.Decreases.Expressions, Printer.ExprToString);
              // Note, in the following line, we use the location information for "clbl", not "m".  These
              // are the same, except in the case where "clbl" is a CoLemma and "m" is a prefix lemma.
              reporter.Info(MessageSource.Resolver, clbl.Tok, s);
            }
          }
        }
      }
    }

    /// <summary>
    /// Return "true" if this routine makes any change to the decreases clause.  If the decreases clause
    /// starts off essentially empty and a default is provided, then clbl.InferredDecreases is also set
    /// to true.
    /// </summary>
    bool FillInDefaultDecreases(ICallable clbl, bool addPrefixInCoClusters) {
      Contract.Requires(clbl != null);

      if (clbl is FixpointPredicate) {
        // fixpoint-predicates don't have decreases clauses
        return false;
      }
      var anyChangeToDecreases = false;
      var decr = clbl.Decreases.Expressions;
      if (DafnyOptions.O.Dafnycc) {
        if (decr.Count > 1) {
          reporter.Error(MessageSource.Resolver, decr[1].tok, "In dafnycc mode, only one decreases expression is allowed");
        }
        // In dafnycc mode, only consider first argument
        if (decr.Count == 0 && clbl.Ins.Count > 0) {
          var p = clbl.Ins[0];
          if (!(p is ImplicitFormal) && p.Type.IsOrdered) {
            var ie = new IdentifierExpr(p.tok, p.Name);
            ie.Var = p; ie.Type = p.Type;  // resolve it here
            decr.Add(ie);
            return true;
          }
        }
        return false;
      }
      if (decr.Count == 0 || (clbl is PrefixLemma && decr.Count == 1)) {
        // The default for a function starts with the function's reads clause, if any
        if (clbl is Function) {
          var fn = (Function)clbl;
          if (fn.Reads.Count != 0) {
            // start the default lexicographic tuple with the reads clause
            var r = FrameToObjectSet(fn.Reads);
            decr.Add(AutoGeneratedExpression.Create(r));
            anyChangeToDecreases = true;
          }
        }

        // Add one component for each parameter, unless the parameter's type is one that
        // doesn't appear useful to orderings.
        foreach (var p in clbl.Ins) {
          if (!(p is ImplicitFormal) && p.Type.IsOrdered) {
            var ie = new IdentifierExpr(p.tok, p.Name);
            ie.Var = p; ie.Type = p.Type;  // resolve it here
            decr.Add(AutoGeneratedExpression.Create(ie));
            anyChangeToDecreases = true;
          }
        }

        clbl.InferredDecreases = true;  // this indicates that finding a default decreases clause was attempted
      }
      if (addPrefixInCoClusters && clbl is Function) {
        var fn = (Function)clbl;
        switch (fn.CoClusterTarget) {
          case Function.CoCallClusterInvolvement.None:
            break;
          case Function.CoCallClusterInvolvement.IsMutuallyRecursiveTarget:
            // prefix: decreases 0,
            clbl.Decreases.Expressions.Insert(0, Expression.CreateIntLiteral(fn.tok, 0));
            anyChangeToDecreases = true;
            break;
          case Function.CoCallClusterInvolvement.CoRecursiveTargetAllTheWay:
            // prefix: decreases 1,
            clbl.Decreases.Expressions.Insert(0, Expression.CreateIntLiteral(fn.tok, 1));
            anyChangeToDecreases = true;
            break;
          default:
            Contract.Assume(false);  // unexpected case
            break;
        }
      }
      return anyChangeToDecreases;
    }

    public Expression FrameArrowToObjectSet(Expression e, FreshIdGenerator idGen) {
      Contract.Requires(e != null);
      Contract.Requires(idGen != null);
      return FrameArrowToObjectSet(e, idGen, builtIns);
    }

    public static Expression FrameArrowToObjectSet(Expression e, FreshIdGenerator idGen, BuiltIns builtIns) {
      Contract.Requires(e != null);
      Contract.Requires(idGen != null);
      Contract.Requires(builtIns != null);
      var arrTy = e.Type.AsArrowType;
      if (arrTy != null) {
        var bvars = new List<BoundVar>();
        var bexprs = new List<Expression>();
        foreach (var t in arrTy.Args) {
          var bv = new BoundVar(e.tok, idGen.FreshId("_x"), t);
          bvars.Add(bv);
          bexprs.Add(new IdentifierExpr(e.tok, bv.Name) { Type = bv.Type, Var = bv });
        }
        var oVar = new BoundVar(e.tok, idGen.FreshId("_o"), builtIns.ObjectQ());
        var obj = new IdentifierExpr(e.tok, oVar.Name) { Type = oVar.Type, Var = oVar };
        bvars.Add(oVar);

        return
          new SetComprehension(e.tok, true, bvars,
            new BinaryExpr(e.tok, BinaryExpr.Opcode.In, obj,
              new ApplyExpr(e.tok, e, bexprs) {
                Type = new SetType(true, builtIns.ObjectQ())
              }) {
              ResolvedOp = BinaryExpr.ResolvedOpcode.InSet,
              Type = Type.Bool
            }, obj, null) {
            Type = new SetType(true, builtIns.ObjectQ())
          };
      } else {
        return e;
      }
    }

    public Expression FrameToObjectSet(List<FrameExpression> fexprs) {
      Contract.Requires(fexprs != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      List<Expression> sets = new List<Expression>();
      List<Expression> singletons = null;
      var idGen = new FreshIdGenerator();
      foreach (FrameExpression fe in fexprs) {
        Contract.Assert(fe != null);
        if (fe.E is WildcardExpr) {
          // drop wildcards altogether
        } else {
          Expression e = FrameArrowToObjectSet(fe.E, idGen);  // keep only fe.E, drop any fe.Field designation
          Contract.Assert(e.Type != null);  // should have been resolved already
          var eType = e.Type.NormalizeExpand();
          if (eType.IsRefType) {
            // e represents a singleton set
            if (singletons == null) {
              singletons = new List<Expression>();
            }
            singletons.Add(e);
          } else if (eType is SeqType || eType is MultiSetType) {
            // e represents a sequence or multiset
            // Add:  set x :: x in e
            var bv = new BoundVar(e.tok, idGen.FreshId("_s2s_"), ((CollectionType)eType).Arg);
            var bvIE = new IdentifierExpr(e.tok, bv.Name);
            bvIE.Var = bv;  // resolve here
            bvIE.Type = bv.Type;  // resolve here
            var sInE = new BinaryExpr(e.tok, BinaryExpr.Opcode.In, bvIE, e);
            if (eType is SeqType) {
              sInE.ResolvedOp = BinaryExpr.ResolvedOpcode.InSeq;  // resolve here
            } else {
              sInE.ResolvedOp = BinaryExpr.ResolvedOpcode.InMultiSet; // resolve here
            }
            sInE.Type = Type.Bool;  // resolve here
            var s = new SetComprehension(e.tok, true, new List<BoundVar>() { bv }, sInE, bvIE, null);
            s.Type = new SetType(true, builtIns.ObjectQ());  // resolve here
            sets.Add(s);
          } else {
            // e is already a set
            Contract.Assert(eType is SetType);
            sets.Add(e);
          }
        }
      }
      if (singletons != null) {
        Expression display = new SetDisplayExpr(singletons[0].tok, true, singletons);
        display.Type = new SetType(true, builtIns.ObjectQ());  // resolve here
        sets.Add(display);
      }
      if (sets.Count == 0) {
        Expression emptyset = new SetDisplayExpr(Token.NoToken, true, new List<Expression>());
        emptyset.Type = new SetType(true, builtIns.ObjectQ());  // resolve here
        return emptyset;
      } else {
        Expression s = sets[0];
        for (int i = 1; i < sets.Count; i++) {
          BinaryExpr union = new BinaryExpr(s.tok, BinaryExpr.Opcode.Add, s, sets[i]);
          union.ResolvedOp = BinaryExpr.ResolvedOpcode.Union;  // resolve here
          union.Type = new SetType(true, builtIns.ObjectQ());  // resolve here
          s = union;
        }
        return s;
      }
    }

    private void ResolveValuetypeDecls() {
      moduleInfo = systemNameInfo;
      foreach (var valueTypeDecl in valuetypeDecls) {
        foreach (var kv in valueTypeDecl.Members) {
          if (kv.Value is Function) {
            ResolveFunctionSignature((Function)kv.Value);
          } else if (kv.Value is Method) {
            ResolveMethodSignature((Method)kv.Value);
          }
        }
      }
    }

    /// <summary>
    /// Resolves the module definition.
    /// A return code of "false" is an indication of an error that may or may not have
    /// been reported in an error message. So, in order to figure out if m was successfully
    /// resolved, a caller has to check for both a change in error count and a "false"
    /// return value.
    /// </summary>
    private bool ResolveModuleDefinition(ModuleDefinition m, ModuleSignature sig) {
      Contract.Requires(AllTypeConstraints.Count == 0);
      Contract.Ensures(AllTypeConstraints.Count == 0);

      sig.VisibilityScope.Augment(systemNameInfo.VisibilityScope);
      // make sure all imported modules were successfully resolved
      foreach (var d in m.TopLevelDecls) {
        if (d is AliasModuleDecl || d is ModuleFacadeDecl) {
          ModuleSignature importSig;
          if (d is AliasModuleDecl) {
            var alias = (AliasModuleDecl)d;
            importSig = alias.Root != null ? alias.Root.Signature : alias.Signature;
          } else {
            importSig = ((ModuleFacadeDecl)d).OriginalSignature;
          }
          if (importSig.ModuleDef == null || !importSig.ModuleDef.SuccessfullyResolved) {
            if (!m.IsEssentiallyEmptyModuleBody()) {  // say something only if this will cause any testing to be omitted
              reporter.Error(MessageSource.Resolver, d, "not resolving module '{0}' because there were errors in resolving its import '{1}'", m.Name, d.Name);
            }
            return false;
          }
        } else if (d is LiteralModuleDecl) {
          var nested = (LiteralModuleDecl)d;
          if (!nested.ModuleDef.SuccessfullyResolved) {
            if (!m.IsEssentiallyEmptyModuleBody()) {  // say something only if this will cause any testing to be omitted
              reporter.Error(MessageSource.Resolver, nested, "not resolving module '{0}' because there were errors in resolving its nested module '{1}'", m.Name, nested.Name);
            }
            return false;
          }
        }
      }

      // resolve
      var oldModuleInfo = moduleInfo;
      moduleInfo = MergeSignature(sig, systemNameInfo);
      Type.PushScope(moduleInfo.VisibilityScope);
      ResolveOpenedImports(moduleInfo, m, useCompileSignatures, this); // opened imports do not persist
      var datatypeDependencies = new Graph<IndDatatypeDecl>();
      var codatatypeDependencies = new Graph<CoDatatypeDecl>();
      int prevErrorCount = reporter.Count(ErrorLevel.Error);
      ResolveTopLevelDecls_Signatures(m, sig, m.TopLevelDecls, datatypeDependencies, codatatypeDependencies);
      Contract.Assert(AllTypeConstraints.Count == 0);  // signature resolution does not add any type constraints
      ResolveAttributes(m.Attributes, m, new ResolveOpts(new NoContext(m.Module), false)); // Must follow ResolveTopLevelDecls_Signatures, in case attributes refer to members
      SolveAllTypeConstraints();  // solve any type constraints entailed by the attributes
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        ResolveTopLevelDecls_Core(m.TopLevelDecls, datatypeDependencies, codatatypeDependencies);
      }
      Type.PopScope(moduleInfo.VisibilityScope);
      moduleInfo = oldModuleInfo;
      return true;
    }

    // Resolve the exports and detect cycles.
    private void ResolveModuleExport(LiteralModuleDecl literalDecl, ModuleSignature sig) {
      ModuleDefinition m = literalDecl.ModuleDef;
      literalDecl.DefaultExport = sig;
      Graph<ModuleExportDecl> exportDependencies = new Graph<ModuleExportDecl>();
      foreach (TopLevelDecl toplevel in m.TopLevelDecls) {
        if (toplevel is ModuleExportDecl) {
          ModuleExportDecl d = (ModuleExportDecl)toplevel;
          exportDependencies.AddVertex(d);
          foreach (string s in d.Extends) {
            ModuleExportDecl extend;
            if (sig.ExportSets.TryGetValue(s, out extend)) {
              d.ExtendDecls.Add(extend);
              exportDependencies.AddEdge(d, extend);
            } else {
              reporter.Error(MessageSource.Resolver, m.tok, s + " must be an export of " + m.Name + " to be extended");
            }
          }
        }
      }

      // detect cycles in the extend
      var cycleError = false;
      foreach (var cycle in exportDependencies.AllCycles()) {
        var cy = Util.Comma(" -> ", cycle, c => c.Name);
        reporter.Error(MessageSource.Resolver, cycle[0], "module export contains a cycle: {0}", cy);
        cycleError = true;
      }
      if (cycleError) { return; } // give up on trying to resolve anything else

      // fill in the exports for the extends.
      List<ModuleExportDecl> sortedExportDecls = exportDependencies.TopologicallySortedComponents();
      ModuleExportDecl defaultExport = null;
      TopLevelDecl defaultClass;

      sig.TopLevels.TryGetValue("_default", out defaultClass);
      Contract.Assert(defaultClass is ClassDecl);
      Contract.Assert(((ClassDecl)defaultClass).IsDefaultClass);
      defaultClass.AddVisibilityScope(m.VisibilityScope, true);

      foreach (var d in sortedExportDecls) {

        defaultClass.AddVisibilityScope(d.ThisScope, true);

        foreach (var eexports in d.ExtendDecls.Select(e => e.Exports)) {
          d.Exports.AddRange(eexports);
        }

        if (d.ExtendDecls.Count == 0 && d.Exports.Count == 0) {
          // This is an empty export.  This is allowed, but unusual.  It could pop up, for example, if
          // someone temporary comments out everything that the export set provides/reveals.  However,
          // if the name of the export set coincides with something else that's declared at the top
          // level of the module, then this export declaration is more likely an error--the user probably
          // forgot the "provides" or "reveals" keyword.
          Dictionary<string, MemberDecl> members;
          MemberDecl member;
          // Top-level functions and methods are actually recorded as members of the _default class.  We look up the
          // export-set name there.  If the export-set name happens to coincide with some other top-level declaration,
          // then an error will already have been produced ("duplicate name of top-level declaration").
          if (classMembers.TryGetValue((ClassDecl)defaultClass, out members) && members.TryGetValue(d.Name, out member)) {
            reporter.Warning(MessageSource.Resolver, d.tok, "note, this export set is empty (did you perhaps forget the 'provides' or 'reveals' keyword?)");
          }
        }

        foreach (ExportSignature export in d.Exports) {

          // check to see if it is a datatype or a member or
          // static function or method in the enclosing module or its imports
          TopLevelDecl tdecl;
          MemberDecl member;
          TopLevelDecl cldecl;

          Declaration decl = null;
          string name = export.Id;

          if (export.ClassId != null) {
            if (sig.TopLevels.TryGetValue(export.ClassId, out cldecl) &&
              ((cldecl is ClassDecl && ((ClassDecl)cldecl).NonNullTypeDecl == null) || cldecl is NonNullTypeDecl)) {  // we are looking for a class name, not a type name
              var cl = (ClassDecl)cldecl.ViewAsClass;
              var lmem = cl.Members.FirstOrDefault(l => l.Name == export.Id);
              if (lmem != null) {
                decl = lmem;
              } else {
                reporter.Error(MessageSource.Resolver, export.Tok, "No member '{0}' found in class '{1}'", export.Id, export.ClassId);
                continue;
              }
            } else {
              reporter.Error(MessageSource.Resolver, export.ClassIdTok, "No class '{0}' found", export.ClassId);
              continue;
            }
          } else if (sig.TopLevels.TryGetValue(name, out tdecl) && (!(tdecl is ClassDecl) || ((ClassDecl)tdecl).NonNullTypeDecl == null)) {  // pretend that C? types are not there
            // Member of the enclosing module
            decl = tdecl.ViewAsClass;  // interpret the export as a class name, not a type name
          } else if (sig.StaticMembers.TryGetValue(name, out member)) {
            decl = member;
          } else if (sig.ExportSets.ContainsKey(name)) {
            reporter.Error(MessageSource.Resolver, export.Tok, "'{0}' is an export set and cannot be provided/revealed by another export set (did you intend to list it in an \"extends\"?)", name);
            continue;
          } else {
            reporter.Error(MessageSource.Resolver, export.Tok, "'{0}' must be a member of '{1}' to be exported", name, m.Name);
            continue;
          }

          if (!decl.CanBeExported()) {
            reporter.Error(MessageSource.Resolver, export.Tok, "'{0}' is not a valid export of '{1}'", name, m.Name);
            continue;
          }

          if (!export.Opaque && !decl.CanBeRevealed()) {
            reporter.Error(MessageSource.Resolver, export.Tok, "'{0}' cannot be revealed in an export. Use \"provides\" instead.", name);
            continue;
          }

          export.Decl = decl;
          decl.AddVisibilityScope(d.ThisScope, export.Opaque);

          if (export.Decl is ClassDecl) {
            var cl = (ClassDecl)export.Decl;
            if (cl.NonNullTypeDecl != null) {
              cl.NonNullTypeDecl.AddVisibilityScope(d.ThisScope, false);  // the associated non-null type is always exported as revealed
            }
            if (!export.Opaque) {
              foreach (var mdecl in cl.Members) {
                mdecl.AddVisibilityScope(d.ThisScope, false);
              }
            }
          }
        }
      }

      foreach (ModuleExportDecl decl in sortedExportDecls) {
        if (decl.IsDefault) {
          if (defaultExport == null) {
            defaultExport = decl;
          } else {
            reporter.Error(MessageSource.Resolver, m.tok, "more than one default export set declared in module {0}", m.Name);
          }
        }
        // fill in export signature
        ModuleSignature signature = decl.Signature;
        signature.ModuleDef = m;


        foreach (var top in sig.TopLevels.Where(t => t.Value.IsVisibleInScope(signature.VisibilityScope) && t.Value.CanBeExported())) {
          if (!signature.TopLevels.ContainsKey(top.Key)) {
            signature.TopLevels.Add(top.Key, top.Value);
          }

          if (top.Value is DatatypeDecl && top.Value.IsRevealedInScope(signature.VisibilityScope)) {
            foreach (var ctor in ((DatatypeDecl)top.Value).Ctors) {
              if (!signature.Ctors.ContainsKey(ctor.Name)) {
                signature.Ctors.Add(ctor.Name, new Tuple<DatatypeCtor, bool>(ctor, false));
              }
            }
          }

          foreach (var mem in sig.StaticMembers.Where(t => t.Value.IsVisibleInScope(signature.VisibilityScope) && t.Value.CanBeExported())) {
            if (!signature.StaticMembers.ContainsKey(mem.Key)) {
              signature.StaticMembers.Add(mem.Key, (MemberDecl)mem.Value);
            }
          }

        }

      }


      // set the default export set, if it exists
      if (defaultExport != null) {
        literalDecl.DefaultExport = defaultExport.Signature;
      } else if (sortedExportDecls.Count > 0) {
        literalDecl.DefaultExport = null;
      }

      // final pass to propagate visibility of exported imports
      var sigs = sortedExportDecls.Select(d => d.Signature).Concat1(sig);

      foreach (var s in sigs) {
        foreach (var decl in s.TopLevels) {
          if (decl.Value is ModuleDecl && !(decl.Value is ModuleExportDecl)) {
            var modDecl = (ModuleDecl)decl.Value;
            s.VisibilityScope.Augment(modDecl.AccessibleSignature().VisibilityScope);
          }
        }
      }

      HashSet<Tuple<Declaration, bool>> exported = new HashSet<Tuple<Declaration, bool>>();

      //some decls may not be set due to resolution errors
      foreach (var e in sortedExportDecls.SelectMany(e => e.Exports).Where(e => e.Decl != null)) {
        var decl = e.Decl;
        exported.Add(new Tuple<Declaration, bool>(decl, e.Opaque));
        if (!e.Opaque && decl.CanBeRevealed()) {
          exported.Add(new Tuple<Declaration, bool>(decl, true));
        }

        if (decl is ClassDecl && ((ClassDecl)decl).NonNullTypeDecl != null) {
          decl = ((ClassDecl)decl).NonNullTypeDecl;
          exported.Add(new Tuple<Declaration, bool>(decl, e.Opaque));
          if (!e.Opaque && decl.CanBeRevealed()) {
            exported.Add(new Tuple<Declaration, bool>(decl, true));
          }
        }

        if (e.Opaque && (decl is DatatypeDecl || decl is TypeSynonymDecl)) {
          // Datatypes and type synonyms are marked as _provided when they appear in any provided export.  If a
          // declaration is never provided, then either it isn't visible outside the module at all or its whole
          // definition is.  Datatype and type-synonym declarations undergo some inference from their definitions.
          // Such inference should not be done for provided declarations, since different views of the module
          // would then get different inferred properties.
          decl.Attributes = new Attributes("_provided", new List<Expression>(), decl.Attributes);
          reporter.Info(MessageSource.Resolver, decl.tok, "{:_provided}");
        }
      }

      Dictionary<RevealableTypeDecl, bool?> declScopes = new Dictionary<RevealableTypeDecl, bool?>();
      Dictionary<RevealableTypeDecl, bool?> modifies = new Dictionary<RevealableTypeDecl, bool?>();

      //of all existing types, compute the minimum visibility of them for each exported declaration's
      //body and signature
      foreach (var e in exported) {

        declScopes.Clear();
        modifies.Clear();

        foreach (var typ in revealableTypes) {
          declScopes.Add(typ, null);
        }

        foreach (var decl in sortedExportDecls) {
          if (decl.Exports.Exists(ex => ex.Decl == e.Item1 && (e.Item2 || !ex.Opaque))) {
            //if we are revealed, consider those exports where we are provided as well
            var scope = decl.Signature.VisibilityScope;

            foreach (var kv in declScopes) {
              bool? isOpaque = kv.Value;
              var typ = kv.Key;
              if (!typ.AsTopLevelDecl.IsVisibleInScope(scope)) {
                modifies[typ] = null;
                continue;
              }

              if (isOpaque.HasValue && isOpaque.Value) {
                //type is visible here, but known-opaque, so do nothing
                continue;
              }

              modifies[typ] = !typ.AsTopLevelDecl.IsRevealedInScope(scope);
            }

            foreach (var kv in modifies) {
              if (!kv.Value.HasValue) {
                declScopes.Remove(kv.Key);
              } else {
                var exvis = declScopes[kv.Key];
                if (exvis.HasValue) {
                  declScopes[kv.Key] = exvis.Value || kv.Value.Value;
                } else {
                  declScopes[kv.Key] = kv.Value;
                }
              }
            }
            modifies.Clear();
          }
        }

        VisibilityScope newscope = new VisibilityScope(true, e.Item1.Name);

        foreach (var rt in declScopes) {
          if (!rt.Value.HasValue)
            continue;

          rt.Key.AsTopLevelDecl.AddVisibilityScope(newscope, rt.Value.Value);
        }
      }
    }

    //check for export consistency by resolving internal modules
    //this should be effect-free, as it only operates on clones
    private void CheckModuleExportConsistency(ModuleDefinition m) {
      var oldModuleInfo = moduleInfo;
      foreach (var top in m.TopLevelDecls) {
        if (!(top is ModuleExportDecl))
          continue;

        ModuleExportDecl decl = (ModuleExportDecl)top;

        foreach (var export in decl.Exports) {
          if (export.Decl is MemberDecl) {
            var member = (MemberDecl)export.Decl;
            if (!member.EnclosingClass.IsVisibleInScope(decl.Signature.VisibilityScope)) {
              reporter.Error(MessageSource.Resolver, export.Tok, "Cannot export class member '{0}' without providing its enclosing {1} '{2}'", member.Name, member.EnclosingClass.WhatKind, member.EnclosingClass.Name);
            }
          }
        }

        reporter = new ErrorReporterWrapper(reporter,
          String.Format("Raised while checking export set {0}: ", decl.Name));
        var scope = decl.Signature.VisibilityScope;
        Cloner cloner = new ScopeCloner(scope);
        var exportView = cloner.CloneModuleDefinition(m, m.Name);

        var testSig = RegisterTopLevelDecls(exportView, true);
        //testSig.Refines = refinementTransformer.RefinedSig;
        ResolveModuleDefinition(exportView, testSig);
        var wasError = reporter.Count(ErrorLevel.Error) > 0;
        reporter = ((ErrorReporterWrapper)reporter).WrappedReporter;

        if (wasError) {
          reporter.Error(MessageSource.Resolver, decl.tok, "This export set is not consistent: {0}", decl.Name);
        }

      }


      moduleInfo = oldModuleInfo;
    }

    public class ModuleBindings
    {
      private ModuleBindings parent;
      private Dictionary<string, ModuleDecl> modules;
      private Dictionary<string, ModuleBindings> bindings;

      public ModuleBindings(ModuleBindings p) {
        parent = p;
        modules = new Dictionary<string, ModuleDecl>();
        bindings = new Dictionary<string, ModuleBindings>();
      }
      public bool BindName(string name, ModuleDecl subModule, ModuleBindings b) {
        if (modules.ContainsKey(name)) {
          return false;
        } else {
          modules.Add(name, subModule);
          bindings.Add(name, b);
          return true;
        }
      }

      public bool TryLookup(IToken name, out ModuleDecl m) {
        Contract.Requires(name != null);
        return TryLookupFilter(name, out m, l => true);
      }

      public bool TryLookupFilter(IToken name, out ModuleDecl m, Func<ModuleDecl, bool> filter) {
        Contract.Requires(name != null);
        if (modules.TryGetValue(name.val, out m) && filter(m)) {
          return true;
        } else if (parent != null) {
          return parent.TryLookupFilter(name, out m, filter);
        } else return false;
      }
      public IEnumerable<ModuleDecl> ModuleList {
        get { return modules.Values; }
      }
      public ModuleBindings SubBindings(string name) {
        ModuleBindings v = null;
        bindings.TryGetValue(name, out v);
        return v;
      }
    }
    private ModuleBindings BindModuleNames(ModuleDefinition moduleDecl, ModuleBindings parentBindings) {
      var bindings = new ModuleBindings(parentBindings);

      // moduleDecl.PrefixNamedModules is a list of pairs like:
      //     A.B.C  ,  module D { ... }
      // We collect these according to the first component of the prefix, like so:
      //     "A"   ->   (A.B.C  ,  module D { ... })
      var prefixNames = new Dictionary<string, List<Tuple<List<IToken>, LiteralModuleDecl>>>();
      foreach (var tup in moduleDecl.PrefixNamedModules) {
        var id = tup.Item1[0].val;
        List<Tuple<List<IToken>, LiteralModuleDecl>> prev;
        if (!prefixNames.TryGetValue(id, out prev)) {
          prev = new List<Tuple<List<IToken>, LiteralModuleDecl>>();
        }
        prev.Add(tup);
        prefixNames[id] = prev;
      }
      moduleDecl.PrefixNamedModules.Clear();

      foreach (var tld in moduleDecl.TopLevelDecls) {
        if (tld is LiteralModuleDecl) {
          var subdecl = (LiteralModuleDecl)tld;
          // Transfer prefix-named modules downwards into the sub-module
          List<Tuple<List<IToken>, LiteralModuleDecl>> prefixModules;
          if (prefixNames.TryGetValue(subdecl.Name, out prefixModules)) {
            prefixNames.Remove(subdecl.Name);
            prefixModules = prefixModules.ConvertAll(ShortenPrefix);
          } else {
            prefixModules = null;
          }
          BindModuleName_LiteralModuleDecl(subdecl, prefixModules, bindings);
        } else if (tld is ModuleFacadeDecl) {
          var subdecl = (ModuleFacadeDecl)tld;
          if (!bindings.BindName(subdecl.Name, subdecl, null)) {
            if (tld.Module.IsDefaultModule) {
              // the import is not in a module.
              reporter.Error(MessageSource.Resolver, subdecl.tok, "Can't import module {0} when not inside of a module", subdecl.Name);
            } else {
              reporter.Error(MessageSource.Resolver, subdecl.tok, "Duplicate module name: {0}", subdecl.Name);
            }
          }
        } else if (tld is AliasModuleDecl) {
          var subdecl = (AliasModuleDecl)tld;
          if (!bindings.BindName(subdecl.Name, subdecl, null)) {
            if (tld.Module.IsDefaultModule) {
              // the import is not in a module.
              reporter.Error(MessageSource.Resolver, subdecl.tok, "Can't import module {0} when not inside of a module", subdecl.Name);
            } else {
              reporter.Error(MessageSource.Resolver, subdecl.tok, "Duplicate module name: {0}", subdecl.Name);
            }
          }
        }
      }
      // add new modules for any remaining entries in "prefixNames"
      foreach (var entry in prefixNames) {
        var name = entry.Key;
        var prefixNamedModules = entry.Value;
        var tok = prefixNamedModules.First().Item1[0];
        var modDef = new ModuleDefinition(tok, name, new List<IToken>(), false, false, false, null, moduleDecl, null, false);
        // Every module is expected to have a default class, so we create and add one now
        var defaultClass = new DefaultClassDecl(modDef, new List<MemberDecl>());
        modDef.TopLevelDecls.Add(defaultClass);
        // Add the new module to the top-level declarations of its parent and then bind its names as usual
        var subdecl = new LiteralModuleDecl(modDef, moduleDecl);
        moduleDecl.TopLevelDecls.Add(subdecl);
        BindModuleName_LiteralModuleDecl(subdecl, prefixNamedModules.ConvertAll(ShortenPrefix), bindings);
      }
      return bindings;
    }

    private Tuple<List<IToken>, LiteralModuleDecl> ShortenPrefix(Tuple<List<IToken>, LiteralModuleDecl> tup)
    {
      Contract.Requires(tup.Item1.Count != 0);
      var rest = tup.Item1.GetRange(1, tup.Item1.Count - 1);
      return new Tuple<List<IToken>, LiteralModuleDecl>(rest, tup.Item2);
    }

    private void BindModuleName_LiteralModuleDecl(LiteralModuleDecl litmod, List<Tuple<List<IToken>, LiteralModuleDecl>>/*?*/ prefixModules, ModuleBindings parentBindings) {
      Contract.Requires(litmod != null);
      Contract.Requires(parentBindings != null);

      // Transfer prefix-named modules downwards into the sub-module
      if (prefixModules != null) {
        foreach (var tup in prefixModules) {
          if (tup.Item1.Count == 0) {
            tup.Item2.ModuleDef.Module = litmod.ModuleDef;  // change the parent, now that we have found the right parent module for the prefix-named module
            var sm = new LiteralModuleDecl(tup.Item2.ModuleDef, litmod.ModuleDef);  // this will create a ModuleDecl with the right parent
            litmod.ModuleDef.TopLevelDecls.Add(sm);
          } else {
            litmod.ModuleDef.PrefixNamedModules.Add(tup);
          }
        }
      }

      var bindings = BindModuleNames(litmod.ModuleDef, parentBindings);
      if (!parentBindings.BindName(litmod.Name, litmod, bindings)) {
        reporter.Error(MessageSource.Resolver, litmod.tok, "Duplicate module name: {0}", litmod.Name);
      }
    }

    private void ProcessDependenciesDefinition(ModuleDecl decl, ModuleDefinition m, ModuleBindings bindings, Graph<ModuleDecl> dependencies) {
      if (m.RefinementBaseName != null) {
        ModuleDecl other;
        if (!bindings.TryLookup(m.RefinementBaseName, out other)) {
          reporter.Error(MessageSource.Resolver, m.RefinementBaseName, "module {0} named as refinement base does not exist", m.RefinementBaseName.val);
        } else if (other is LiteralModuleDecl && ((LiteralModuleDecl)other).ModuleDef == m) {
          reporter.Error(MessageSource.Resolver, m.RefinementBaseName, "module cannot refine itself: {0}", m.RefinementBaseName.val);
        } else {
          Contract.Assert(other != null);  // follows from postcondition of TryGetValue
          dependencies.AddEdge(decl, other);
          m.RefinementBaseRoot = other;
        }
      }
      foreach (var toplevel in m.TopLevelDecls) {
        if (toplevel is ModuleDecl) {
          var d = (ModuleDecl)toplevel;
          dependencies.AddEdge(decl, d);
          var subbindings = bindings.SubBindings(d.Name);
          ProcessDependencies(d, subbindings ?? bindings, dependencies);
        }
      }
    }
    private void ProcessDependencies(ModuleDecl moduleDecl, ModuleBindings bindings, Graph<ModuleDecl> dependencies) {
      dependencies.AddVertex(moduleDecl);
      if (moduleDecl is LiteralModuleDecl) {
        ProcessDependenciesDefinition(moduleDecl, ((LiteralModuleDecl)moduleDecl).ModuleDef, bindings, dependencies);
      } else if (moduleDecl is AliasModuleDecl) {
        var alias = moduleDecl as AliasModuleDecl;
        ModuleDecl root;
        if (!bindings.TryLookupFilter(alias.Path[0], out root,
          m => alias != m && (((alias.Module == m.Module) && (alias.Exports.Count == 0)) || m is LiteralModuleDecl)))
          reporter.Error(MessageSource.Resolver, alias.tok, ModuleNotFoundErrorMessage(0, alias.Path));
        else {
          dependencies.AddEdge(moduleDecl, root);
          alias.Root = root;
        }
      } else if (moduleDecl is ModuleFacadeDecl) {
        var abs = moduleDecl as ModuleFacadeDecl;
        ModuleDecl root;
        if (!bindings.TryLookupFilter(abs.Path[0], out root,
          m => abs != m && (((abs.Module == m.Module) && (abs.Exports.Count == 0)) || m is LiteralModuleDecl)))
          reporter.Error(MessageSource.Resolver, abs.tok, ModuleNotFoundErrorMessage(0, abs.Path));
        else {
          dependencies.AddEdge(moduleDecl, root);
          abs.Root = root;
        }
      }
    }

    private static string ModuleNotFoundErrorMessage(int i, List<IToken> path) {
      Contract.Requires(path != null);
      Contract.Requires(0 <= i && i < path.Count);
      return "module " + path[i].val + " does not exist" +
        (1 < path.Count ? " (position " + i.ToString() + " in path " + Util.Comma(".", path, x => x.val) + ")" : "");
    }

    [Pure]
    private static bool EquivIfPresent<T1, T2>(Dictionary<T1, T2> dic, T1 key, T2 val)
    where T2 : class {
      T2 val2;
      if (dic.TryGetValue(key, out val2)) {
        return val.Equals(val2);
      }
      return true;
    }

    public static ModuleSignature MergeSignature(ModuleSignature m, ModuleSignature system) {
      Contract.Requires(m != null);
      Contract.Requires(system != null);
      var info = new ModuleSignature();
      // add the system-declared information, among which we know there are no duplicates
      foreach (var kv in system.TopLevels) {
        info.TopLevels.Add(kv.Key, kv.Value);
      }
      foreach (var kv in system.Ctors) {
        info.Ctors.Add(kv.Key, kv.Value);
      }
      foreach (var kv in system.StaticMembers) {
        info.StaticMembers.Add(kv.Key, kv.Value);
      }
      // add for the module itself
      foreach (var kv in m.TopLevels) {
        Contract.Assert(EquivIfPresent(info.TopLevels, kv.Key, kv.Value));
        info.TopLevels[kv.Key] = kv.Value;
      }
      foreach (var kv in m.Ctors) {
        Contract.Assert(EquivIfPresent(info.Ctors, kv.Key, kv.Value));
        info.Ctors[kv.Key] = kv.Value;
      }
      foreach (var kv in m.StaticMembers) {
        Contract.Assert(EquivIfPresent(info.StaticMembers, kv.Key, kv.Value));
        info.StaticMembers[kv.Key] = kv.Value;
      }
      info.IsAbstract = m.IsAbstract;
      info.VisibilityScope = new VisibilityScope();
      info.VisibilityScope.Augment(m.VisibilityScope);
      info.VisibilityScope.Augment(system.VisibilityScope);
      return info;
    }

    public static void ResolveOpenedImports(ModuleSignature sig, ModuleDefinition moduleDef, bool useCompileSignatures, Resolver resolver) {
      var declarations = sig.TopLevels.Values.ToList<TopLevelDecl>();
      var importedSigs = new HashSet<ModuleSignature>() { sig };

      foreach (var top in declarations) {
        if (top is ModuleDecl && ((ModuleDecl)top).Opened) {
          ResolveOpenedImportsWorker(sig, moduleDef, (ModuleDecl)top, importedSigs, useCompileSignatures);
        }
      }

      if (resolver != null) { //needed because ResolveOpenedImports is used statically for a refinement check
        if (sig.TopLevels["_default"] is AmbiguousTopLevelDecl) {
          Contract.Assert(sig.TopLevels["_default"].WhatKind == "class");
          var cl = new DefaultClassDecl(moduleDef, sig.StaticMembers.Values.ToList());
          sig.TopLevels["_default"] = cl;
          resolver.classMembers[cl] = cl.Members.ToDictionary(m => m.Name);
        }
      }
    }

    static void ResolveOpenedImportsWorker(ModuleSignature sig, ModuleDefinition moduleDef, ModuleDecl im, HashSet<ModuleSignature> importedSigs, bool useCompileSignatures) {
      bool useImports = true;
      var s = GetSignatureExt(im.AccessibleSignature(useCompileSignatures), useCompileSignatures);

      if (importedSigs.Contains(s)) {
        return; // we've already got these declarations
      }

      importedSigs.Add(s);

      if (useImports || DafnyOptions.O.IronDafny) {
        // classes:
        foreach (var kv in s.TopLevels) {
          if (!kv.Value.CanBeExported())
            continue;

          if (kv.Value is ModuleDecl && ((ModuleDecl)kv.Value).Opened && DafnyOptions.O.IronDafny) {
            ResolveOpenedImportsWorker(sig, moduleDef, (ModuleDecl)kv.Value, importedSigs, useCompileSignatures);
          }

          // IronDafny: we need to pull the members of the opened module's _default class in so that they can be merged.
          if (useImports || string.Equals(kv.Key, "_default", StringComparison.InvariantCulture)) {
            TopLevelDecl d;
            if (sig.TopLevels.TryGetValue(kv.Key, out d)) {
              sig.TopLevels[kv.Key] = AmbiguousTopLevelDecl.Create(moduleDef, d, kv.Value);
            } else {
              sig.TopLevels.Add(kv.Key, kv.Value);
            }
          }
        }

        if (useImports) {
          // constructors:
          foreach (var kv in s.Ctors) {
            Tuple<DatatypeCtor, bool> pair;
            if (sig.Ctors.TryGetValue(kv.Key, out pair)) {
              // The same ctor can be imported from two different imports (e.g "diamond" imports), in which case,
              // they are not duplicates.
              if (!Object.ReferenceEquals(kv.Value.Item1, pair.Item1)) {
                // mark it as a duplicate
                sig.Ctors[kv.Key] = new Tuple<DatatypeCtor, bool>(pair.Item1, true);
              }
            } else {
              // add new
              sig.Ctors.Add(kv.Key, kv.Value);
            }
          }
        }

        if (useImports || DafnyOptions.O.IronDafny) {
          // static members:
          foreach (var kv in s.StaticMembers) {
            if (!kv.Value.CanBeExported())
              continue;

            MemberDecl md;
            if (sig.StaticMembers.TryGetValue(kv.Key, out md)) {
              sig.StaticMembers[kv.Key] = AmbiguousMemberDecl.Create(moduleDef, md, kv.Value);
            } else {
              // add new
              sig.StaticMembers.Add(kv.Key, kv.Value);
            }
          }
        }

      }
    }

    ModuleSignature RegisterTopLevelDecls(ModuleDefinition moduleDef, bool useImports) {
      Contract.Requires(moduleDef != null);
      var sig = new ModuleSignature();
      sig.ModuleDef = moduleDef;
      sig.IsAbstract = moduleDef.IsAbstract;
      sig.VisibilityScope = new VisibilityScope();
      sig.VisibilityScope.Augment(moduleDef.VisibilityScope);

      List<TopLevelDecl> declarations = moduleDef.TopLevelDecls;

      // This is solely used to detect duplicates amongst the various e
      Dictionary<string, TopLevelDecl> toplevels = new Dictionary<string, TopLevelDecl>();
      // Now add the things present
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);

        if (d is RevealableTypeDecl) {
          revealableTypes.Add((RevealableTypeDecl)d);
        }

        // register the class/datatype/module name
        if (d is ModuleExportDecl export) {
          if (sig.ExportSets.ContainsKey(d.Name)) {
            reporter.Error(MessageSource.Resolver, d, "duplicate name of export set: {0}", d.Name);
          } else {
            sig.ExportSets[d.Name] = export;
          }
        } else if (toplevels.ContainsKey(d.Name)) {
          reporter.Error(MessageSource.Resolver, d, "duplicate name of top-level declaration: {0}", d.Name);
        } else {
          var cl = d as ClassDecl;
          TopLevelDecl dprime = cl != null && cl.NonNullTypeDecl != null ? cl.NonNullTypeDecl : d;
          toplevels[d.Name] = dprime;
          sig.TopLevels[d.Name] = dprime;
        }
        if (d is ModuleDecl) {
          // nothing to do
        } else if (d is OpaqueTypeDecl) {
          // nothing more to register
        } else if (d is TypeSynonymDecl) {
          // nothing more to register
        } else if (d is NewtypeDecl) {
          var cl = (TopLevelDeclWithMembers)d;
          // register the names of the type members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(cl, members);
          RegisterMembers(moduleDef, cl, members);
        } else if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;

          // register the names of the implicit members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(iter, members);

          // First, register the iterator's in- and out-parameters as readonly fields
          foreach (var p in iter.Ins) {
            if (members.ContainsKey(p.Name)) {
              reporter.Error(MessageSource.Resolver, p, "Name of in-parameter is used by another member of the iterator: {0}", p.Name);
            } else {
              var field = new SpecialField(p.tok, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, false, false, p.Type, null);
              field.EnclosingClass = iter;  // resolve here
              field.InheritVisibility(iter);
              members.Add(p.Name, field);
              iter.Members.Add(field);
            }
          }
          var nonDuplicateOuts = new List<Formal>();
          foreach (var p in iter.Outs) {
            if (members.ContainsKey(p.Name)) {
              reporter.Error(MessageSource.Resolver, p, "Name of yield-parameter is used by another member of the iterator: {0}", p.Name);
            } else {
              nonDuplicateOuts.Add(p);
              var field = new SpecialField(p.tok, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, true, true, p.Type, null);
              field.EnclosingClass = iter;  // resolve here
              field.InheritVisibility(iter);
              iter.OutsFields.Add(field);
              members.Add(p.Name, field);
              iter.Members.Add(field);
            }
          }
          foreach (var p in nonDuplicateOuts) {
            var nm = p.Name + "s";
            if (members.ContainsKey(nm)) {
              reporter.Error(MessageSource.Resolver, p.tok, "Name of implicit yield-history variable '{0}' is already used by another member of the iterator", p.Name);
              nm = p.Name + "*";  // bogus name, but at least it'll be unique
            }
            // we add some field to OutsHistoryFields, even if there was an error; the name of the field, in case of error, is not so important
            var tp = new SeqType(p.Type.NormalizeExpand());
            var field = new SpecialField(p.tok, nm, SpecialField.ID.UseIdParam, nm, true, true, false, tp, null);
            field.EnclosingClass = iter;  // resolve here
            field.InheritVisibility(iter);
            iter.OutsHistoryFields.Add(field);  // for now, just record this field (until all parameters have been added as members)
          }
          Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);  // the code above makes sure this holds, even in the face of errors
          // now that already-used 'ys' names have been checked for, add these yield-history variables
          iter.OutsHistoryFields.ForEach(f => {
            members.Add(f.Name, f);
            iter.Members.Add(f);
          });
          // add the additional special variables as fields
          iter.Member_Reads = new SpecialField(iter.tok, "_reads", SpecialField.ID.Reads, null, true, false, false, new SetType(true, builtIns.ObjectQ()), null);
          iter.Member_Modifies = new SpecialField(iter.tok, "_modifies", SpecialField.ID.Modifies, null, true, false, false, new SetType(true, builtIns.ObjectQ()), null);
          iter.Member_New = new SpecialField(iter.tok, "_new", SpecialField.ID.New, null, true, true, true, new SetType(true, builtIns.ObjectQ()), null);
          foreach (var field in new List<Field>() { iter.Member_Reads, iter.Member_Modifies, iter.Member_New }) {
            field.EnclosingClass = iter;  // resolve here
            field.InheritVisibility(iter);
            members.Add(field.Name, field);
            iter.Members.Add(field);
          }
          // finally, add special variables to hold the components of the (explicit or implicit) decreases clause
          FillInDefaultDecreases(iter, false);
          // create the fields; unfortunately, we don't know their types yet, so we'll just insert type proxies for now
          var i = 0;
          foreach (var p in iter.Decreases.Expressions) {
            var nm = "_decreases" + i;
            var field = new SpecialField(p.tok, nm, SpecialField.ID.UseIdParam, nm, true, false, false, new InferredTypeProxy(), null);
            field.EnclosingClass = iter;  // resolve here
            field.InheritVisibility(iter);
            iter.DecreasesFields.Add(field);
            members.Add(field.Name, field);
            iter.Members.Add(field);
            i++;
          }

          // Note, the typeArgs parameter to the following Method/Predicate constructors is passed in as the empty list.  What that is
          // saying is that the Method/Predicate does not take any type parameters over and beyond what the enclosing type (namely, the
          // iterator type) does.
          // --- here comes the constructor
          var init = new Constructor(iter.tok, "_ctor", new List<TypeParameter>(), iter.Ins,
            new List<MaybeFreeExpression>(),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            new List<MaybeFreeExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, null, null);
          // --- here comes predicate Valid()
          var valid = new Predicate(iter.tok, "Valid", false, true, true, new List<TypeParameter>(),
            new List<Formal>(),
            new List<MaybeFreeExpression>(),
            new List<FrameExpression>(),
            new List<MaybeFreeExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, Predicate.BodyOriginKind.OriginalOrInherited, null, null);
          // --- here comes method MoveNext
          var moveNext = new Method(iter.tok, "MoveNext", false, false, new List<TypeParameter>(),
            new List<Formal>(), new List<Formal>() { new Formal(iter.tok, "more", Type.Bool, false, false) },
            new List<MaybeFreeExpression>(),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            new List<MaybeFreeExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, null, null);
          // add these implicit members to the class
          init.EnclosingClass = iter;
          init.InheritVisibility(iter);
          valid.EnclosingClass = iter;
          valid.InheritVisibility(iter);
          moveNext.EnclosingClass = iter;
          moveNext.InheritVisibility(iter);
          iter.HasConstructor = true;
          iter.Member_Init = init;
          iter.Member_Valid = valid;
          iter.Member_MoveNext = moveNext;
          MemberDecl member;
          if (members.TryGetValue(init.Name, out member)) {
            reporter.Error(MessageSource.Resolver, member.tok, "member name '{0}' is already predefined for this iterator", init.Name);
          } else {
            members.Add(init.Name, init);
            iter.Members.Add(init);
          }
          // If the name of the iterator is "Valid" or "MoveNext", one of the following will produce an error message.  That
          // error message may not be as clear as it could be, but the situation also seems unlikely to ever occur in practice.
          if (members.TryGetValue("Valid", out member)) {
            reporter.Error(MessageSource.Resolver, member.tok, "member name 'Valid' is already predefined for iterators");
          } else {
            members.Add(valid.Name, valid);
            iter.Members.Add(valid);
          }
          if (members.TryGetValue("MoveNext", out member)) {
            reporter.Error(MessageSource.Resolver, member.tok, "member name 'MoveNext' is already predefined for iterators");
          } else {
            members.Add(moveNext.Name, moveNext);
            iter.Members.Add(moveNext);
          }

        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          var preMemberErrs = reporter.Count(ErrorLevel.Error);

          // register the names of the class members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(cl, members);
          RegisterMembers(moduleDef, cl, members);

          Contract.Assert(preMemberErrs != reporter.Count(ErrorLevel.Error) || !cl.Members.Except(members.Values).Any());

          if (cl.IsDefaultClass) {
            foreach (MemberDecl m in members.Values) {
              Contract.Assert(!m.HasStaticKeyword || m is ConstantField || DafnyOptions.O.AllowGlobals);  // note, the IsStatic value isn't available yet; when it becomes available, we expect it will have the value 'true'
              if (m is Function || m is Method || m is ConstantField) {
                sig.StaticMembers[m.Name] = m;
              }
            }
          }

        } else if (d is DatatypeDecl) {
          var dt = (DatatypeDecl)d;

          // register the names of the constructors
          var ctors = new Dictionary<string, DatatypeCtor>();
          datatypeCtors.Add(dt, ctors);
          // ... and of the other members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(dt, members);

          foreach (DatatypeCtor ctor in dt.Ctors) {
            if (ctor.Name.EndsWith("?")) {
              reporter.Error(MessageSource.Resolver, ctor, "a datatype constructor name is not allowed to end with '?'");
            } else if (ctors.ContainsKey(ctor.Name)) {
              reporter.Error(MessageSource.Resolver, ctor, "Duplicate datatype constructor name: {0}", ctor.Name);
            } else {
              ctors.Add(ctor.Name, ctor);
              ctor.InheritVisibility(dt);

              // create and add the query "method" (field, really)
              string queryName = ctor.Name + "?";
              var query = new SpecialField(ctor.tok, queryName, SpecialField.ID.UseIdParam, "is_" + ctor.CompileName, false, false, false, Type.Bool, null);
              query.InheritVisibility(dt);
              query.EnclosingClass = dt;  // resolve here
              members.Add(queryName, query);
              ctor.QueryField = query;

              // also register the constructor name globally
              Tuple<DatatypeCtor, bool> pair;
              if (sig.Ctors.TryGetValue(ctor.Name, out pair)) {
                // mark it as a duplicate
                sig.Ctors[ctor.Name] = new Tuple<DatatypeCtor, bool>(pair.Item1, true);
              } else {
                // add new
                sig.Ctors.Add(ctor.Name, new Tuple<DatatypeCtor, bool>(ctor, false));
              }
            }
          }
          // add deconstructors now (that is, after the query methods have been added)
          foreach (DatatypeCtor ctor in dt.Ctors) {
            var formalsUsedInThisCtor = new HashSet<string>();
            foreach (var formal in ctor.Formals) {
              MemberDecl previousMember = null;
              var localDuplicate = false;
              if (formal.HasName) {
                if (members.TryGetValue(formal.Name, out previousMember)) {
                  localDuplicate = formalsUsedInThisCtor.Contains(formal.Name);
                  if (localDuplicate) {
                    reporter.Error(MessageSource.Resolver, ctor, "Duplicate use of deconstructor name in the same constructor: {0}", formal.Name);
                  } else if (previousMember is DatatypeDestructor) {
                    // this is okay, if the destructor has the appropriate type; this will be checked later, after type checking
                  } else {
                    reporter.Error(MessageSource.Resolver, ctor, "Name of deconstructor is used by another member of the datatype: {0}", formal.Name);
                  }
                }
                formalsUsedInThisCtor.Add(formal.Name);
              }
              DatatypeDestructor dtor;
              if (!localDuplicate && previousMember is DatatypeDestructor) {
                // a destructor with this name already existed in (a different constructor in) the datatype
                dtor = (DatatypeDestructor)previousMember;
                dtor.AddAnotherEnclosingCtor(ctor, formal);
              } else {
                // either the destructor has no explicit name, or this constructor declared another destructor with this name, or no previous destructor had this name
                dtor = new DatatypeDestructor(formal.tok, ctor, formal, formal.Name, "dtor_" + formal.CompileName, formal.IsGhost, formal.Type, null);
                dtor.InheritVisibility(dt);
                dtor.EnclosingClass = dt;  // resolve here
                if (formal.HasName && !localDuplicate && previousMember == null) {
                  // the destructor has an explict name and there was no member at all with this name before
                  members.Add(formal.Name, dtor);
                }
              }
              ctor.Destructors.Add(dtor);
            }
          }
          // finally, add any additional user-defined members
          RegisterMembers(moduleDef, dt, members);
        } else {
          Contract.Assert(d is ValuetypeDecl);
        }
      }
      // Now, for each class, register its possibly-null type
      foreach (TopLevelDecl d in declarations) {
        if ((d as ClassDecl)?.NonNullTypeDecl != null) {
          var name = d.Name + "?";
          TopLevelDecl prev;
          if (toplevels.TryGetValue(name, out prev)) {
            reporter.Error(MessageSource.Resolver, d, "a module that already contains a top-level declaration '{0}' is not allowed to declare a {1} '{2}'", name, d.WhatKind, d.Name);
          } else {
            toplevels[name] = d;
            sig.TopLevels[name] = d;
          }
        }
      }
      return sig;
    }

    void RegisterMembers(ModuleDefinition moduleDef, TopLevelDeclWithMembers cl, Dictionary<string, MemberDecl> members) {
      Contract.Requires(moduleDef != null);
      Contract.Requires(cl != null);
      Contract.Requires(members != null);

      foreach (MemberDecl m in cl.Members) {
        if (!members.ContainsKey(m.Name)) {
          members.Add(m.Name, m);
          if (m is Constructor) {
            Contract.Assert(cl is ClassDecl);  // the parser ensures this condition
            if (cl is TraitDecl) {
              reporter.Error(MessageSource.Resolver, m.tok, "a trait is not allowed to declare a constructor");
            } else {
              ((ClassDecl)cl).HasConstructor = true;
            }
          } else if (m is FixpointPredicate || m is FixpointLemma) {
            var extraName = m.Name + "#";
            MemberDecl extraMember;
            var cloner = new Cloner();
            var formals = new List<Formal>();
            Type typeOfK;
            if ((m is FixpointPredicate && ((FixpointPredicate)m).KNat) || (m is FixpointLemma && ((FixpointLemma)m).KNat)) {
              typeOfK = new UserDefinedType(m.tok, "nat", (List<Type>)null);
            } else {
              typeOfK = new BigOrdinalType();
            }
            var k = new ImplicitFormal(m.tok, "_k", typeOfK, true, false);
            reporter.Info(MessageSource.Resolver, m.tok, string.Format("_k: {0}", k.Type));
            formals.Add(k);
            if (m is FixpointPredicate) {
              var cop = (FixpointPredicate)m;
              formals.AddRange(cop.Formals.ConvertAll(cloner.CloneFormal));

              List<TypeParameter> tyvars = cop.TypeArgs.ConvertAll(cloner.CloneTypeParam);

              // create prefix predicate
              cop.PrefixPredicate = new PrefixPredicate(cop.tok, extraName, cop.HasStaticKeyword, cop.IsProtected,
                tyvars, k, formals,
                cop.Req.ConvertAll(cloner.CloneMayBeFreeExpr),
                cop.Reads.ConvertAll(cloner.CloneFrameExpr),
                cop.Ens.ConvertAll(cloner.CloneMayBeFreeExpr),
                new Specification<Expression>(new List<Expression>() { new IdentifierExpr(cop.tok, k.Name) }, null),
                cop.Body,
                null,
                cop);
              extraMember = cop.PrefixPredicate;
              // In the call graph, add an edge from P# to P, since this will have the desired effect of detecting unwanted cycles.
              moduleDef.CallGraph.AddEdge(cop.PrefixPredicate, cop);
            } else {
              var com = (FixpointLemma)m;
              // _k has already been added to 'formals', so append the original formals
              formals.AddRange(com.Ins.ConvertAll(cloner.CloneFormal));
              // prepend _k to the given decreases clause
              var decr = new List<Expression>();
              decr.Add(new IdentifierExpr(com.tok, k.Name));
              decr.AddRange(com.Decreases.Expressions.ConvertAll(cloner.CloneExpr));
              // Create prefix lemma.  Note that the body is not cloned, but simply shared.
              // For a colemma, the postconditions are filled in after the colemma's postconditions have been resolved.
              // For an inductive lemma, the preconditions are filled in after the inductive lemma's preconditions have been resolved.
              var req = com is CoLemma ? com.Req.ConvertAll(cloner.CloneMayBeFreeExpr) : new List<MaybeFreeExpression>();
              var ens = com is CoLemma ? new List<MaybeFreeExpression>() : com.Ens.ConvertAll(cloner.CloneMayBeFreeExpr);
              com.PrefixLemma = new PrefixLemma(com.tok, extraName, com.HasStaticKeyword,
                com.TypeArgs.ConvertAll(cloner.CloneTypeParam), k, formals, com.Outs.ConvertAll(cloner.CloneFormal),
                req, cloner.CloneSpecFrameExpr(com.Mod), ens,
                new Specification<Expression>(decr, null),
                null, // Note, the body for the prefix method will be created once the call graph has been computed and the SCC for the colemma is known
                cloner.CloneAttributes(com.Attributes), com);
              extraMember = com.PrefixLemma;
              // In the call graph, add an edge from M# to M, since this will have the desired effect of detecting unwanted cycles.
              moduleDef.CallGraph.AddEdge(com.PrefixLemma, com);
            }
            extraMember.InheritVisibility(m);
            members.Add(extraName, extraMember);
          }
        } else if (m is Constructor && !((Constructor)m).HasName) {
          reporter.Error(MessageSource.Resolver, m, "More than one anonymous constructor");
        } else {
          reporter.Error(MessageSource.Resolver, m, "Duplicate member name: {0}", m.Name);
        }
      }
    }

    private ModuleSignature MakeAbstractSignature(ModuleSignature p, string Name, int Height, Dictionary<ModuleDefinition, ModuleSignature> mods, Dictionary<ModuleDefinition, ModuleDefinition> compilationModuleClones) {
      Contract.Requires(p != null);
      Contract.Requires(Name != null);
      Contract.Requires(mods != null);
      Contract.Requires(compilationModuleClones != null);
      var errCount = reporter.Count(ErrorLevel.Error);

      var mod = new ModuleDefinition(Token.NoToken, Name + ".Abs", new List<IToken>(), true, true, true, null, null, null, false);
      mod.Height = Height;
      mod.IsToBeVerified = p.ModuleDef.IsToBeVerified;
      bool hasDefaultClass = false;
      foreach (var kv in p.TopLevels) {
        hasDefaultClass = kv.Value is DefaultClassDecl || hasDefaultClass;
        if (!(kv.Value is NonNullTypeDecl)) {
          var clone = CloneDeclaration(p.VisibilityScope, kv.Value, mod, mods, Name, compilationModuleClones);
          mod.TopLevelDecls.Add(clone);
        }
      }
      if (!hasDefaultClass) {
        DefaultClassDecl cl = new DefaultClassDecl(mod, p.StaticMembers.Values.ToList());
        mod.TopLevelDecls.Add(CloneDeclaration(p.VisibilityScope, cl, mod, mods, Name, compilationModuleClones));
      }
      var sig = RegisterTopLevelDecls(mod, true);
      sig.Refines = p.Refines;
      sig.CompileSignature = p;
      sig.IsAbstract = p.IsAbstract;
      mods.Add(mod, sig);
      var good = ResolveModuleDefinition(mod, sig);
      if (good && reporter.Count(ErrorLevel.Error) == errCount) {
        mod.SuccessfullyResolved = true;
      }
      return sig;
    }


    TopLevelDecl CloneDeclaration(VisibilityScope scope, TopLevelDecl d, ModuleDefinition m, Dictionary<ModuleDefinition, ModuleSignature> mods, string Name, Dictionary<ModuleDefinition, ModuleDefinition> compilationModuleClones) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);
      Contract.Requires(mods != null);
      Contract.Requires(Name != null);
      Contract.Requires(compilationModuleClones != null);

      if (d is ModuleFacadeDecl) {
        var abs = (ModuleFacadeDecl)d;
        var sig = MakeAbstractSignature(abs.OriginalSignature, Name + "." + abs.Name, abs.Height, mods, compilationModuleClones);
        var a = new ModuleFacadeDecl(abs.Path, abs.tok, m, abs.Opened, abs.Exports);
        a.Signature = sig;
        a.OriginalSignature = abs.OriginalSignature;
        return a;
      } else {
        return new AbstractSignatureCloner(scope).CloneDeclaration(d, m);
      }
    }


    public bool ResolveExport(ModuleDecl alias, ModuleDecl root, ModuleDefinition parent, List<IToken> Path, List<IToken> Exports, out ModuleSignature p, ErrorReporter reporter) {
      Contract.Requires(Path != null);
      Contract.Requires(Path.Count > 0);
      Contract.Requires(Exports != null);
      Contract.Requires(Exports.Count == 0 || Path.Count == 1); // Path.Count > 1 ==> Exports.Count == 0
      Contract.Requires(Exports.Count == 0 || root is LiteralModuleDecl); // only literal modules may have exports
      if (Path.Count == 1 && root is LiteralModuleDecl) {
        // use the default export set when importing the root
        LiteralModuleDecl decl = (LiteralModuleDecl)root;
        if (Exports.Count == 0) {
          p = decl.DefaultExport;
          if (p == null) {
            // no default view is specified.
            reporter.Error(MessageSource.Resolver, Path[0], "no default export set declared in module: {0}", decl.Name);
            return false;
          }
          return true;
        } else {
          ModuleExportDecl pp;
          if (root.Signature.ExportSets.TryGetValue(Exports[0].val, out pp)) {
            p = pp.Signature;
          } else {
            reporter.Error(MessageSource.Resolver, Exports[0], "no export set '{0}' in module '{1}'", Exports[0].val, decl.Name);
            p = null;
            return false;
          }

          foreach (IToken export in Exports.Skip(1)) {
            if (root.Signature.ExportSets.TryGetValue(export.val, out pp)) {
              Contract.Assert(Object.ReferenceEquals(p.ModuleDef, pp.Signature.ModuleDef));
              ModuleSignature merged = MergeSignature(p, pp.Signature);
              merged.ModuleDef = pp.Signature.ModuleDef;
              merged.CompileSignature = MergeSignature(p.CompileSignature, pp.Signature.CompileSignature);
              p = merged;
            } else {
              reporter.Error(MessageSource.Resolver, export, "no export set {0} in module {1}", export.val, decl.Name);
              p = null;
              return false;
            }
          }
          return true;
        }
      }

      // Although the module is known, we demand it be imported before we're willing to access it.
      var thisImport = parent.TopLevelDecls.FirstOrDefault(t => t.Name == Path[0].val && t != alias);

      if (thisImport == null || !(thisImport is ModuleDecl)) {

        reporter.Error(MessageSource.Resolver, Path[0], ModuleNotFoundErrorMessage(0, Path));
        p = null;
        return false;
      }

      var psig = ((ModuleDecl)thisImport).AccessibleSignature();
      int i = 1;
      while (i < Path.Count) {
        ModuleSignature pp;
        if (psig.FindImport(Path[i].val, out pp)) {
          psig = pp;
          i++;
        } else {
          reporter.Error(MessageSource.Resolver, Path[i], ModuleNotFoundErrorMessage(i, Path));
          break;
        }
      }
      p = psig;
      return i == Path.Count;
    }

    public void RevealAllInScope(List<TopLevelDecl> declarations, VisibilityScope scope) {
      foreach (TopLevelDecl d in declarations) {
        d.AddVisibilityScope(scope, false);
        if (d is TopLevelDeclWithMembers) {
          var cl = (TopLevelDeclWithMembers)d;
          foreach (var mem in cl.Members) {
            if (!mem.ScopeIsInherited) {
              mem.AddVisibilityScope(scope, false);
            }
          }
          var nnd = (cl as ClassDecl)?.NonNullTypeDecl;
          if (nnd != null) {
            nnd.AddVisibilityScope(scope, false);
          }
        }
      }
    }

    public void ResolveTopLevelDecls_Signatures(ModuleDefinition def, ModuleSignature sig, List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<IndDatatypeDecl/*!*/>/*!*/ datatypeDependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ codatatypeDependencies) {
      Contract.Requires(declarations != null);
      Contract.Requires(datatypeDependencies != null);
      Contract.Requires(codatatypeDependencies != null);
      RevealAllInScope(declarations, def.VisibilityScope);

      /* Augment the scoping environment for the current module*/
      foreach (TopLevelDecl d in declarations) {
        if (d is ModuleDecl && !(d is ModuleExportDecl)) {
          var decl = (ModuleDecl)d;
          moduleInfo.VisibilityScope.Augment(decl.AccessibleSignature().VisibilityScope);
          sig.VisibilityScope.Augment(decl.AccessibleSignature().VisibilityScope);
        }
      }
      /*if (sig.Refines != null) {
        moduleInfo.VisibilityScope.Augment(sig.Refines.VisibilityScope);
        sig.VisibilityScope.Augment(sig.Refines.VisibilityScope);
      }*/

      // resolve the trait names that a class extends and register the trait members in the classes that inherit them
      foreach (TopLevelDecl d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          RegisterInheritedMembers(cl);
        }
      }

      var typeRedirectionDependencies = new Graph<RedirectingTypeDecl>();  // this concerns the type directions, not their constraints (which are checked for cyclic dependencies later)
      foreach (TopLevelDecl d in ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(declarations)) {
        Contract.Assert(d != null);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        if (d is OpaqueTypeDecl) {
          // do nothing
        } else if (d is TypeSynonymDecl) {
          var dd = (TypeSynonymDecl)d;
          ResolveType(dd.tok, dd.Rhs, dd, ResolveTypeOptionEnum.AllowPrefix, dd.TypeArgs);
          dd.Rhs.ForeachTypeComponent(ty => {
            var s = ty.AsRedirectingType;
            if (s != null) {
              typeRedirectionDependencies.AddEdge(dd, s);
            }
          });
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          ResolveType(dd.tok, dd.BaseType, dd, ResolveTypeOptionEnum.DontInfer, null);
          dd.BaseType.ForeachTypeComponent(ty => {
            var s = ty.AsRedirectingType;
            if (s != null) {
              typeRedirectionDependencies.AddEdge(dd, s);
            }
          });
          ResolveClassMemberTypes(dd);
        } else if (d is IteratorDecl) {
          ResolveIteratorSignature((IteratorDecl)d);
        } else if (d is ClassDecl) {
          ResolveClassMemberTypes((ClassDecl)d);
        } else if (d is ModuleDecl) {
          var decl = (ModuleDecl)d;
          if (!def.IsAbstract && decl is AliasModuleDecl am && decl.Signature.IsAbstract) {
            reporter.Error(MessageSource.Resolver, am.Path.Last(), "a compiled module ({0}) is not allowed to import an abstract module ({1})", def.Name, Util.Comma(".", am.Path, tok => tok.val));
          }
        } else {
          var dd = (DatatypeDecl)d;
          ResolveCtorTypes(dd, datatypeDependencies, codatatypeDependencies);
          ResolveClassMemberTypes(dd);
        }
        allTypeParameters.PopMarker();
      }

      // Now that all traits have been resolved, let classes inherit the trait members
      foreach (var d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          InheritTraitMembers(cl);
        }
      }

      // perform acyclicity test on type synonyms
      foreach (var cycle in typeRedirectionDependencies.AllCycles()) {
        Contract.Assert(cycle.Count != 0);
        var erste = cycle[0];
        reporter.Error(MessageSource.Resolver, erste.Tok, "Cycle among redirecting types (newtypes, subset types, type synonyms): {0} -> {1}", Util.Comma(" -> ", cycle, syn => syn.Name), erste.Name);
      }
    }

    public static readonly List<NativeType> NativeTypes = new List<NativeType>() {
      new NativeType("byte", 0, 0x100, 8,NativeType.Selection.Byte, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
      new NativeType("sbyte", -0x80, 0x80, 0, NativeType.Selection.SByte, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
      new NativeType("ushort", 0, 0x1_0000, 16, NativeType.Selection.UShort, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
      new NativeType("short", -0x8000, 0x8000, 0, NativeType.Selection.Short, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
      new NativeType("uint", 0, 0x1_0000_0000, 32, NativeType.Selection.UInt, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
      new NativeType("int", -0x8000_0000, 0x8000_0000, 0, NativeType.Selection.Int, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
      new NativeType("number", -0x1f_ffff_ffff_ffff, 0x20_0000_0000_0000, 0, NativeType.Selection.Number,
        DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.JavaScript | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),  // JavaScript integers
      new NativeType("ulong", 0, new BigInteger(0x1_0000_0000) * new BigInteger(0x1_0000_0000), 64, NativeType.Selection.ULong, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
      new NativeType("long", Int64.MinValue, 0x8000_0000_0000_0000, 0, NativeType.Selection.Long, DafnyOptions.CompilationTarget.Csharp | DafnyOptions.CompilationTarget.Go | DafnyOptions.CompilationTarget.Java),
    };

    public void ResolveTopLevelDecls_Core(List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<IndDatatypeDecl/*!*/>/*!*/ datatypeDependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ codatatypeDependencies) {
      Contract.Requires(declarations != null);
      Contract.Requires(cce.NonNullElements(datatypeDependencies));
      Contract.Requires(cce.NonNullElements(codatatypeDependencies));
      Contract.Requires(AllTypeConstraints.Count == 0);

      Contract.Ensures(AllTypeConstraints.Count == 0);

      int prevErrorCount = reporter.Count(ErrorLevel.Error);

      // ---------------------------------- Pass 0 ----------------------------------
      // This pass resolves names, introduces (and may solve) type constraints, and
      // builds the module's call graph.
      // For 'newtype' and subset-type declarations, it also checks that all types were fully
      // determined.
      // ----------------------------------------------------------------------------

      // Resolve the meat of classes and iterators, the definitions of type synonyms, and the type parameters of all top-level type declarations
      // In the first two loops below, resolve the newtype/subset-type declarations and their constraint clauses and const definitions, including
      // filling in .ResolvedOp fields.  This is needed for the resolution of the other declarations, because those other declarations may invoke
      // DiscoverBounds, which looks at the .Constraint or .Rhs field of any such types involved.
      // The third loop resolves the other declarations.  It also resolves any witness expressions of newtype/subset-type declarations.
      foreach (TopLevelDecl topd in declarations) {
        Contract.Assert(topd != null);
        Contract.Assert(VisibleInScope(topd));
        TopLevelDecl d = topd is ClassDecl ? ((ClassDecl)topd).NonNullTypeDecl : topd;
        if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          ResolveAttributes(d.Attributes, d, new ResolveOpts(new NoContext(d.Module), false));
          // this check can be done only after it has been determined that the redirected types do not involve cycles
          AddXConstraint(dd.tok, "NumericType", dd.BaseType, "newtypes must be based on some numeric type (got {0})");
          // type check the constraint, if any
          if (dd.Var == null) {
            SolveAllTypeConstraints();
          } else {
            Contract.Assert(object.ReferenceEquals(dd.Var.Type, dd.BaseType));  // follows from NewtypeDecl invariant
            Contract.Assert(dd.Constraint != null);  // follows from NewtypeDecl invariant

            scope.PushMarker();
            var added = scope.Push(dd.Var.Name, dd.Var);
            Contract.Assert(added == Scope<IVariable>.PushResult.Success);
            ResolveExpression(dd.Constraint, new ResolveOpts(dd, false));
            Contract.Assert(dd.Constraint.Type != null);  // follows from postcondition of ResolveExpression
            ConstrainTypeExprBool(dd.Constraint, "newtype constraint must be of type bool (instead got {0})");
            SolveAllTypeConstraints();
            if (!CheckTypeInference_Visitor.IsDetermined(dd.BaseType.NormalizeExpand())) {
              reporter.Error(MessageSource.Resolver, dd.tok, "newtype's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
            }
            scope.PopMarker();
          }

        } else if (d is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)d;

          allTypeParameters.PushMarker();
          ResolveTypeParameters(d.TypeArgs, false, d);
          ResolveAttributes(d.Attributes, d, new ResolveOpts(new NoContext(d.Module), false));
          // type check the constraint
          Contract.Assert(object.ReferenceEquals(dd.Var.Type, dd.Rhs));  // follows from SubsetTypeDecl invariant
          Contract.Assert(dd.Constraint != null);  // follows from SubsetTypeDecl invariant
          scope.PushMarker();
          var added = scope.Push(dd.Var.Name, dd.Var);
          Contract.Assert(added == Scope<IVariable>.PushResult.Success);
          ResolveExpression(dd.Constraint, new ResolveOpts(dd, false));
          Contract.Assert(dd.Constraint.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(dd.Constraint, "subset-type constraint must be of type bool (instead got {0})");
          SolveAllTypeConstraints();
          if (!CheckTypeInference_Visitor.IsDetermined(dd.Rhs.NormalizeExpand())) {
            reporter.Error(MessageSource.Resolver, dd.tok, "subset type's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
          }
          scope.PopMarker();
          allTypeParameters.PopMarker();
        }
        if (topd is TopLevelDeclWithMembers) {
          var cl = (TopLevelDeclWithMembers)topd;
          currentClass = cl;
          foreach (var member in cl.Members) {
            Contract.Assert(VisibleInScope(member));
            if (member is ConstantField) {
              var field = (ConstantField)member;
              var opts = new ResolveOpts(field, false);
              ResolveAttributes(field.Attributes, field, opts);
              // Resolve the value expression
              if (field.Rhs != null) {
                var ec = reporter.Count(ErrorLevel.Error);
                ResolveExpression(field.Rhs, opts);
                if (reporter.Count(ErrorLevel.Error) == ec) {
                  // make sure initialization only refers to constant field or literal expression
                  if (CheckIsConstantExpr(field, field.Rhs)) {
                    AddAssignableConstraint(field.tok, field.Type, field.Rhs.Type, "type for constant '" + field.Name + "' is '{0}', but its initialization value type is '{1}'");
                  }
                }
              }
              SolveAllTypeConstraints();
              if (!CheckTypeInference_Visitor.IsDetermined(field.Type.NormalizeExpand())) {
                reporter.Error(MessageSource.Resolver, field.tok, "const field's type is not fully determined");
              }
            }
          }
          currentClass = null;
        }
      }
      Contract.Assert(AllTypeConstraints.Count == 0);
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Check type inference, which also discovers bounds, in newtype/subset-type constraints and const declarations
        foreach (TopLevelDecl topd in declarations) {
          TopLevelDecl d = topd is ClassDecl ? ((ClassDecl)topd).NonNullTypeDecl : topd;
          if (d is RedirectingTypeDecl dd && dd.Constraint != null) {
            CheckTypeInference(dd.Constraint, dd);
          }
          if (topd is TopLevelDeclWithMembers cl) {
            foreach (var member in cl.Members) {
              if (member is ConstantField field && field.Rhs != null) {
                CheckTypeInference(field.Rhs, field);
                if (!field.IsGhost) {
                  CheckIsCompilable(field.Rhs);
                }
              }
            }
          }
        }
      }
      // Now, we're ready for the other declarations, along with any witness clauses of newtype/subset-type declarations.
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(AllTypeConstraints.Count == 0);
        if (d is TraitDecl && d.TypeArgs.Count > 0) {
          reporter.Error(MessageSource.Resolver, d, "sorry, traits with type parameters are not supported");
        }
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, false, d);
        if (d is NewtypeDecl || d is SubsetTypeDecl) {
          // NewTypeDecl's and SubsetTypeDecl's were already processed in the loop above, except for any witness clauses
          var dd = (RedirectingTypeDecl)d;
          if (dd.Witness != null) {
            var prevErrCnt = reporter.Count(ErrorLevel.Error);
            ResolveExpression(dd.Witness, new ResolveOpts(dd, false));
            ConstrainSubtypeRelation(dd.Var.Type, dd.Witness.Type, dd.Witness, "witness expression must have type '{0}' (got '{1}')", dd.Var.Type, dd.Witness.Type);
            SolveAllTypeConstraints();
            if (reporter.Count(ErrorLevel.Error) == prevErrCnt) {
              CheckTypeInference(dd.Witness, dd);
            }
            if (reporter.Count(ErrorLevel.Error) == prevErrCnt && dd.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
              CheckIsCompilable(dd.Witness);
            }
          }
          if (d is TopLevelDeclWithMembers dm) {
            ResolveClassMemberBodies(dm);
          }
        } else {
          if (!(d is IteratorDecl)) {
            // Note, attributes of iterators are resolved by ResolvedIterator, after registering any names in the iterator signature
            ResolveAttributes(d.Attributes, d, new ResolveOpts(new NoContext(d.Module), false));
          }
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            ResolveIterator(iter);
            ResolveClassMemberBodies(iter);  // resolve the automatically generated members
          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            ResolveClassMemberBodies(cl);
          } else if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              foreach (var formal in ctor.Formals) {
                AddTypeDependencyEdges((ICallable)d, formal.Type);
              }
            }
            ResolveClassMemberBodies(dt);
          }
        }
        allTypeParameters.PopMarker();
      }

      // ---------------------------------- Pass 1 ----------------------------------
      // This pass:
      // * checks that type inference was able to determine all types
      // * check that shared destructors in datatypes are in agreement
      // * fills in the .ResolvedOp field of binary expressions
      // * discovers bounds for:
      //     - forall statements
      //     - set comprehensions
      //     - map comprehensions
      //     - quantifier expressions
      //     - assign-such-that statements
      //     - compilable let-such-that expressions
      //     - newtype constraints
      //     - subset-type constraints
      // For each statement body that it successfully typed, this pass also:
      // * computes ghost interests
      // * determines/checks tail-recursion.
      // ----------------------------------------------------------------------------

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Check that type inference went well everywhere; this will also fill in the .ResolvedOp field in binary expressions
        // Also, for each datatype, check that shared destructors are in agreement
        foreach (TopLevelDecl d in declarations) {
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            var prevErrCnt = reporter.Count(ErrorLevel.Error);
            iter.Members.Iter(CheckTypeInference_Member);
            if (prevErrCnt == reporter.Count(ErrorLevel.Error)) {
              iter.SubExpressions.Iter(e => CheckExpression(e, this, iter));
            }
            if (iter.Body != null) {
              CheckTypeInference(iter.Body, iter);
              if (prevErrCnt == reporter.Count(ErrorLevel.Error)) {
                ComputeGhostInterest(iter.Body, false, iter);
                CheckExpression(iter.Body, this, iter);
              }
            }
          } else if (d is ClassDecl) {
            var dd = (ClassDecl)d;
            ResolveClassMembers_Pass1(dd);
          } else if (d is SubsetTypeDecl) {
            var dd = (SubsetTypeDecl)d;
            Contract.Assert(dd.Constraint != null);
            CheckExpression(dd.Constraint, this, dd);
          } else if (d is NewtypeDecl) {
            var dd = (NewtypeDecl)d;
            if (dd.Var != null) {
              Contract.Assert(dd.Constraint != null);
              CheckExpression(dd.Constraint, this, dd);
            }
            FigureOutNativeType(dd);
            ResolveClassMembers_Pass1(dd);
          } else if (d is DatatypeDecl) {
            var dd = (DatatypeDecl)d;
            foreach (var member in classMembers[dd].Values) {
              var dtor = member as DatatypeDestructor;
              if (dtor != null) {
                var rolemodel = dtor.CorrespondingFormals[0];
                for (int i = 1; i < dtor.CorrespondingFormals.Count; i++) {
                  var other = dtor.CorrespondingFormals[i];
                  if (!Type.Equal_Improved(rolemodel.Type, other.Type)) {
                    reporter.Error(MessageSource.Resolver, other,
                      "shared destructors must have the same type, but '{0}' has type '{1}' in constructor '{2}' and type '{3}' in constructor '{4}'",
                      rolemodel.Name, rolemodel.Type, dtor.EnclosingCtors[0].Name, other.Type, dtor.EnclosingCtors[i].Name);
                  } else if (rolemodel.IsGhost != other.IsGhost) {
                    reporter.Error(MessageSource.Resolver, other,
                      "shared destructors must agree on whether or not they are ghost, but '{0}' is {1} in constructor '{2}' and {3} in constructor '{4}'",
                      rolemodel.Name,
                      rolemodel.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[0].Name,
                      other.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[i].Name);
                  }
                }
              }
            }
            ResolveClassMembers_Pass1(dd);
          }
        }
      }


      // ---------------------------------- Pass 2 ----------------------------------
      // This pass fills in various additional information.
      // ----------------------------------------------------------------------------

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // fill in the postconditions and bodies of prefix lemmas
        foreach (var com in ModuleDefinition.AllFixpointLemmas(declarations)) {
          var prefixLemma = com.PrefixLemma;
          if (prefixLemma == null) {
            continue;  // something went wrong during registration of the prefix lemma (probably a duplicated fixpoint-lemma name)
          }
          var k = prefixLemma.Ins[0];
          var focalPredicates = new HashSet<FixpointPredicate>();
          if (com is CoLemma) {
            // compute the postconditions of the prefix lemma
            Contract.Assume(prefixLemma.Ens.Count == 0);  // these are not supposed to have been filled in before
            foreach (var p in com.Ens) {
              var coConclusions = new HashSet<Expression>();
              CollectFriendlyCallsInFixpointLemmaSpecification(p.E, true, coConclusions, true, com);
              var subst = new FixpointLemmaSpecificationSubstituter(coConclusions, new IdentifierExpr(k.tok, k.Name), this.reporter, true);
              var post = subst.CloneExpr(p.E);
              prefixLemma.Ens.Add(new MaybeFreeExpression(post, p.IsFree));
              foreach (var e in coConclusions) {
                var fce = e as FunctionCallExpr;
                if (fce != null) {  // the other possibility is that "e" is a BinaryExpr
                  CoPredicate predicate = (CoPredicate)fce.Function;
                  focalPredicates.Add(predicate);
                  // For every focal predicate P in S, add to S all co-predicates in the same strongly connected
                  // component (in the call graph) as P
                  foreach (var node in predicate.EnclosingClass.Module.CallGraph.GetSCC(predicate)) {
                    if (node is CoPredicate) {
                      focalPredicates.Add((CoPredicate)node);
                    }
                  }
                }
              }
            }
          } else {
            // compute the preconditions of the prefix lemma
            Contract.Assume(prefixLemma.Req.Count == 0);  // these are not supposed to have been filled in before
            foreach (var p in com.Req) {
              var antecedents = new HashSet<Expression>();
              CollectFriendlyCallsInFixpointLemmaSpecification(p.E, true, antecedents, false, com);
              var subst = new FixpointLemmaSpecificationSubstituter(antecedents, new IdentifierExpr(k.tok, k.Name), this.reporter, false);
              var pre = subst.CloneExpr(p.E);
              prefixLemma.Req.Add(new MaybeFreeExpression(pre, p.IsFree));
              foreach (var e in antecedents) {
                var fce = (FunctionCallExpr)e;  // we expect "antecedents" to contain only FunctionCallExpr's
                InductivePredicate predicate = (InductivePredicate)fce.Function;
                focalPredicates.Add(predicate);
                // For every focal predicate P in S, add to S all inductive predicates in the same strongly connected
                // component (in the call graph) as P
                foreach (var node in predicate.EnclosingClass.Module.CallGraph.GetSCC(predicate)) {
                  if (node is InductivePredicate) {
                    focalPredicates.Add((InductivePredicate)node);
                  }
                }
              }
            }
          }
          reporter.Info(MessageSource.Resolver, com.tok,
            string.Format("{0} with focal predicate{2} {1}", com.PrefixLemma.Name, Util.Comma(focalPredicates, p => p.Name), focalPredicates.Count == 1 ? "" : "s"));
          // Compute the statement body of the prefix lemma
          Contract.Assume(prefixLemma.Body == null);  // this is not supposed to have been filled in before
          if (com.Body != null) {
            var kMinusOne = new BinaryExpr(com.tok, BinaryExpr.Opcode.Sub, new IdentifierExpr(k.tok, k.Name), new LiteralExpr(com.tok, 1));
            var subst = new FixpointLemmaBodyCloner(com, kMinusOne, focalPredicates, this.reporter);
            var mainBody = subst.CloneBlockStmt(com.Body);
            Expression kk;
            Statement els;
            if (k.Type.IsBigOrdinalType) {
              kk = new MemberSelectExpr(k.tok, new IdentifierExpr(k.tok, k.Name), "Offset");
              // As an "else" branch, we add recursive calls for the limit case.  When automatic induction is on,
              // this get handled automatically, but we still want it in the case when automatic inductino has been
              // turned off.
              //     forall k', params | k' < _k && Precondition {
              //       pp(k', params);
              //     }
              Contract.Assume(builtIns.ORDINAL_Offset != null);  // should have been filled in earlier
              var kId = new IdentifierExpr(com.tok, k);
              var kprimeVar = new BoundVar(com.tok, "_k'", Type.BigOrdinal);
              var kprime = new IdentifierExpr(com.tok, kprimeVar);
              var smaller = Expression.CreateLess(kprime, kId);

              var bvs = new List<BoundVar>();  // TODO: populate with k', params
              var substMap = new Dictionary<IVariable, Expression>();
              foreach (var inFormal in prefixLemma.Ins) {
                if (inFormal == k) {
                  bvs.Add(kprimeVar);
                  substMap.Add(k, kprime);
                } else {
                  var bv = new BoundVar(inFormal.tok, inFormal.Name, inFormal.Type);
                  bvs.Add(bv);
                  substMap.Add(inFormal, new IdentifierExpr(com.tok, bv));
                }
              }

              List<Type> typeApplication;
              Dictionary<TypeParameter, Type> typeArgumentSubstitutions;  // not used
              Expression recursiveCallReceiver;
              List<Expression> recursiveCallArgs;
              Translator.RecursiveCallParameters(com.tok, prefixLemma, prefixLemma.TypeArgs, prefixLemma.Ins, substMap, out typeApplication, out typeArgumentSubstitutions, out recursiveCallReceiver, out recursiveCallArgs);
              var methodSel = new MemberSelectExpr(com.tok, recursiveCallReceiver, prefixLemma.Name);
              methodSel.Member = prefixLemma;  // resolve here
              methodSel.TypeApplication = typeApplication;
              methodSel.Type = new InferredTypeProxy();
              var recursiveCall = new CallStmt(com.tok, com.tok, new List<Expression>(), methodSel, recursiveCallArgs);
              recursiveCall.IsGhost = prefixLemma.IsGhost;  // resolve here

              var range = smaller;  // The range will be strengthened later with the call's precondition, substituted
                                    // appropriately (which can only be done once the precondition has been resolved).
              var attrs = new Attributes("_autorequires", new List<Expression>(), null);
#if VERIFY_CORRECTNESS_OF_TRANSLATION_FORALL_STATEMENT_RANGE
              // don't add the :_trustWellformed attribute
#else
              attrs = new Attributes("_trustWellformed", new List<Expression>(), attrs);
#endif
              attrs = new Attributes("auto_generated", new List<Expression>(), attrs);
              var forallBody = new BlockStmt(com.tok, com.tok, new List<Statement>() { recursiveCall });
              var forallStmt = new ForallStmt(com.tok, com.tok, bvs, attrs, range, new List<MaybeFreeExpression>(), forallBody);
              els = new BlockStmt(com.BodyStartTok, mainBody.EndTok, new List<Statement>() { forallStmt });
            } else {
              kk = new IdentifierExpr(k.tok, k.Name);
              els = null;
            }
            var kPositive = new BinaryExpr(com.tok, BinaryExpr.Opcode.Lt, new LiteralExpr(com.tok, 0), kk);
            var condBody = new IfStmt(com.BodyStartTok, mainBody.EndTok, false, kPositive, mainBody, els);
            prefixLemma.Body = new BlockStmt(com.tok, condBody.EndTok, new List<Statement>() { condBody });
          }
          // The prefix lemma now has all its components, so it's finally time we resolve it
          currentClass = (ClassDecl)prefixLemma.EnclosingClass;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(currentClass.TypeArgs, false, currentClass);
          ResolveTypeParameters(prefixLemma.TypeArgs, false, prefixLemma);
          ResolveMethod(prefixLemma);
          allTypeParameters.PopMarker();
          currentClass = null;
          CheckTypeInference_Member(prefixLemma);
        }
      }

      // Perform the stratosphere check on inductive datatypes, and compute to what extent the inductive datatypes require equality support
      foreach (var dtd in datatypeDependencies.TopologicallySortedComponents()) {
        if (datatypeDependencies.GetSCCRepresentative(dtd) == dtd) {
          // do the following check once per SCC, so call it on each SCC representative
          SccStratosphereCheck(dtd, datatypeDependencies);
          DetermineEqualitySupport(dtd, datatypeDependencies);
        }
      }

      // Set the SccRepr field of codatatypes
      foreach (var repr in codatatypeDependencies.TopologicallySortedComponents()) {
        foreach (var codt in codatatypeDependencies.GetSCC(repr)) {
          codt.SscRepr = repr;
        }
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {  // because CheckCoCalls requires the given expression to have been successfully resolved
        // Perform the guardedness check on co-datatypes
        foreach (var repr in ModuleDefinition.AllFunctionSCCs(declarations)) {
          var module = repr.EnclosingModule;
          bool dealsWithCodatatypes = false;
          foreach (var m in module.CallGraph.GetSCC(repr)) {
            var f = m as Function;
            if (f != null && f.ResultType.InvolvesCoDatatype) {
              dealsWithCodatatypes = true;
              break;
            }
          }
          var coCandidates = new List<CoCallResolution.CoCallInfo>();
          var hasIntraClusterCallsInDestructiveContexts = false;
          foreach (var m in module.CallGraph.GetSCC(repr)) {
            var f = m as Function;
            if (f != null && f.Body != null) {
              var checker = new CoCallResolution(f, dealsWithCodatatypes);
              checker.CheckCoCalls(f.Body);
              coCandidates.AddRange(checker.FinalCandidates);
              hasIntraClusterCallsInDestructiveContexts |= checker.HasIntraClusterCallsInDestructiveContexts;
            } else if (f == null) {
              // the SCC contains a method, which we always consider to be a destructive context
              hasIntraClusterCallsInDestructiveContexts = true;
            }
          }
          if (coCandidates.Count != 0) {
            if (hasIntraClusterCallsInDestructiveContexts) {
              foreach (var c in coCandidates) {
                c.CandidateCall.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsInDestructiveContext;
              }
            } else {
              foreach (var c in coCandidates) {
                c.CandidateCall.CoCall = FunctionCallExpr.CoCallResolution.Yes;
                c.EnclosingCoConstructor.IsCoCall = true;
                reporter.Info(MessageSource.Resolver, c.CandidateCall.tok, "co-recursive call");
              }
              // Finally, fill in the CoClusterTarget field
              // Start by setting all the CoClusterTarget fields to CoRecursiveTargetAllTheWay.
              foreach (var m in module.CallGraph.GetSCC(repr)) {
                var f = (Function)m;  // the cast is justified on account of that we allow co-recursive calls only in clusters that have no methods at all
                f.CoClusterTarget = Function.CoCallClusterInvolvement.CoRecursiveTargetAllTheWay;
              }
              // Then change the field to IsMutuallyRecursiveTarget whenever we see a non-self recursive non-co-recursive call
              foreach (var m in module.CallGraph.GetSCC(repr)) {
                var f = (Function)m;  // cast is justified just like above
                foreach (var call in f.AllCalls) {
                  if (call.CoCall != FunctionCallExpr.CoCallResolution.Yes && call.Function != f && ModuleDefinition.InSameSCC(f, call.Function)) {
                    call.Function.CoClusterTarget = Function.CoCallClusterInvolvement.IsMutuallyRecursiveTarget;
                  }
                }
              }
            }
          }
        }
        // Inferred required equality support for datatypes and type synonyms, and for Function and Method signatures.
        // First, do datatypes and type synonyms until a fixpoint is reached.
        bool inferredSomething;
        do {
          inferredSomething = false;
          foreach (var d in declarations) {
            if (Attributes.Contains(d.Attributes, "_provided")) {
              // Don't infer required-equality-support for the type parameters, since there are
              // scopes that see the name of the declaration but not its body.
            } else if (d is DatatypeDecl) {
              var dt = (DatatypeDecl)d;
              foreach (var tp in dt.TypeArgs) {
                if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                  // here's our chance to infer the need for equality support
                  foreach (var ctor in dt.Ctors) {
                    foreach (var arg in ctor.Formals) {
                      if (InferRequiredEqualitySupport(tp, arg.Type)) {
                        tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                        inferredSomething = true;
                        goto DONE_DT;  // break out of the doubly-nested loop
                      }
                    }
                  }
                  DONE_DT:;
                }
              }
            } else if (d is TypeSynonymDecl) {
              var syn = (TypeSynonymDecl)d;
              foreach (var tp in syn.TypeArgs) {
                if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                  // here's our chance to infer the need for equality support
                  if (InferRequiredEqualitySupport(tp, syn.Rhs)) {
                    tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    inferredSomething = true;
                  }
                }
              }
            }
          }
        } while (inferredSomething);
        // Now do it for Function and Method signatures.
        foreach (var d in declarations) {
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            var done = false;
            foreach (var tp in iter.TypeArgs) {
              if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                // here's our chance to infer the need for equality support
                foreach (var p in iter.Ins) {
                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    done = true;
                    break;
                  }
                }
                foreach (var p in iter.Outs) {
                  if (done) break;
                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    break;
                  }
                }
              }
            }
          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            foreach (var member in cl.Members) {
              if (!member.IsGhost) {
                if (member is Function) {
                  var f = (Function)member;
                  foreach (var tp in f.TypeArgs) {
                    if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                      // here's our chance to infer the need for equality support
                      if (InferRequiredEqualitySupport(tp, f.ResultType)) {
                        tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                      } else {
                        foreach (var p in f.Formals) {
                          if (InferRequiredEqualitySupport(tp, p.Type)) {
                            tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                            break;
                          }
                        }
                      }
                    }
                  }
                } else if (member is Method) {
                  var m = (Method)member;
                  bool done = false;
                  foreach (var tp in m.TypeArgs) {
                    if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                      // here's our chance to infer the need for equality support
                      foreach (var p in m.Ins) {
                        if (InferRequiredEqualitySupport(tp, p.Type)) {
                          tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                          done = true;
                          break;
                        }
                      }
                      foreach (var p in m.Outs) {
                        if (done) break;
                        if (InferRequiredEqualitySupport(tp, p.Type)) {
                          tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                          break;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        // Check that functions claiming to be abstemious really are
        foreach (var fn in ModuleDefinition.AllFunctions(declarations)) {
          if (fn.Body != null) {
            var abstemious = true;
            if (Attributes.ContainsBool(fn.Attributes, "abstemious", ref abstemious) && abstemious) {
              if (CoCallResolution.GuaranteedCoCtors(fn) == 0) {
                reporter.Error(MessageSource.Resolver, fn, "the value returned by an abstemious function must come from invoking a co-constructor");
              } else {
                CheckDestructsAreAbstemiousCompliant(fn.Body);
              }
            }
          }
        }
        // Check that all == and != operators in non-ghost contexts are applied to equality-supporting types.
        // Note that this check can only be done after determining which expressions are ghosts.
        foreach (var d in declarations) {
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            foreach (var p in iter.Ins) {
              if (!p.IsGhost) {
                CheckEqualityTypes_Type(p.tok, p.Type);
              }
            }
            foreach (var p in iter.Outs) {
              if (!p.IsGhost) {
                CheckEqualityTypes_Type(p.tok, p.Type);
              }
            }
            if (iter.Body != null) {
              CheckEqualityTypes_Stmt(iter.Body);
            }
          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            foreach (var member in cl.Members) {
              if (!member.IsGhost) {
                if (member is Field) {
                  var f = (Field)member;
                  CheckEqualityTypes_Type(f.tok, f.Type);
                } else if (member is Function) {
                  var f = (Function)member;
                  foreach (var p in f.Formals) {
                    if (!p.IsGhost) {
                      CheckEqualityTypes_Type(p.tok, p.Type);
                    }
                  }
                  CheckEqualityTypes_Type(f.tok, f.ResultType);
                  if (f.Body != null) {
                    CheckEqualityTypes(f.Body);
                  }
                } else if (member is Method) {
                  var m = (Method)member;
                  foreach (var p in m.Ins) {
                    if (!p.IsGhost) {
                      CheckEqualityTypes_Type(p.tok, p.Type);
                    }
                  }
                  foreach (var p in m.Outs) {
                    if (!p.IsGhost) {
                      CheckEqualityTypes_Type(p.tok, p.Type);
                    }
                  }
                  if (m.Body != null) {
                    CheckEqualityTypes_Stmt(m.Body);
                  }
                }
              }
            }
          } else if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              foreach (var p in ctor.Formals) {
                if (!p.IsGhost) {
                  CheckEqualityTypes_Type(p.tok, p.Type);
                }
              }
            }
          } else if (d is TypeSynonymDecl) {
            var syn = (TypeSynonymDecl)d;
            CheckEqualityTypes_Type(syn.tok, syn.Rhs);
            if (syn.MustSupportEquality && !syn.Rhs.SupportsEquality) {
              reporter.Error(MessageSource.Resolver, syn.tok, "type '{0}' declared as supporting equality, but the RHS type ({1}) does not", syn.Name, syn.Rhs);
            }
          }
        }
        // Check that fixpoint-predicates are not recursive with non-fixpoint-predicate functions (and only
        // with fixpoint-predicates of the same polarity), and
        // check that colemmas are not recursive with non-colemma methods.
        // Also, check that the constraints of newtypes/subset-types do not depend on the type itself.
        // And check that const initializers are not cyclic.
        var cycleErrorHasBeenReported = new HashSet<ICallable>();
        foreach (var d in declarations) {
          if (d is ClassDecl) {
            foreach (var member in ((ClassDecl)d).Members) {
              if (member is FixpointPredicate) {
                var fn = (FixpointPredicate)member;
                // Check here for the presence of any 'ensures' clauses, which are not allowed (because we're not sure
                // of their soundness)
                if (fn.Ens.Count != 0) {
                  reporter.Error(MessageSource.Resolver, fn.Ens[0].E.tok, "a {0} is not allowed to declare any ensures clause", member.WhatKind);
                }
                if (fn.Body != null) {
                  FixpointPredicateChecks(fn.Body, fn, CallingPosition.Positive);
                }
              } else if (member is FixpointLemma) {
                var m = (FixpointLemma)member;
                if (m.Body != null) {
                  FixpointLemmaChecks(m.Body, m);
                }
              } else if (member is ConstantField) {
                var cf = (ConstantField)member;
                if (cf.EnclosingModule.CallGraph.GetSCCSize(cf) != 1) {
                  var r = cf.EnclosingModule.CallGraph.GetSCCRepresentative(cf);
                  if (cycleErrorHasBeenReported.Contains(r)) {
                    // An error has already been reported for this cycle, so don't report another.
                    // Note, the representative, "r", may itself not be a const.
                  } else {
                    cycleErrorHasBeenReported.Add(r);
                    var cycle = Util.Comma(" -> ", cf.EnclosingModule.CallGraph.GetSCC(cf), clbl => clbl.NameRelativeToModule);
                    reporter.Error(MessageSource.Resolver, cf.tok, "const definition contains a cycle: " + cycle);
                  }
                }
              }
            }
          } else if (d is SubsetTypeDecl || d is NewtypeDecl) {
            var dd = (RedirectingTypeDecl)d;
            if (d.Module.CallGraph.GetSCCSize(dd) != 1) {
              var r = d.Module.CallGraph.GetSCCRepresentative(dd);
              if (cycleErrorHasBeenReported.Contains(r)) {
                // An error has already been reported for this cycle, so don't report another.
                // Note, the representative, "r", may itself not be a const.
              } else {
                cycleErrorHasBeenReported.Add(r);
                var cycle = Util.Comma(" -> ", d.Module.CallGraph.GetSCC(dd), clbl => clbl.NameRelativeToModule);
                reporter.Error(MessageSource.Resolver, d.tok, "recursive constraint dependency involving a {0}: {1}", d.WhatKind, cycle);
              }
            }
          }
        }
      }

      // ---------------------------------- Pass 3 ----------------------------------
      // Further checks
      // ----------------------------------------------------------------------------

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Check that type-parameter variance is respected in type definitions
        foreach (TopLevelDecl d in declarations) {
          if (d is IteratorDecl || d is ClassDecl) {
            foreach (var tp in d.TypeArgs) {
              if (tp.Variance != TypeParameter.TPVariance.Non) {
                reporter.Error(MessageSource.Resolver, tp.tok, "{0} declarations only support non-variant type parameters", d.WhatKind);
              }
            }
          } else if (d is TypeSynonymDecl) {
            var dd = (TypeSynonymDecl)d;
            CheckVariance(dd.Rhs, dd, TypeParameter.TPVariance.Co, false);
          } else if (d is NewtypeDecl) {
            var dd = (NewtypeDecl)d;
            CheckVariance(dd.BaseType, dd, TypeParameter.TPVariance.Co, false);
          } else if (d is DatatypeDecl) {
            var dd = (DatatypeDecl)d;
            foreach (var ctor in dd.Ctors) {
              ctor.Formals.Iter(formal => CheckVariance(formal.Type, dd, TypeParameter.TPVariance.Co, false));
            }
          }
        }
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Check that usage of "this" is restricted before "new;" in constructor bodies,
        // and that a class without any constructor only has fields with known initializers.
        // Also check that static fields (which are necessarily const) have initializers.
        var cdci = new CheckDividedConstructorInit_Visitor(this);
        foreach (var cl in ModuleDefinition.AllClasses(declarations)) {
          if (cl is TraitDecl) {
            // traits never have constructors, but check for static consts
            foreach (var member in cl.Members) {
              if (member is ConstantField && member.IsStatic && !member.IsGhost) {
                var f = (ConstantField)member;
                if (!cl.Module.IsAbstract && f.Rhs == null && !Compiler.InitializerIsKnown(f.Type) && !f.IsExtern(out _, out _)) {
                  reporter.Error(MessageSource.Resolver, f.tok, "static non-ghost const field '{0}' of type '{1}' (which does not have a default compiled value) must give a defining value",
                    f.Name, f.Type);
                }
              }
            }
            continue;
          }
          var hasConstructor = false;
          Field fieldWithoutKnownInitializer = null;
          foreach (var member in cl.Members) {
            if (member is Constructor) {
              hasConstructor = true;
              var constructor = (Constructor)member;
              if (constructor.BodyInit != null) {
                cdci.CheckInit(constructor.BodyInit);
              }
            } else if (member is ConstantField && member.IsStatic && !member.IsGhost) {
              var f = (ConstantField)member;
              if (!cl.Module.IsAbstract && f.Rhs == null && !Compiler.InitializerIsKnown(f.Type) && !f.IsExtern(out _, out _)) {
                reporter.Error(MessageSource.Resolver, f.tok, "static non-ghost const field '{0}' of type '{1}' (which does not have a default compiled value) must give a defining value",
                  f.Name, f.Type);
              }
            } else if (member is Field && !member.IsGhost && fieldWithoutKnownInitializer == null) {
              var f = (Field)member;
              if (f is ConstantField && ((ConstantField)f).Rhs != null) {
                // fine
              } else if (!Compiler.InitializerIsKnown(f.Type)) {
                fieldWithoutKnownInitializer = f;
              }
            }
          }
          if (!hasConstructor) {
            if (fieldWithoutKnownInitializer == null) {
              // time to check inherited members
              foreach (var member in cl.InheritedMembers) {
                if (member is Field && !member.IsGhost) {
                  var f = (Field)member;
                  if (f is ConstantField && ((ConstantField)f).Rhs != null) {
                    // fine
                  } else if (!Compiler.InitializerIsKnown(f.Type)) {
                    fieldWithoutKnownInitializer = f;
                    break;
                  }
                }
              }
            }
            // go through inherited members...
            if (fieldWithoutKnownInitializer != null) {
              reporter.Error(MessageSource.Resolver, cl.tok, "class '{0}' with fields without known initializers, like '{1}' of type '{2}', must declare a constructor",
                cl.Name, fieldWithoutKnownInitializer.Name, fieldWithoutKnownInitializer.Type);
            }
          }
        }
      }
    }

    private void ResolveClassMembers_Pass1(TopLevelDeclWithMembers cl) {
      foreach (var member in cl.Members) {
        var prevErrCnt = reporter.Count(ErrorLevel.Error);
        CheckTypeInference_Member(member);
        if (prevErrCnt == reporter.Count(ErrorLevel.Error)) {
          if (member is Method) {
            var m = (Method)member;
            if (m.Body != null) {
              ComputeGhostInterest(m.Body, m.IsGhost, m);
              CheckExpression(m.Body, this, m);
              DetermineTailRecursion(m);
            }
          } else if (member is Function) {
            var f = (Function)member;
            if (!f.IsGhost && f.Body != null) {
              CheckIsCompilable(f.Body);
            }
            DetermineTailRecursion(f);
          }
          if (prevErrCnt == reporter.Count(ErrorLevel.Error) && member is ICodeContext) {
            member.SubExpressions.Iter(e => CheckExpression(e, this, (ICodeContext)member));
          }
        }
      }
    }

    private void CheckDestructsAreAbstemiousCompliant(Expression expr) {
      Contract.Assert(expr != null);
      expr = expr.Resolved;
      if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member.EnclosingClass is CoDatatypeDecl) {
          var ide = Expression.StripParens(e.Obj).Resolved as IdentifierExpr;
          if (ide != null && ide.Var is Formal) {
            // cool
          } else {
            reporter.Error(MessageSource.Resolver, expr, "an abstemious function is allowed to invoke a codatatype destructor only on its parameters");
          }
          return;
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        if (e.Source.Type.IsCoDatatype) {
          var ide = Expression.StripParens(e.Source).Resolved as IdentifierExpr;
          if (ide != null && ide.Var is Formal) {
            // cool; fall through to check match branches
          } else {
            reporter.Error(MessageSource.Resolver, e.Source, "an abstemious function is allowed to codatatype-match only on its parameters");
            return;
          }
        }
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) {
          if (e.E0.Type.IsCoDatatype) {
            reporter.Error(MessageSource.Resolver, expr, "an abstemious function is not only allowed to check codatatype equality");
            return;
          }
        }
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        // ignore the statement part
        CheckDestructsAreAbstemiousCompliant(e.E);
        return;
      }
      expr.SubExpressions.Iter(CheckDestructsAreAbstemiousCompliant);
    }

    /// <summary>
    /// Add edges to the callgraph.
    /// </summary>
    private void AddTypeDependencyEdges(ICodeContext context, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      var caller = context as ICallable;
      if (caller != null && type is NonProxyType) {
        type.ForeachTypeComponent(ty => {
          var udt = ty as UserDefinedType;
          var cl = udt == null ? null : udt.ResolvedClass as ICallable;
          if (cl != null) {
            caller.EnclosingModule.CallGraph.AddEdge(caller, cl);
          }
        });
      }
    }

    private void FigureOutNativeType(NewtypeDecl dd) {
      Contract.Requires(dd != null);
      bool? boolNativeType = null;
      NativeType stringNativeType = null;
      object nativeTypeAttr = true;
      bool hasNativeTypeAttr = Attributes.ContainsMatchingValue(dd.Attributes, "nativeType", ref nativeTypeAttr,
        new Attributes.MatchingValueOption[] {
                Attributes.MatchingValueOption.Empty,
                Attributes.MatchingValueOption.Bool,
                Attributes.MatchingValueOption.String },
        err => reporter.Error(MessageSource.Resolver, dd, err));
      if (hasNativeTypeAttr) {
        if (nativeTypeAttr is bool) {
          boolNativeType = (bool)nativeTypeAttr;
        } else {
          var keyString = (string)nativeTypeAttr;
          foreach (var nativeT in NativeTypes) {
            if (nativeT.Name == keyString) {
              if ((nativeT.CompilationTargets & DafnyOptions.O.CompileTarget) == 0) {
                reporter.Error(MessageSource.Resolver, dd, "nativeType '{0}' not supported on the current compilation target", keyString);
              } else {
                stringNativeType = nativeT;
              }
              break;
            }
          }
          if (stringNativeType == null) {
            reporter.Error(MessageSource.Resolver, dd, "nativeType '{0}' not known", keyString);
          }
        }
      }
      // Figure out the variable and constraint.  Usually, these would be just .Var and .Constraint, but
      // in the case .Var is null, these can be computed from the .BaseType recursively.
      var ddVar = dd.Var;
      var ddConstraint = dd.Constraint;
      for (var ddWhereConstraintsAre = dd; ddVar == null;) {
        ddWhereConstraintsAre = ddWhereConstraintsAre.BaseType.AsNewtype;
        if (ddWhereConstraintsAre == null) {
          break;
        }
        ddVar = ddWhereConstraintsAre.Var;
        ddConstraint = ddWhereConstraintsAre.Constraint;
      }
      if (stringNativeType != null || boolNativeType == true) {
        if (!dd.BaseType.IsNumericBased(Type.NumericPersuation.Int)) {
          reporter.Error(MessageSource.Resolver, dd, "nativeType can only be used on integral types");
        }
        if (ddVar == null) {
          reporter.Error(MessageSource.Resolver, dd, "nativeType can only be used if newtype specifies a constraint");
        }
      }
      if (ddVar != null) {
        Func<Expression, BigInteger?> GetConst = null;
        GetConst = (Expression e) => {
          int m = 1;
          BinaryExpr bin = e as BinaryExpr;
          if (bin != null && bin.Op == BinaryExpr.Opcode.Sub && GetConst(bin.E0) == BigInteger.Zero) {
            m = -1;
            e = bin.E1;
          }
          LiteralExpr l = e as LiteralExpr;
          if (l != null && l.Value is BigInteger) {
            return m * (BigInteger)l.Value;
          }
          return null;
        };
        var bounds = DiscoverAllBounds_SingleVar(ddVar, ddConstraint);
        List<NativeType> potentialNativeTypes =
          (stringNativeType != null) ? new List<NativeType> { stringNativeType } :
          (boolNativeType == false) ? new List<NativeType>() :
          NativeTypes.Where(nt => (nt.CompilationTargets & DafnyOptions.O.CompileTarget) != 0).ToList();
        foreach (var nt in potentialNativeTypes) {
          bool lowerOk = false;
          bool upperOk = false;
          foreach (var bound in bounds) {
            if (bound is ComprehensionExpr.IntBoundedPool) {
              var bnd = (ComprehensionExpr.IntBoundedPool)bound;
              if (bnd.LowerBound != null) {
                BigInteger? lower = GetConst(bnd.LowerBound);
                if (lower != null && nt.LowerBound <= lower) {
                  lowerOk = true;
                }
              }
              if (bnd.UpperBound != null) {
                BigInteger? upper = GetConst(bnd.UpperBound);
                if (upper != null && upper <= nt.UpperBound) {
                  upperOk = true;
                }
              }
            }
          }
          if (lowerOk && upperOk) {
            dd.NativeType = nt;
            break;
          }
        }
        if (dd.NativeType == null && (boolNativeType == true || stringNativeType != null)) {
          reporter.Error(MessageSource.Resolver, dd, "Dafny's heuristics cannot find a compatible native type.  " +
            "Hint: try writing a newtype constraint of the form 'i:int | lowerBound <= i < upperBound && (...any additional constraints...)'");
        }
        if (dd.NativeType != null && stringNativeType == null) {
          reporter.Info(MessageSource.Resolver, dd.tok, "{:nativeType \"" + dd.NativeType.Name + "\"}");
        }
      }
    }

    TypeProxy NewIntegerBasedProxy(IToken tok) {
      Contract.Requires(tok != null);
      var proxy = new InferredTypeProxy();
      ConstrainSubtypeRelation(new IntVarietiesSupertype(), proxy, tok, "integer literal used as if it had type {0}", proxy);
      return proxy;
    }

    private bool ConstrainSubtypeRelation(Type super, Type sub, Expression exprForToken, string msg, params object[] msgArgs) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(exprForToken != null);
      Contract.Requires(msg != null);
      Contract.Requires(msgArgs != null);
      return ConstrainSubtypeRelation(super, sub, exprForToken.tok, msg, msgArgs);
    }
    private void ConstrainTypeExprBool(Expression e, string msg) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);  // expected to have a {0} part
      ConstrainSubtypeRelation(Type.Bool, e.Type, e, msg, e.Type);
    }
    private bool ConstrainSubtypeRelation(Type super, Type sub, IToken tok, string msg, params object[] msgArgs) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(msgArgs != null);
      return ConstrainSubtypeRelation(super, sub, new TypeConstraint.ErrorMsgWithToken(tok, msg, msgArgs));
    }

    private void ConstrainAssignable(NonProxyType lhs, Type rhs, TypeConstraint.ErrorMsg errMsg, out bool moreXConstraints, bool allowDecisions) {
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsg != null);

      bool isRoot, isLeaf, headIsRoot, headIsLeaf;
      CheckEnds(lhs, out isRoot, out isLeaf, out headIsRoot, out headIsLeaf);
      if (isRoot) {
        ConstrainSubtypeRelation(lhs, rhs, errMsg, true, allowDecisions);
        moreXConstraints = false;
      } else {
        var lhsWithProxyArgs = Type.HeadWithProxyArgs(lhs);
        ConstrainSubtypeRelation(lhsWithProxyArgs, rhs, errMsg, false, allowDecisions);
        ConstrainAssignableTypeArgs(lhs, lhsWithProxyArgs.TypeArgs, lhs.TypeArgs, errMsg, out moreXConstraints);
      }
    }

    private void ConstrainAssignableTypeArgs(Type typeHead, List<Type> A, List<Type> B, TypeConstraint.ErrorMsg errMsg, out bool moreXConstraints) {
      Contract.Requires(typeHead != null);
      Contract.Requires(A != null);
      Contract.Requires(B != null);
      Contract.Requires(A.Count == B.Count);
      Contract.Requires(errMsg != null);

      var tok = errMsg.Tok;
      if (B.Count == 0) {
        // all done
        moreXConstraints = false;
      } else if (typeHead is MapType) {
        var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter 0 expects {1} <: {0}", A[0], B[0]);
        AddAssignableConstraint(tok, A[0], B[0], em);
        em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter 1 expects {1} <: {0}", A[1], B[1]);
        AddAssignableConstraint(tok, A[1], B[1], em);
        moreXConstraints = true;
      } else if (typeHead is CollectionType) {
        var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter expects {1} <: {0}", A[0], B[0]);
        AddAssignableConstraint(tok, A[0], B[0], em);
        moreXConstraints = true;
      } else {
        var udt = (UserDefinedType)typeHead;  // note, collections, maps, and user-defined types are the only one with TypeArgs.Count != 0
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        Contract.Assert(cl.TypeArgs.Count == B.Count);
        moreXConstraints = false;
        for (int i = 0; i < B.Count; i++) {
          var msgFormat = "variance for type parameter" + (B.Count == 1 ? "" : "" + i) + " expects {1} <: {0}";
          if (cl.TypeArgs[i].Variance == TypeParameter.TPVariance.Co) {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "co" + msgFormat, A[i], B[i]);
            AddAssignableConstraint(tok, A[i], B[i], em);
            moreXConstraints = true;
          } else if (cl.TypeArgs[i].Variance == TypeParameter.TPVariance.Contra) {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "contra" + msgFormat, B[i], A[i]);
            AddAssignableConstraint(tok, B[i], A[i], em);
            moreXConstraints = true;
          } else {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "non" + msgFormat, A[i], B[i]);
            ConstrainSubtypeRelation_Equal(A[i], B[i], em);
          }
        }
      }
    }

    /// <summary>
    /// Adds the subtyping constraint that "a" and "b" are the same type.
    /// </summary>
    private void ConstrainSubtypeRelation_Equal(Type a, Type b, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(errMsg != null);

      var proxy = a.Normalize() as TypeProxy;
      if (proxy != null && proxy.T == null && !Reaches(b, proxy, 1, new HashSet<TypeProxy>())) {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: (invariance) assigning proxy {0}.T := {1}", proxy, b);
        }
        proxy.T = b;
      }
      proxy = b.Normalize() as TypeProxy;
      if (proxy != null && proxy.T == null && !Reaches(a, proxy, 1, new HashSet<TypeProxy>())) {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: (invariance) assigning proxy {0}.T := {1}", proxy, a);
        }
        proxy.T = a;
      }

      ConstrainSubtypeRelation(a, b, errMsg, true);
      ConstrainSubtypeRelation(b, a, errMsg, true);
    }

    /// <summary>
    /// Adds the subtyping constraint that "sub" is a subtype of "super".
    /// If this constraint seems feasible, returns "true".  Otherwise, prints error message (either "errMsg" or something
    /// more specific) and returns "false".
    /// Note, if in doubt, this method can return "true", because the constraints will be checked for sure at a later stage.
    /// </summary>
    private bool ConstrainSubtypeRelation(Type super, Type sub, TypeConstraint.ErrorMsg errMsg, bool keepConstraints = false, bool allowDecisions = false) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(errMsg != null);

      if (!keepConstraints && super is InferredTypeProxy) {
        var ip = (InferredTypeProxy)super;
        if (ip.KeepConstraints) {
          keepConstraints = true;
        }
      }
      if (!keepConstraints && sub is InferredTypeProxy) {
        var ip = (InferredTypeProxy)sub;
        if (ip.KeepConstraints) {
          keepConstraints = true;
        }
      }

      super = super.NormalizeExpand(keepConstraints);
      sub = sub.NormalizeExpand(keepConstraints);
      var c = new TypeConstraint(super, sub, errMsg, keepConstraints);
      AllTypeConstraints.Add(c);
      return ConstrainSubtypeRelation_Aux(super, sub, c, keepConstraints, allowDecisions);
    }
    private bool ConstrainSubtypeRelation_Aux(Type super, Type sub, TypeConstraint c, bool keepConstraints, bool allowDecisions) {
      Contract.Requires(sub != null);
      Contract.Requires(!(sub is TypeProxy) || ((TypeProxy)sub).T == null);  // caller is expected to have Normalized away proxies
      Contract.Requires(super != null);
      Contract.Requires(!(super is TypeProxy) || ((TypeProxy)super).T == null);  // caller is expected to have Normalized away proxies
      Contract.Requires(c != null);

      if (object.ReferenceEquals(super, sub)) {
        return true;
      } else if (super is TypeProxy && sub is TypeProxy) {
        // both are proxies
        ((TypeProxy)sub).AddSupertype(c);
        ((TypeProxy)super).AddSubtype(c);
        return true;
      } else if (sub is TypeProxy) {
        var proxy = (TypeProxy)sub;
        proxy.AddSupertype(c);
        AssignKnownEnd(proxy, keepConstraints, allowDecisions);
        return true;
      } else if (super is TypeProxy) {
        var proxy = (TypeProxy)super;
        proxy.AddSubtype(c);
        AssignKnownEnd(proxy, keepConstraints, allowDecisions);
        return true;
      } else {
        // two non-proxy types
        // set "headSymbolsAgree" to "false" if it's clear the head symbols couldn't be the same; "true" means they may be the same
        bool headSymbolsAgree = Type.IsHeadSupertypeOf(super.NormalizeExpand(keepConstraints), sub);
        if (!headSymbolsAgree) {
          c.FlagAsError();
          return false;
        }
        // TODO: inspect type parameters in order to produce some error messages sooner
        return true;
      }
    }

    /// <summary>
    /// "root" says that the type is a non-artificial type with no proper supertypes.
    /// "leaf" says that the only possible proper subtypes are subset types of the type. Thus, the only
    /// types that are not leaf types are traits and artificial types.
    /// The "headIs" versions speak only about the head symbols, so it is possible that the given
    /// type arguments would change the root/leaf status of the entire type.
    /// </summary>
    void CheckEnds(Type t, out bool isRoot, out bool isLeaf, out bool headIsRoot, out bool headIsLeaf) {
      Contract.Requires(t != null);
      Contract.Ensures(!Contract.ValueAtReturn(out isRoot) || Contract.ValueAtReturn(out headIsRoot)); // isRoot ==> headIsRoot
      Contract.Ensures(!Contract.ValueAtReturn(out isLeaf) || Contract.ValueAtReturn(out headIsLeaf)); // isLeaf ==> headIsLeaf
      t = t.NormalizeExpandKeepConstraints();
      if (t.IsBoolType || t.IsCharType || t.IsIntegerType || t.IsRealType || t.AsNewtype != null || t.IsBitVectorType || t.IsBigOrdinalType) {
        isRoot = true; isLeaf = true;
        headIsRoot = true; headIsLeaf = true;
      } else if (t is ArtificialType) {
        isRoot = false; isLeaf = false;
        headIsRoot = false; headIsLeaf = false;
      } else if (t.IsObjectQ) {
        isRoot = true; isLeaf = false;
        headIsRoot = true; headIsLeaf = false;
      } else if (t is ArrowType) {
        var arr = (ArrowType)t;
        headIsRoot = true; headIsLeaf = true;  // these are definitely true
        isRoot = true; isLeaf = true;  // set these to true until proven otherwise
        Contract.Assert(arr.Arity + 1 == arr.TypeArgs.Count);
        for (int i = 0; i < arr.TypeArgs.Count; i++) {
          var arg = arr.TypeArgs[i];
          bool r, l, hr, hl;
          CheckEnds(arg, out r, out l, out hr, out hl);
          if (i < arr.Arity) {
            isRoot &= l; isLeaf &= r;  // argument types are contravariant
          } else {
            isRoot &= r; isLeaf &= l;  // result type is covariant
          }
        }
      } else if (t is UserDefinedType) {
        var udt = (UserDefinedType)t;
        var cl = udt.ResolvedClass;
        if (cl != null) {
          if (cl is SubsetTypeDecl) {
            headIsRoot = false; headIsLeaf = true;
          } else if (cl is TraitDecl) {
            headIsRoot = false; headIsLeaf = false;
          } else if (cl is ClassDecl) {
            headIsRoot = false; headIsLeaf = true;
          } else if (cl is OpaqueTypeDecl) {
            headIsRoot = true; headIsLeaf = true;
          } else if (cl is InternalTypeSynonymDecl) {
            Contract.Assert(object.ReferenceEquals(t, t.NormalizeExpand())); // should be opaque in scope
            headIsRoot = true; headIsLeaf = true;
          } else {
            Contract.Assert(cl is DatatypeDecl);
            headIsRoot = true; headIsLeaf = true;
          }
          // for "isRoot" and "isLeaf", also take into consideration the root/leaf status of type arguments
          isRoot = headIsRoot; isLeaf = headIsLeaf;
          Contract.Assert(udt.TypeArgs.Count == cl.TypeArgs.Count);
          for (int i = 0; i < udt.TypeArgs.Count; i++) {
            var variance = cl.TypeArgs[i].Variance;
            if (variance != TypeParameter.TPVariance.Non) {
              bool r, l, hr, hl;
              CheckEnds(udt.TypeArgs[i], out r, out l, out hr, out hl);
              if (variance == TypeParameter.TPVariance.Co) {
                isRoot &= r; isLeaf &= l;
              } else {
                isRoot &= l; isLeaf &= r;
              }
            }
          }
        } else if (t.IsTypeParameter) {
          var tp = udt.AsTypeParameter;
          Contract.Assert(tp != null);
          isRoot = true; isLeaf = true;  // all type parameters are invariant
          headIsRoot = true; headIsLeaf = true;
        } else {
          isRoot = false; isLeaf = false;  // don't know
          headIsRoot = false; headIsLeaf = false;
        }
      } else if (t is MapType) {  // map, imap
        Contract.Assert(t.TypeArgs.Count == 2);
        bool r0, l0, r1, l1, hr, hl;
        CheckEnds(t.TypeArgs[0], out r0, out l0, out hr, out hl);
        CheckEnds(t.TypeArgs[1], out r1, out l1, out hr, out hl);
        isRoot = r0 & r1; isLeaf = r0 & r1;  // map types are covariant in both type arguments
        headIsRoot = true; headIsLeaf = true;
      } else if (t is CollectionType) {  // set, iset, multiset, seq
        Contract.Assert(t.TypeArgs.Count == 1);
        bool hr, hl;
        CheckEnds(t.TypeArgs[0], out isRoot, out isLeaf, out hr, out hl);  // type is covariant is type argument
        headIsRoot = true; headIsLeaf = true;
      } else {
        isRoot = false; isLeaf = false;  // don't know
        headIsRoot = false; headIsLeaf = false;
      }
    }

    int _recursionDepth = 0;
    private bool AssignProxyAndHandleItsConstraints(TypeProxy proxy, Type t, bool keepConstraints = false) {
      Contract.Requires(proxy != null);
      Contract.Requires(proxy.T == null);
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy));
      Contract.Requires(!(t is ArtificialType));
      if (_recursionDepth == 20) {
        Contract.Assume(false);  // possible infinite recursion
      }
      _recursionDepth++;
      var b = AssignProxyAndHandleItsConstraints_aux(proxy, t, keepConstraints);
      _recursionDepth--;
      return b;
    }
    /// <summary>
    /// This method is called if "proxy" is an unassigned proxy and "t" is a type whose head symbol is known.
    /// It always sets "proxy.T" to "t".
    /// Then, it deals with the constraints of "proxy" as follows:
    /// * If the constraint compares "t" with a non-proxy with a head comparable with that of "t",
    ///   then add constraints that the type arguments satisfy the desired subtyping constraint
    /// * If the constraint compares "t" with a non-proxy with a head not comparable with that of "t",
    ///   then report an error
    /// * If the constraint compares "t" with a proxy, then (depending on the constraint and "t") attempt
    ///   to recursively set it
    /// After this process, the proxy's .Supertypes and .Subtypes lists of constraints are no longer needed.
    /// If anything is found to be infeasible, "false" is returned (and the propagation may be interrupted);
    /// otherwise, "true" is returned.
    /// </summary>
    private bool AssignProxyAndHandleItsConstraints_aux(TypeProxy proxy, Type t, bool keepConstraints = false) {
      Contract.Requires(proxy != null);
      Contract.Requires(proxy.T == null);
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy));
      Contract.Requires(!(t is ArtificialType));

      t = keepConstraints ? t.NormalizeExpandKeepConstraints() : t.NormalizeExpand();
      // never violate the type constraint of a literal expression
      var followedRequestedAssignment = true;
      foreach (var su in proxy.Supertypes) {
        if (su is IntVarietiesSupertype) {
          var fam = TypeProxy.GetFamily(t);
          if (fam == TypeProxy.Family.IntLike || fam == TypeProxy.Family.BitVector || fam == TypeProxy.Family.Ordinal) {
            // good, let's continue with the request to equate the proxy with t
            // unless...
            if (t != t.NormalizeExpand()) {
              // force the type to be a base type
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, t.NormalizeExpand());
              }
              t = t.NormalizeExpand();
              followedRequestedAssignment = false;
            }
          } else {
            // hijack the setting of proxy; to do that, we decide on a particular int variety now
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, Type.Int);
            }
            t = Type.Int;
            followedRequestedAssignment = false;
          }
          break;
        } else if (su is RealVarietiesSupertype) {
          if (TypeProxy.GetFamily(t) == TypeProxy.Family.RealLike) {
            // good, let's continue with the request to equate the proxy with t
            // unless...
            if (t != t.NormalizeExpand()) {
              // force the type to be a base type
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, t.NormalizeExpand());
              }
              t = t.NormalizeExpand();
              followedRequestedAssignment = false;
            }
          } else {
            // hijack the setting of proxy; to do that, we decide on a particular real variety now
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, Type.Real);
            }
            t = Type.Real;
            followedRequestedAssignment = false;
          }
          break;
        }
      }
      // set proxy.T right away, so that we can freely recurse without having to worry about infinite recursion
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: setting proxy {0}.T := {1}", proxy, t, Type.Real);
      }
      proxy.T = t;

      // check feasibility
      bool isRoot, isLeaf, headRoot, headLeaf;
      CheckEnds(t, out isRoot, out isLeaf, out headRoot, out headLeaf);
      // propagate up
      foreach (var c in proxy.SupertypeConstraints) {
        var u = keepConstraints ? c.Super.NormalizeExpandKeepConstraints() : c.Super.NormalizeExpand();
        if (!(u is TypeProxy)) {
          ImposeSubtypingConstraint(u, t, c.errorMsg);
        } else if (isRoot) {
          // If t is a root, we might as well constrain u now.  Otherwise, we'll wait until the .Subtype constraint of u is dealt with.
          AssignProxyAndHandleItsConstraints((TypeProxy)u, t, keepConstraints);
        }
      }
      // propagate down
      foreach (var c in proxy.SubtypeConstraints) {
        var u = keepConstraints ? c.Sub.NormalizeExpandKeepConstraints() : c.Sub.NormalizeExpand();
        Contract.Assert(!TypeProxy.IsSupertypeOfLiteral(u));  // these should only appear among .Supertypes
        if (!(u is TypeProxy)) {
          ImposeSubtypingConstraint(t, u, c.errorMsg);
        } else if (isLeaf) {
          // If t is a leaf (no pun intended), we might as well constrain u now.  Otherwise, we'll wait until the .Supertype constraint of u is dealt with.
          AssignProxyAndHandleItsConstraints((TypeProxy)u, t, keepConstraints);
        }
      }

      return followedRequestedAssignment;
    }

    /// <summary>
    /// Impose constraints that "sub" is a subtype of "super", returning "false" if this leads to an overconstrained situation.
    /// In most cases, "sub" being a subtype of "super" means that "sub" and "super" have the same head symbol and, therefore, the
    /// same number of type arguments. Depending on the polarities of the type parameters, the corresponding arguments
    /// of "sub" and "super" must be in co-, in-, or contra-variant relationships to each other.
    /// There are two ways "sub" can be a subtype of "super" without the two having the same head symbol.
    /// One way is that "sub" is a subset type. In this case, the method starts by moving "sub" up toward "super".
    /// The other way is that "super" is a trait (possibly
    /// the trait "object").  By a current restriction in Dafny's type system, traits have no type parameters, so in this case, it
    /// suffices to check that the head symbol of "super" is something that derives from "sub".
    /// </summary>
    private bool ImposeSubtypingConstraint(Type super, Type sub, TypeConstraint.ErrorMsg errorMsg) {
      Contract.Requires(super != null && !(super is TypeProxy));
      Contract.Requires(sub != null && !(sub is TypeProxy));
      Contract.Requires(errorMsg != null);
      List<int> polarities = ConstrainTypeHead_ModuloSubsetTypeParents(super, ref sub);
      if (polarities == null) {
        errorMsg.FlagAsError();
        return false;
      }
      bool keepConstraints = KeepConstraints(super, sub);
      var p = polarities.Count;
      Contract.Assert(p == super.TypeArgs.Count);  // postcondition of ConstrainTypeHead
      Contract.Assert(p == 0 || sub.TypeArgs.Count == super.TypeArgs.Count);  // postcondition of ConstrainTypeHead
      for (int i = 0; i < p; i++) {
        var pol = polarities[i];
        var tp = p == 1 ? "" : " " + i;
        var errMsg = new TypeConstraint.ErrorMsgWithBase(errorMsg,
          pol < 0 ? "contravariant type parameter{0} would require {1} <: {2}" :
          pol > 0 ? "covariant type parameter{0} would require {2} <: {1}" :
          "invariant type parameter{0} would require {1} = {2}",
          tp, super.TypeArgs[i], sub.TypeArgs[i]);
        if (pol >= 0) {
          if (!ConstrainSubtypeRelation(super.TypeArgs[i], sub.TypeArgs[i], errMsg, keepConstraints)) {
            return false;
          }
        }
        if (pol <= 0) {
          if (!ConstrainSubtypeRelation(sub.TypeArgs[i], super.TypeArgs[i], errMsg, keepConstraints)) {
            return false;
          }
        }
      }
      return true;
    }

    /// <summary>
    /// This is a more liberal version of "ConstrainTypeHead" below. It is willing to move "sub"
    /// upward toward its subset-type parents until it finds a head that matches "super", if any.
    /// </summary>
    private List<int> ConstrainTypeHead_ModuloSubsetTypeParents(Type super, ref Type sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);

      // Before we do anything else, make a note of whether or not both "a" and "b" are non-null types.
      var abNonNullTypes = super.IsNonNullRefType && sub.IsNonNullRefType;

      super = super.NormalizeExpandKeepConstraints();
      var X = sub.NormalizeExpandKeepConstraints();
      UserDefinedType prevX = null;
      while (true) {
        var polarities = ConstrainTypeHead(super, X);
        if (polarities != null) {
          sub = X;
          return polarities;
        }
        var udt = X as UserDefinedType;
        if (udt != null && udt.ResolvedClass is SubsetTypeDecl) {
          var sst = (SubsetTypeDecl)udt.ResolvedClass;
          prevX = udt;
          X = sst.RhsWithArgument(udt.TypeArgs).NormalizeExpandKeepConstraints();
        } else {
          // There is one more thing to check.  If we started with two non-null types, then we
          // have just moved X down from "sub" to the base-most type and prevX is the non-null
          // version of X.  If "super" is exactly a non-null type, then the head of "sub" is a
          // subtype of the head of "super" if the head of "sub.parent" is a subtype of the head
          // of "super.parent".  And since the type parameters of a possibly null type are the
          // same as those for the corresponding non-null type, we can just answer our question
          // by asking it for prevX and super.parent.
          if (abNonNullTypes) {
            Contract.Assert(prevX != null && prevX.ResolvedClass is NonNullTypeDecl);
            var udtSuper = super as UserDefinedType;
            if (udtSuper != null && udtSuper.ResolvedClass is NonNullTypeDecl) {
              var nnt = (NonNullTypeDecl)udtSuper.ResolvedClass;
              super = nnt.RhsWithArgument(udtSuper.TypeArgs);
              polarities = ConstrainTypeHead(super, X);
              if (polarities != null) {
                sub = prevX;
                return polarities;
              }
            }
          }
          return null;
        }
      }
    }

    /// <summary>
    /// Determines if the head of "sub" can be a subtype of "super".
    /// If this is not possible, null is returned.
    /// If it is possible, return a list of polarities, one for each type argument of "sub".  Polarities
    /// indicate:
    ///     +1  co-variant
    ///      0  invariant
    ///     -1  contra-variant
    /// "sub" is of some type that can (in general) have type parameters.
    /// See also note about Dafny's current type system in the description of method "ImposeSubtypingConstraint".
    /// </summary>
    private List<int> ConstrainTypeHead(Type super, Type sub) {
      Contract.Requires(super != null && !(super is TypeProxy));
      Contract.Requires(sub != null && !(sub is TypeProxy));
      if (super is IntVarietiesSupertype) {
        var famSub = TypeProxy.GetFamily(sub);
        if (famSub == TypeProxy.Family.IntLike || famSub == TypeProxy.Family.BitVector || famSub == TypeProxy.Family.Ordinal || super.Equals(sub)) {
          return new List<int>();
        } else {
          return null;
        }
      } else if (super is RealVarietiesSupertype) {
        if (TypeProxy.GetFamily(sub) == TypeProxy.Family.RealLike || super.Equals(sub)) {
          return new List<int>();
        } else {
          return null;
        }
      }
      switch (TypeProxy.GetFamily(super)) {
        case TypeProxy.Family.Bool:
        case TypeProxy.Family.Char:
        case TypeProxy.Family.IntLike:
        case TypeProxy.Family.RealLike:
        case TypeProxy.Family.Ordinal:
        case TypeProxy.Family.BitVector:
          if (super.Equals(sub)) {
            return new List<int>();
          } else {
            return null;
          }
        case TypeProxy.Family.ValueType:
        case TypeProxy.Family.Ref:
        case TypeProxy.Family.Opaque:
          break;  // more elaborate work below
        case TypeProxy.Family.Unknown:
        default:  // just in case the family is mentioned explicitly as one of the cases
          Contract.Assert(false);  // unexpected type (the precondition of ConstrainTypeHead says "no proxies")
          return null;  // please compiler
      }
      if (super is SetType) {
        var tt = (SetType)super;
        var uu = sub as SetType;
        return uu != null && tt.Finite == uu.Finite ? new List<int> { 1 } : null;
      } else if (super is SeqType) {
        return sub is SeqType ? new List<int> { 1 } : null;
      } else if (super is MultiSetType) {
        return sub is MultiSetType ? new List<int> { 1 } : null;
      } else if (super is MapType) {
        var tt = (MapType)super;
        var uu = sub as MapType;
        return uu != null && tt.Finite == uu.Finite ? new List<int> { 1, 1 } : null;
      } else if (super.IsObjectQ) {
        return sub.IsRefType ? new List<int>() : null;
      } else {
        // The only remaining cases are that "super" is a (co)datatype, opaque type, or non-object trait/class.
        // In each of these cases, "super" is a UserDefinedType.
        var udfSuper = (UserDefinedType)super;
        var clSuper = udfSuper.ResolvedClass;
        if (clSuper == null) {
          Contract.Assert(super.TypeArgs.Count == 0);
          if (super.IsTypeParameter) {
            // we're looking at a type parameter
            return super.AsTypeParameter == sub.AsTypeParameter ? new List<int>() : null;
          } else {
            Contract.Assert(super.IsInternalTypeSynonym);
            return super.AsInternalTypeSynonym == sub.AsInternalTypeSynonym ? new List<int>() : null;
          }
        }
        var udfSub = sub as UserDefinedType;
        var clSub = udfSub == null ? null : udfSub.ResolvedClass;
        if (clSub == null) {
          return null;
        } else if (clSuper == clSub) {
          // good
          var polarities = new List<int>();
          Contract.Assert(clSuper.TypeArgs.Count == udfSuper.TypeArgs.Count);
          Contract.Assert(clSuper.TypeArgs.Count == udfSub.TypeArgs.Count);
          foreach (var tp in clSuper.TypeArgs) {
            var polarity =
              tp.Variance == TypeParameter.TPVariance.Co ? 1 :
              tp.Variance == TypeParameter.TPVariance.Contra ? -1 : 0;
            polarities.Add(polarity);
          }
          return polarities;
        } else if (clSub is ClassDecl && ((ClassDecl)clSub).DerivesFrom(clSuper)) {
          // cool
          Contract.Assert(clSuper.TypeArgs.Count == 0);  // traits are currently not allowed to have any type parameters
          return new List<int>();
        } else {
          return null;
        }
      }
    }
    private bool KeepConstraints(Type super, Type sub) {
      Contract.Requires(super != null && !(super is TypeProxy));
      Contract.Requires(sub != null && !(sub is TypeProxy));
      if (super is IntVarietiesSupertype) {
        return false;
      } else if (super is RealVarietiesSupertype) {
        return false;
      }
      switch (TypeProxy.GetFamily(super)) {
        case TypeProxy.Family.Bool:
        case TypeProxy.Family.Char:
        case TypeProxy.Family.IntLike:
        case TypeProxy.Family.RealLike:
        case TypeProxy.Family.Ordinal:
        case TypeProxy.Family.BitVector:
          return false;
        case TypeProxy.Family.ValueType:
        case TypeProxy.Family.Ref:
        case TypeProxy.Family.Opaque:
          break;  // more elaborate work below
        case TypeProxy.Family.Unknown:
          return false;
      }
      if (super is SetType || super is SeqType || super is MultiSetType || super is MapType) {
        return true;
      } else if (super is ArrowType) {
        return false;
      } else if (super.IsObjectQ) {
        return false;
      } else {
        // super is UserDefinedType
        return true;
      }
    }

    public List<TypeConstraint> AllTypeConstraints = new List<TypeConstraint>();
    public List<XConstraint> AllXConstraints = new List<XConstraint>();

    public class XConstraint
    {
      public readonly IToken tok;
      public readonly string ConstraintName;
      public readonly Type[] Types;
      public readonly TypeConstraint.ErrorMsg errorMsg;
      public XConstraint(IToken tok, string constraintName, Type[] types, TypeConstraint.ErrorMsg errMsg) {
        Contract.Requires(tok != null);
        Contract.Requires(constraintName != null);
        Contract.Requires(types != null);
        Contract.Requires(errMsg != null);
        this.tok = tok;
        ConstraintName = constraintName;
        Types = types;
        errorMsg = errMsg;
      }

      public override string ToString() {
        var s = ConstraintName + ":";
        foreach (var t in Types) {
          s += " " + t;
        }
        return s;
      }

      /// <summary>
      /// Tries to confirm the XConstraint.
      /// If the XConstraint can be confirmed, or at least is plausible enough to have been converted into other type
      /// constraints or more XConstraints, then "true" is returned and the out-parameters "convertedIntoOtherTypeConstraints"
      /// and "moreXConstraints" are set to true accordingly.
      /// If the XConstraint can be refuted, then an error message will be produced and "true" is returned (to indicate
      /// that this XConstraint has finished serving its purpose).
      /// If there's not enough information to confirm or refute the XConstraint, then "false" is returned.
      /// </summary>
      public bool Confirm(Resolver resolver, bool fullstrength, out bool convertedIntoOtherTypeConstraints, out bool moreXConstraints) {
        Contract.Requires(resolver != null);
        convertedIntoOtherTypeConstraints = false;
        moreXConstraints = false;
        var t = Types[0].NormalizeExpand();
        if (t is TypeProxy) {
          switch (ConstraintName) {
            case "Assignable":
            case "Equatable":
            case "EquatableArg":
            case "Indexable":
            case "Innable":
            case "MultiIndexable":
            case "IntOrORDINAL":
              // have a go downstairs
              break;
            default:
              return false;  // there's not enough information to confirm or refute this XConstraint
          }
        }
        bool satisfied;
        Type tUp, uUp;
        switch (ConstraintName) {
          case "Assignable": {
              Contract.Assert(t == t.Normalize());  // it's already been normalized above
              var u = Types[1].NormalizeExpandKeepConstraints();
              if (CheckTypeInference_Visitor.IsDetermined(t) &&
                (fullstrength
                || !ProxyWithNoSubTypeConstraint(u, resolver)
                || (Types[0].NormalizeExpandKeepConstraints().IsNonNullRefType && u is TypeProxy && resolver.HasApplicableNullableRefTypeConstraint(new HashSet<TypeProxy>() { (TypeProxy)u })))) {
                // This is the best case.  We convert Assignable(t, u) to the subtype constraint base(t) :> u.
                resolver.ConstrainAssignable((NonProxyType)t, u, errorMsg, out moreXConstraints, fullstrength);
                convertedIntoOtherTypeConstraints = true;
                return true;
              } else if (u.IsTypeParameter) {
                // we need the constraint base(t) :> u, which for a type parameter t can happen iff t :> u
                resolver.ConstrainSubtypeRelation(t, u, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              } else if (Type.FromSameHead(t, u, out tUp, out uUp)) {
                resolver.ConstrainAssignableTypeArgs(tUp, tUp.TypeArgs, uUp.TypeArgs, errorMsg, out moreXConstraints);
                return true;
              } else if (fullstrength && t is NonProxyType) {
                // We convert Assignable(t, u) to the subtype constraint base(t) :> u.
                resolver.ConstrainAssignable((NonProxyType)t, u, errorMsg, out moreXConstraints, fullstrength);
                convertedIntoOtherTypeConstraints = true;
                return true;
              } else if (fullstrength && u is NonProxyType) {
                // We're willing to change "base(t) :> u" to the stronger constraint "t :> u" for the sake of making progress.
                resolver.ConstrainSubtypeRelation(t, u, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              // There's not enough information to say anything
              return false;
            }
          case "NumericType":
            satisfied = t.IsNumericBased();
            break;
          case "IntegerType":
            satisfied = t.IsNumericBased(Type.NumericPersuation.Int);
            break;
          case "IsBitvector":
            satisfied = t.IsBitVectorType;
            break;
          case "IsRefType":
            satisfied = t.IsRefType;
            break;
          case "IsNullableRefType":
            satisfied = t.IsRefType && !t.IsNonNullRefType;
            break;
          case "Orderable_Lt":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SeqType || t is SetType || t is MultiSetType;
            break;
          case "Orderable_Gt":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SetType || t is MultiSetType;
            break;
          case "RankOrderable": {
              var u = Types[1].NormalizeExpand();
              if (u is TypeProxy) {
                return false;  // not enough information
              }
              satisfied = (t.IsIndDatatype || t.IsTypeParameter) && u.IsIndDatatype;
              break;
            }
          case "Plussable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SeqType || t is SetType || t is MultiSetType;
            break;
          case "Minusable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SetType || t is MultiSetType;
            break;
          case "Mullable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t is SetType || t is MultiSetType;
            break;
          case "IntOrORDINAL":
            if (!(t is TypeProxy)) {
              if (TernaryExpr.PrefixEqUsesNat) {
                satisfied = t.IsNumericBased(Type.NumericPersuation.Int);
              } else {
                satisfied = t.IsNumericBased(Type.NumericPersuation.Int) || t.IsBigOrdinalType;
              }
            } else if (fullstrength) {
              var proxy = (TypeProxy)t;
              if (TernaryExpr.PrefixEqUsesNat) {
                resolver.AssignProxyAndHandleItsConstraints(proxy, Type.Int);
              } else {
                // let's choose ORDINAL over int
                resolver.AssignProxyAndHandleItsConstraints(proxy, Type.BigOrdinal);
              }
              convertedIntoOtherTypeConstraints = true;
              satisfied = true;
            } else {
              return false;
            }
            break;
          case "NumericOrBitvector":
            satisfied = t.IsNumericBased() || t.IsBitVectorType;
            break;
          case "NumericOrBitvectorOrCharOrORDINAL":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsCharType || t.IsBigOrdinalType;
            break;
          case "IntLikeOrBitvector":
            satisfied = t.IsNumericBased(Type.NumericPersuation.Int) || t.IsBitVectorType;
            break;
          case "BooleanBits":
            satisfied = t.IsBoolType || t.IsBitVectorType;
            break;
          case "Sizeable":
            satisfied = (t is SetType && ((SetType)t).Finite) || t is MultiSetType || t is SeqType || (t is MapType && ((MapType)t).Finite);
            break;
          case "Disjointable":
            satisfied = t is SetType || t is MultiSetType || t is MapType;
            break;
          case "MultiSetConvertible":
            satisfied = (t is SetType && ((SetType)t).Finite) || t is SeqType;
            if (satisfied) {
              Type elementType = ((CollectionType)t).Arg;
              var u = Types[1];  // note, it's okay if "u" is a TypeProxy
              var em = new TypeConstraint.ErrorMsgWithBase(errorMsg, "expecting element type {0} (got {1})", u, elementType);
              resolver.ConstrainSubtypeRelation_Equal(elementType, u, em);
              convertedIntoOtherTypeConstraints = true;
            }
            break;
          case "IsCoDatatype":
            satisfied = t.IsCoDatatype;
            break;
          case "Indexable":
            if (!(t is TypeProxy)) {
              satisfied = t is SeqType || t is MultiSetType || t is MapType || (t.IsArrayType && t.AsArrayType.Dims == 1);
            } else {
              // t is a proxy, but perhaps it stands for something between "object" and "array<?>".  If so, we can add a constraint
              // that it does have the form "array<?>", since "object" would not be Indexable.
              var proxy = (TypeProxy)t;
              Type meet = null;
              if (resolver.MeetOfAllSubtypes(proxy, ref meet, new HashSet<TypeProxy>()) && meet != null) {
                var tt = Type.HeadWithProxyArgs(meet);
                satisfied = tt is SeqType || tt is MultiSetType || tt is MapType || (tt.IsArrayType && tt.AsArrayType.Dims == 1);
                if (satisfied) {
                  resolver.AssignProxyAndHandleItsConstraints(proxy, tt);
                  convertedIntoOtherTypeConstraints = true;
                }
              } else {
                return false;  // we can't determine the answer
              }
            }
            break;
          case "MultiIndexable":
            if (!(t is TypeProxy)) {
              satisfied = t is SeqType || (t.IsArrayType && t.AsArrayType.Dims == 1);
            } else {
              // t is a proxy, but perhaps it stands for something between "object" and "array<?>".  If so, we can add a constraint
              // that it does have the form "array<?>", since "object" would not be Indexable.
              var proxy = (TypeProxy)t;
              Type meet = null;
              if (resolver.MeetOfAllSubtypes(proxy, ref meet, new HashSet<TypeProxy>()) && meet != null) {
                var tt = Type.HeadWithProxyArgs(meet);
                satisfied = tt is SeqType || (tt.IsArrayType && tt.AsArrayType.Dims == 1);
                if (satisfied) {
                  resolver.AssignProxyAndHandleItsConstraints(proxy, tt);
                  convertedIntoOtherTypeConstraints = true;
                }
              } else {
                return false;  // we can't determine the answer
              }
            }
            break;
          case "Innable": {
              var elementType = FindCollectionType(t, true, new HashSet<TypeProxy>()) ?? FindCollectionType(t, false, new HashSet<TypeProxy>());
              if (elementType != null) {
                var u = Types[1];  // note, it's okay if "u" is a TypeProxy
                resolver.AddXConstraint(this.tok, "Equatable", elementType, u, new TypeConstraint.ErrorMsgWithBase(errorMsg, "expecting element type to be assignable to {1} (got {0})", u, elementType));
                moreXConstraints = true;
                return true;
              }
              if (t is TypeProxy) {
                return false;  // not enough information to do anything
              }
              satisfied = false;
              break;
            }
          case "SeqUpdatable": {
              var xcWithExprs = (XConstraintWithExprs)this;
              var index = xcWithExprs.Exprs[0];
              var value = xcWithExprs.Exprs[1];
              if (t is SeqType) {
                var s = (SeqType)t;
                resolver.ConstrainSubtypeRelation(Type.Int, index.Type, index, "sequence update requires integer index (got {0})", index.Type);
                resolver.ConstrainSubtypeRelation(s.Arg, value.Type, value, "sequence update requires the value to have the element type of the sequence (got {0})", value.Type);
              } else if (t is MapType) {
                var s = (MapType)t;
                if (s.Finite) {
                  resolver.ConstrainSubtypeRelation(s.Domain, index.Type, index, "map update requires domain element to be of type {0} (got {1})", s.Domain, index.Type);
                  resolver.ConstrainSubtypeRelation(s.Range, value.Type, value, "map update requires the value to have the range type {0} (got {1})", s.Range, value.Type);
                } else {
                  resolver.ConstrainSubtypeRelation(s.Domain, index.Type, index, "imap update requires domain element to be of type {0} (got {1})", s.Domain, index.Type);
                  resolver.ConstrainSubtypeRelation(s.Range, value.Type, value, "imap update requires the value to have the range type {0} (got {1})", s.Range, value.Type);
                }
              } else if (t is MultiSetType) {
                var s = (MultiSetType)t;
                resolver.ConstrainSubtypeRelation(s.Arg, index.Type, index, "multiset update requires domain element to be of type {0} (got {1})", s.Arg, index.Type);
                resolver.ConstrainToIntegerType(value, "multiset update requires integer-based numeric value (got {0})");
              } else {
                satisfied = false;
                break;
              }
              convertedIntoOtherTypeConstraints = true;
              return true;
            }
          case "ContainerIndex":
            // The semantics of this XConstraint is that *if* the head is seq/array/map/multiset, then its element/domain type must a supertype of "u"
            Type indexType;
            if (t is SeqType) {
              indexType = resolver.NewIntegerBasedProxy(tok);
            } else if (t.IsArrayType) {
              indexType = resolver.NewIntegerBasedProxy(tok);
            } else if (t is MapType) {
              indexType = ((MapType)t).Domain;
            } else if (t is MultiSetType) {
              indexType = ((MultiSetType)t).Arg;
            } else {
              // some other head symbol; that's cool
              return true;
            }
            // note, it's okay if "Types[1]" is a TypeProxy
            resolver.ConstrainSubtypeRelation(indexType, Types[1], errorMsg);  // use the same error message
            convertedIntoOtherTypeConstraints = true;
            return true;
          case "ContainerResult":
            // The semantics of this XConstraint is that *if* the head is seq/array/map/multiset, then the type of a selection must a subtype of "u"
            Type resultType;
            if (t is SeqType) {
              resultType = ((SeqType)t).Arg;
            } else if (t.IsArrayType) {
              resultType = UserDefinedType.ArrayElementType(t);
            } else if (t is MapType) {
              resultType = ((MapType)t).Range;
            } else if (t is MultiSetType) {
              resultType = resolver.builtIns.Nat();
            } else {
              // some other head symbol; that's cool
              return true;
            }
            // note, it's okay if "Types[1]" is a TypeProxy
            resolver.ConstrainSubtypeRelation(Types[1], resultType, errorMsg);
            convertedIntoOtherTypeConstraints = true;
            return true;
          case "Equatable": {
              t = Types[0].NormalizeExpandKeepConstraints();
              var u = Types[1].NormalizeExpandKeepConstraints();
              if (object.ReferenceEquals(t, u)) {
                return true;
              }
              if (t is TypeProxy && u is TypeProxy) {
                return false;  // not enough information to do anything sensible
              } else if (t is TypeProxy || u is TypeProxy) {
                TypeProxy proxy;
                Type other;
                if (t is TypeProxy) {
                  proxy = (TypeProxy)t;
                  other = u;
                } else {
                  proxy = (TypeProxy)u;
                  other = t;
                }
                if (other.IsNumericBased() || other.IsBitVectorType || other.IsBigOrdinalType) {
                  resolver.ConstrainSubtypeRelation(other.NormalizeExpand(), proxy, errorMsg, true);
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else if (fullstrength) {
                  // the following is rather aggressive
                  if (Resolver.TypeConstraintsIncludeProxy(other, proxy)) {
                    return false;
                  } else {
                    if (other.IsRefType && resolver.HasApplicableNullableRefTypeConstraint_SubDirection(proxy)) {
                      other = other.NormalizeExpand();  // shave off all constraints
                    }
                    satisfied = resolver.AssignProxyAndHandleItsConstraints(proxy, other, true);
                    convertedIntoOtherTypeConstraints = true;
                    break;
                  }
                } else {
                  return false;  // not enough information
                }
              }
              Type a,b;
              satisfied = Type.FromSameHead_Subtype(t, u, resolver.builtIns, out a, out b);
              if (satisfied) {
                Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
                var cl = a is UserDefinedType ? ((UserDefinedType)a).ResolvedClass : null;
                for (int i = 0; i < a.TypeArgs.Count; i++) {
                  resolver.AllXConstraints.Add(new XConstraint_EquatableArg(tok,
                    a.TypeArgs[i], b.TypeArgs[i],
                    a is CollectionType || (cl != null && cl.TypeArgs[i].Variance != TypeParameter.TPVariance.Non),
                    a.IsRefType,
                    errorMsg));
                  moreXConstraints = true;
                }
              }
              break;
            }
          case "EquatableArg": {
              t = Types[0].NormalizeExpandKeepConstraints();
              var u = Types[1].NormalizeExpandKeepConstraints();
              var moreExactThis = (XConstraint_EquatableArg)this;
              if (t is TypeProxy && u is TypeProxy) {
                return false;  // not enough information to do anything sensible
              } else if (t is TypeProxy || u is TypeProxy) {
                TypeProxy proxy;
                Type other;
                if (t is TypeProxy) {
                  proxy = (TypeProxy)t;
                  other = u;
                } else {
                  proxy = (TypeProxy)u;
                  other = t;
                }
                if (other.IsNumericBased() || other.IsBitVectorType || other.IsBigOrdinalType) {
                  resolver.ConstrainSubtypeRelation(other.NormalizeExpand(), proxy, errorMsg, true);
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else if (fullstrength) {
                  // the following is rather aggressive
                  if (Resolver.TypeConstraintsIncludeProxy(other, proxy)) {
                    return false;
                  } else {
                    if (other.IsRefType && resolver.HasApplicableNullableRefTypeConstraint_SubDirection(proxy)) {
                      other = other.NormalizeExpand();  // shave off all constraints
                    }
                    satisfied = resolver.AssignProxyAndHandleItsConstraints(proxy, other, true);
                    convertedIntoOtherTypeConstraints = true;
                    break;
                  }
                } else {
                  return false;  // not enough information
                }
              }
              if (moreExactThis.TreatTypeParamAsWild && (t.IsTypeParameter || u.IsTypeParameter)) {
                return true;
              } else if (!moreExactThis.AllowSuperSub) {
                resolver.ConstrainSubtypeRelation_Equal(t, u, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              Type a, b;
              // okay if t<:u or u<:t (this makes type inference more manageable, though it is more liberal than one might wish)
              satisfied = Type.FromSameHead_Subtype(t, u, resolver.builtIns, out a, out b);
              if (satisfied) {
                Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
                var cl = a is UserDefinedType ? ((UserDefinedType)a).ResolvedClass : null;
                for (int i = 0; i < a.TypeArgs.Count; i++) {
                  resolver.AllXConstraints.Add(new XConstraint_EquatableArg(tok,
                    a.TypeArgs[i], b.TypeArgs[i],
                    a is CollectionType || (cl != null && cl.TypeArgs[i].Variance != TypeParameter.TPVariance.Non),
                    false,
                    errorMsg));
                  moreXConstraints = true;
                }
              }
              break;
            }
          case "Freshable": {
              var collType = t.AsCollectionType;
              if (collType != null) {
                t = collType.Arg.NormalizeExpand();
              }
              if (t is TypeProxy) {
                return false;  // there is not enough information
              }
              satisfied = t.IsRefType;
              break;
            }
          case "ModifiesFrame": {
              var u = Types[1].NormalizeExpand();  // eventual ref type
              var collType = t is MapType ? null : t.AsCollectionType;
              if (collType != null) {
                t = collType.Arg.NormalizeExpand();
              }
              if (t is TypeProxy) {
                if (collType != null) {
                  // we know enough to convert into a subtyping constraint
                  resolver.AddXConstraint(Token.NoToken/*bogus, but it seems this token would be used only when integers are involved*/, "IsRefType", t, errorMsg);
                  moreXConstraints = true;
                  resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                  moreXConstraints = true;
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else {
                  return false;  // there is not enough information
                }
              }
              if (t.IsRefType) {
                resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              satisfied = false;
              break;
            }
          case "ReadsFrame": {
              var u = Types[1].NormalizeExpand();  // eventual ref type
              var arrTy = t.AsArrowType;
              if (arrTy != null) {
                t = arrTy.Result.NormalizeExpand();
              }
              var collType = t is MapType ? null : t.AsCollectionType;
              if (collType != null) {
                t = collType.Arg.NormalizeExpand();
              }
              if (t is TypeProxy) {
                if (collType != null) {
                  // we know enough to convert into a subtyping constraint
                  resolver.AddXConstraint(Token.NoToken/*bogus, but it seems this token would be used only when integers are involved*/, "IsRefType", t, errorMsg);
                  resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                  moreXConstraints = true;
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else {
                  return false;  // there is not enough information
                }
              }
              if (t.IsRefType) {
                resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              satisfied = false;
              break;
            }
          default:
            Contract.Assume(false);  // unknown XConstraint
            return false;  // to please the compiler
        }
        if (!satisfied) {
          errorMsg.FlagAsError();
        }
        return true;  // the XConstraint has served its purpose
      }

      public bool ProxyWithNoSubTypeConstraint(Type u, Resolver resolver) {
        Contract.Requires(u != null);
        Contract.Requires(resolver != null);
        var proxy = u as TypeProxy;
        if (proxy != null) {
          if (proxy.SubtypeConstraints.Any()) {
            return false;
          }
          foreach (var xc in resolver.AllXConstraints) {
            if (xc.ConstraintName == "Assignable" && xc.Types[0] == proxy) {
              return false;
            }
          }
          return true;
        }
        return false;
      }

      bool IsEqDetermined(Type t) {
        Contract.Requires(t != null);
        switch (TypeProxy.GetFamily(t)) {
          case TypeProxy.Family.Bool:
          case TypeProxy.Family.Char:
          case TypeProxy.Family.IntLike:
          case TypeProxy.Family.RealLike:
          case TypeProxy.Family.Ordinal:
          case TypeProxy.Family.BitVector:
            return true;
          case TypeProxy.Family.ValueType:
          case TypeProxy.Family.Ref:
          case TypeProxy.Family.Opaque:
          case TypeProxy.Family.Unknown:
          default:
            return false;  // TODO: could be made more exact
        }
      }

      internal bool CouldBeAnything() {
        return Types.All(t => t.NormalizeExpand() is TypeProxy);
      }

      /// <summary>
      /// If "t" or any type among its transitive sub/super-types (depending on "towardsSub")
      /// is a collection type, then returns the element/domain type of that collection.
      /// Otherwise, returns null.
      /// </summary>
      static Type FindCollectionType(Type t, bool towardsSub, ISet<TypeProxy> visited) {
        Contract.Requires(t != null);
        Contract.Requires(visited != null);
        t = t.NormalizeExpand();
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: FindCollectionType({0}, {1})", t, towardsSub ? "sub" : "super");
        }
        if (t is CollectionType) {
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("DEBUG: FindCollectionType({0}) = {1}", t, ((CollectionType)t).Arg);
          }
          return ((CollectionType)t).Arg;
        }
        var proxy = t as TypeProxy;
        if (proxy == null || visited.Contains(proxy)) {
          return null;
        }
        visited.Add(proxy);
        foreach (var sub in towardsSub ? proxy.Subtypes : proxy.Supertypes) {
          var e = FindCollectionType(sub, towardsSub, visited);
          if (e != null) {
            return e;
          }
        }
        return null;
      }
    }

    public class XConstraintWithExprs : XConstraint
    {
      public readonly Expression[] Exprs;
      public XConstraintWithExprs(IToken tok, string constraintName, Type[] types, Expression[] exprs, TypeConstraint.ErrorMsg errMsg)
        : base(tok, constraintName, types, errMsg) {
        Contract.Requires(tok != null);
        Contract.Requires(constraintName != null);
        Contract.Requires(types != null);
        Contract.Requires(exprs != null);
        Contract.Requires(errMsg != null);
        this.Exprs = exprs;
      }
    }

    public class XConstraint_EquatableArg : XConstraint
    {
      public bool AllowSuperSub;
      public bool TreatTypeParamAsWild;
      public XConstraint_EquatableArg(IToken tok, Type a, Type b, bool allowSuperSub, bool treatTypeParamAsWild, TypeConstraint.ErrorMsg errMsg)
        : base(tok, "EquatableArg", new Type[] { a, b }, errMsg) {
        Contract.Requires(tok != null);
        Contract.Requires(a != null);
        Contract.Requires(b != null);
        Contract.Requires(errMsg != null);
        AllowSuperSub = allowSuperSub;
        TreatTypeParamAsWild = treatTypeParamAsWild;
      }
    }

    /// <summary>
    /// Solves or simplifies as many type constraints as possible.
    /// If "allowDecisions" is "false", then no decisions, only determined inferences, are made; this mode is
    /// appropriate for the partial solving that's done before a member lookup.
    /// </summary>
    void PartiallySolveTypeConstraints(bool allowDecisions) {
      int state = 0;
      while (true) {
        if (2 <= state && !allowDecisions) {
          // time to say goodnight to Napoli
          return;
        } else if (AllTypeConstraints.Count == 0 && AllXConstraints.Count == 0) {
          // we're done
          return;
        }

        var anyNewConstraints = false;
        var fullStrength = false;
        // Process subtyping constraints
        PrintTypeConstraintState(220 + 2 * state);
        switch (state) {
          case 0: {
              var allTypeConstraints = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              var processed = new HashSet<TypeConstraint>();
              foreach (var c in allTypeConstraints) {
                ProcessOneSubtypingConstraintAndItsSubs(c, processed, fullStrength, ref anyNewConstraints);
              }

              allTypeConstraints = new List<TypeConstraint>(AllTypeConstraints);  // copy the list
              foreach (var c in allTypeConstraints) {
                var super = c.Super.NormalizeExpand() as TypeProxy;
                if (AssignKnownEnd(super, true, fullStrength)) {
                  anyNewConstraints = true;
                } else if (super != null && fullStrength && AssignKnownEndsFullstrength(super)) {  // KRML: is this used any more?
                  anyNewConstraints = true;
                }
              }
            }
            break;

          case 1: {
              // Process XConstraints
              // confirm as many XConstraints as possible, setting "anyNewConstraints" to "true" if the confirmation
              // of an XConstraint gives rise to new constraints to be handled in the loop above
              bool generatedMoreXConstraints;
              do {
                generatedMoreXConstraints = false;
                var allXConstraints = AllXConstraints;
                AllXConstraints = new List<XConstraint>();
                foreach (var xc in allXConstraints) {
                  bool convertedIntoOtherTypeConstraints, moreXConstraints;
                  if (xc.Confirm(this, fullStrength, out convertedIntoOtherTypeConstraints, out moreXConstraints)) {
                    if (convertedIntoOtherTypeConstraints) {
                      anyNewConstraints = true;
                    } else {
                      generatedMoreXConstraints = true;
                    }
                    if (moreXConstraints) {
                      generatedMoreXConstraints = true;
                    }
                  } else {
                    AllXConstraints.Add(xc);
                  }
                }
              } while (generatedMoreXConstraints);
            }
            break;

          case 2: {
              var assignables = AllXConstraints.Where(xc => xc.ConstraintName == "Assignable").ToList();
              var postponeForNow = new HashSet<TypeProxy>();
              foreach (var constraint in AllTypeConstraints) {
                var lhs = constraint.Super.NormalizeExpandKeepConstraints() as NonProxyType;
                if (lhs != null) {
                  foreach (var ta in lhs.TypeArgs) {
                    AddAllProxies(ta, postponeForNow);
                  }
                }
              }
              foreach (var constraint in AllTypeConstraints) {
                var lhs = constraint.Super.Normalize() as TypeProxy;
                if (lhs != null && !postponeForNow.Contains(lhs)) {
                  var rhss = assignables.Where(xc => xc.Types[0].Normalize() == lhs).Select(xc => xc.Types[1]).ToList();
                  if (ProcessAssignable(lhs, rhss)) {
                    anyNewConstraints = true;  // next time around the big loop, start with state 0 again
                  }
                }
              }
              foreach (var assignable in assignables) {
                var lhs = assignable.Types[0].Normalize() as TypeProxy;
                if (lhs != null && !postponeForNow.Contains(lhs)) {
                  var rhss = assignables.Where(xc => xc.Types[0].Normalize() == lhs).Select(xc => xc.Types[1]).ToList();
                  if (ProcessAssignable(lhs, rhss)) {
                    anyNewConstraints = true;  // next time around the big loop, start with state 0 again
                                               // process only one Assignable constraint in this way
                    break;
                  }
                }
              }
            }
            break;

          case 3:
            anyNewConstraints = ConvertAssignableToSubtypeConstraints(null);
            break;

          case 4: {
              var allTC = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              var proxyProcessed = new HashSet<TypeProxy>();
              foreach (var c in allTC) {
                ProcessFullStrength_SubDirection(c.Super, proxyProcessed, ref anyNewConstraints);
              }
              foreach (var xc in AllXConstraints) {
                if (xc.ConstraintName == "Assignable") {
                  ProcessFullStrength_SubDirection(xc.Types[0], proxyProcessed, ref anyNewConstraints);
                }
              }
              if (!anyNewConstraints) {
                // only do super-direction if sub-direction had no effect
                proxyProcessed = new HashSet<TypeProxy>();
                foreach (var c in allTC) {
                  ProcessFullStrength_SuperDirection(c.Sub, proxyProcessed, ref anyNewConstraints);
                }
                foreach (var xc in AllXConstraints) {
                  if (xc.ConstraintName == "Assignable") {
                    ProcessFullStrength_SuperDirection(xc.Types[1], proxyProcessed, ref anyNewConstraints);
                  }
                }
              }
              AllTypeConstraints.AddRange(allTC);
            }
            break;

          case 5: {
              // Process default numeric types
              var allTypeConstraints = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              foreach (var c in allTypeConstraints) {
                if (c.Super is ArtificialType) {
                  var proxy = c.Sub.NormalizeExpand() as TypeProxy;
                  if (proxy != null) {
                    AssignProxyAndHandleItsConstraints(proxy, c.Super is IntVarietiesSupertype ? (Type)Type.Int : Type.Real);
                    anyNewConstraints = true;
                    continue;
                  }
                }
                AllTypeConstraints.Add(c);
              }
            }
            break;

          case 6: {
              fullStrength = true;
              bool generatedMoreXConstraints;
              do {
                generatedMoreXConstraints = false;
                var allXConstraints = AllXConstraints;
                AllXConstraints = new List<XConstraint>();
                foreach (var xc in allXConstraints) {
                  bool convertedIntoOtherTypeConstraints, moreXConstraints;
                  if ((xc.ConstraintName == "Equatable" || xc.ConstraintName == "EquatableArg") && xc.Confirm(this, fullStrength, out convertedIntoOtherTypeConstraints, out moreXConstraints)) {
                    if (convertedIntoOtherTypeConstraints) {
                      anyNewConstraints = true;
                    } else {
                      generatedMoreXConstraints = true;
                    }
                    if (moreXConstraints) {
                      generatedMoreXConstraints = true;
                    }
                  } else {
                    AllXConstraints.Add(xc);
                  }
                }
              } while (generatedMoreXConstraints);
            }
            break;

          case 7: {
              // Process default reference types
              var allXConstraints = AllXConstraints;
              AllXConstraints = new List<XConstraint>();
              foreach (var xc in allXConstraints) {
                if (xc.ConstraintName == "IsRefType" || xc.ConstraintName == "IsNullableRefType") {
                  var proxy = xc.Types[0].Normalize() as TypeProxy;  // before we started processing default types, this would have been a proxy (since it's still in the A
                  if (proxy != null) {
                    AssignProxyAndHandleItsConstraints(proxy, builtIns.ObjectQ());
                    anyNewConstraints = true;
                    continue;
                  }
                }
                AllXConstraints.Add(xc);
              }
            }
            break;

          case 8: fullStrength = true; goto case 0;
          case 9: fullStrength = true; goto case 1;

          case 10: {
              // Finally, collapse constraints involving only proxies, which will have the effect of trading some type error
              // messages for type-underspecification messages.
              var allTypeConstraints = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              foreach (var c in allTypeConstraints) {
                var super = c.Super.NormalizeExpand();
                var sub = c.Sub.NormalizeExpand();
                if (super == sub) {
                  continue;
                } else if (super is TypeProxy && sub is TypeProxy) {
                  var proxy = (TypeProxy)super;
                  if (DafnyOptions.O.TypeInferenceDebug) {
                    Console.WriteLine("DEBUG: (merge in PartiallySolve) assigning proxy {0}.T := {1}", proxy, sub);
                  }
                  proxy.T = sub;
                  anyNewConstraints = true;  // signal a change in the constraints
                  continue;
                }
                AllTypeConstraints.Add(c);
              }
            }
            break;

          case 11:
            // we're so out of here
            return;
        }
        if (anyNewConstraints) {
          state = 0;
        } else {
          state++;
        }
      }
    }

    private void AddAllProxies(Type type, HashSet<TypeProxy> proxies) {
      Contract.Requires(type != null);
      Contract.Requires(proxies != null);
      var proxy = type as TypeProxy;
      if (proxy != null) {
        proxies.Add(proxy);
      } else {
        foreach (var ta in type.TypeArgs) {
          AddAllProxies(ta, proxies);
        }
      }
    }

    /// <summary>
    /// Set "lhs" to the meet of "rhss" and "lhs.Subtypes, if possible.
    /// Returns "true' if something was done, or "false" otherwise.
    /// </summary>
    private bool ProcessAssignable(TypeProxy lhs, List<Type> rhss) {
      Contract.Requires(lhs != null && lhs.T == null);
      Contract.Requires(rhss != null);
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.Write("DEBUG: ProcessAssignable: {0} with rhss:", lhs);
        foreach (var rhs in rhss) {
          Console.Write(" {0}", rhs);
        }
        Console.Write(" subtypes:");
        foreach (var sub in lhs.SubtypesKeepConstraints) {
          Console.Write(" {0}", sub);
        }
        Console.WriteLine();
      }
      Type meet = null;
      foreach (var rhs in rhss) {
        if (rhs is TypeProxy) { return false; }
        meet = meet == null ? rhs : Type.Meet(meet, rhs, builtIns);
      }
      foreach (var sub in lhs.SubtypesKeepConstraints) {
        if (sub is TypeProxy) { return false; }
        meet = meet == null ? sub : Type.Meet(meet, sub, builtIns);
      }
      if (meet == null) {
        return false;
      } else if (Reaches(meet, lhs, 1, new HashSet<TypeProxy>())) {
        // would cause a cycle, so don't do it
        return false;
      } else {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: ProcessAssignable: assigning proxy {0}.T := {1}", lhs, meet);
        }
        lhs.T = meet;
        return true;
      }
    }

    /// <summary>
    /// Convert each Assignable(A, B) constraint into a subtyping constraint A :> B,
    /// provided that:
    ///  - B is a non-proxy, and
    ///  - either "proxySpecialization" is null or some proxy in "proxySpecializations" prominently appears in A.
    /// </summary>
    bool ConvertAssignableToSubtypeConstraints(ISet<TypeProxy>/*?*/ proxySpecializations) {
      var anyNewConstraints = false;
      // If (the head of) the RHS of an Assignable is known, convert the XConstraint into a subtyping constraint
      var allX = AllXConstraints;
      AllXConstraints = new List<XConstraint>();
      foreach (var xc in allX) {
        if (xc.ConstraintName == "Assignable" && xc.Types[1].Normalize() is NonProxyType) {
          var t0 = xc.Types[0].NormalizeExpand();
          if (proxySpecializations == null
            || proxySpecializations.Contains(t0)
            || t0.TypeArgs.Exists(ta => proxySpecializations.Contains(ta))) {
            ConstrainSubtypeRelation(t0, xc.Types[1], xc.errorMsg, true);
            anyNewConstraints = true;
            continue;
          }
        }
        AllXConstraints.Add(xc);
      }
      return anyNewConstraints;
    }

    bool TightenUpEquatable(ISet<TypeProxy> proxiesOfInterest) {
      Contract.Requires(proxiesOfInterest != null);
      var anyNewConstraints = false;
      var allX = AllXConstraints;
      AllXConstraints = new List<XConstraint>();
      foreach (var xc in allX) {
        if (xc.ConstraintName == "Equatable" || xc.ConstraintName == "EquatableArg") {
          var t0 = xc.Types[0].NormalizeExpandKeepConstraints();
          var t1 = xc.Types[1].NormalizeExpandKeepConstraints();
          if (proxiesOfInterest.Contains(t0) || proxiesOfInterest.Contains(t1)) {
            ConstrainSubtypeRelation_Equal(t0, t1, xc.errorMsg);
            anyNewConstraints = true;
            continue;
          }
        }
        AllXConstraints.Add(xc);
      }
      return anyNewConstraints;
    }

    void ProcessOneSubtypingConstraintAndItsSubs(TypeConstraint c, ISet<TypeConstraint> processed, bool fullStrength, ref bool anyNewConstraints) {
      Contract.Requires(c != null);
      Contract.Requires(processed != null);
      if (processed.Contains(c)) {
        return;  // our job has already been done, or is at least in progress
      }
      processed.Add(c);

      var super = c.Super.NormalizeExpandKeepConstraints();
      var sub = c.Sub.NormalizeExpandKeepConstraints();
      // Process all subtype types before going on
      var subProxy = sub as TypeProxy;
      if (subProxy != null) {
        foreach (var cc in subProxy.SubtypeConstraints) {
          ProcessOneSubtypingConstraintAndItsSubs(cc, processed, fullStrength, ref anyNewConstraints);
        }
      }
      // the processing may have assigned some proxies, so we'll refresh super and sub
      super = super.NormalizeExpandKeepConstraints();
      sub = sub.NormalizeExpandKeepConstraints();

      if (super.Equals(sub)) {
        // the constraint is satisfied, so just drop it
      } else if ((super is NonProxyType || super is ArtificialType) && sub is NonProxyType) {
        ImposeSubtypingConstraint(super, sub, c.errorMsg);
        anyNewConstraints = true;
      } else if (AssignKnownEnd(sub as TypeProxy, true, fullStrength)) {
        anyNewConstraints = true;
      } else if (sub is TypeProxy && fullStrength && AssignKnownEndsFullstrength((TypeProxy)sub)) {
        anyNewConstraints = true;
      } else {
        // keep the constraint for now
        AllTypeConstraints.Add(c);
      }
    }

    void ProcessFullStrength_SubDirection(Type t, ISet<TypeProxy> processed, ref bool anyNewConstraints) {
      Contract.Requires(t != null);
      Contract.Requires(processed != null);
      var proxy = t.NormalizeExpand() as TypeProxy;
      if (proxy != null) {
        if (processed.Contains(proxy)) {
          return;  // our job has already been done, or is at least in progress
        }
        processed.Add(proxy);

        foreach (var u in proxy.SubtypesKeepConstraints_WithAssignable(AllXConstraints)) {
          ProcessFullStrength_SubDirection(u, processed, ref anyNewConstraints);
        }
        proxy = proxy.NormalizeExpand() as TypeProxy;
        if (proxy != null && AssignKnownEndsFullstrength_SubDirection(proxy)) {
          anyNewConstraints = true;
        }
      }
    }

    void ProcessFullStrength_SuperDirection(Type t, ISet<TypeProxy> processed, ref bool anyNewConstraints) {
      Contract.Requires(t != null);
      Contract.Requires(processed != null);
      var proxy = t.NormalizeExpand() as TypeProxy;
      if (proxy != null) {
        if (processed.Contains(proxy)) {
          return;  // our job has already been done, or is at least in progress
        }
        processed.Add(proxy);

        foreach (var u in proxy.Supertypes) {
          ProcessFullStrength_SuperDirection(u, processed, ref anyNewConstraints);
        }
        proxy = proxy.NormalizeExpand() as TypeProxy;
        if (proxy != null && AssignKnownEndsFullstrength_SuperDirection(proxy)) {
          anyNewConstraints = true;
        }
      }
    }

    /// <summary>
    /// Returns true if anything happened.
    /// </summary>
    bool AssignKnownEnd(TypeProxy proxy, bool keepConstraints, bool fullStrength) {
      Contract.Requires(proxy == null || proxy.T == null);  // caller is supposed to have called NormalizeExpand
      if (proxy == null) {
        // nothing to do
        return false;
      }
      // ----- first, go light; also, prefer subtypes over supertypes
      IEnumerable<Type> subTypes = keepConstraints ? proxy.SubtypesKeepConstraints : proxy.Subtypes;
      foreach (var su in subTypes) {
        bool isRoot, isLeaf, headRoot, headLeaf;
        CheckEnds(su, out isRoot, out isLeaf, out headRoot, out headLeaf);
        Contract.Assert(!isRoot || headRoot);  // isRoot ==> headRoot
        if (isRoot) {
          if (Reaches(su, proxy, 1, new HashSet<TypeProxy>())) {
            // adding a constraint here would cause a bad cycle, so we don't
          } else {
            AssignProxyAndHandleItsConstraints(proxy, su, keepConstraints);
            return true;
          }
        } else if (headRoot) {
          if (Reaches(su, proxy, 1, new HashSet<TypeProxy>())) {
            // adding a constraint here would cause a bad cycle, so we don't
          } else {
            AssignProxyAndHandleItsConstraints(proxy, TypeProxy.HeadWithProxyArgs(su), keepConstraints);
            return true;
          }
        }
      }
      if (fullStrength) {
        IEnumerable<Type> superTypes = keepConstraints ? proxy.SupertypesKeepConstraints : proxy.Supertypes;
        foreach (var su in superTypes) {
          bool isRoot, isLeaf, headRoot, headLeaf;
          CheckEnds(su, out isRoot, out isLeaf, out headRoot, out headLeaf);
          Contract.Assert(!isLeaf || headLeaf);  // isLeaf ==> headLeaf
          if (isLeaf) {
            if (Reaches(su, proxy, -1, new HashSet<TypeProxy>())) {
              // adding a constraint here would cause a bad cycle, so we don't
            } else {
              AssignProxyAndHandleItsConstraints(proxy, su, keepConstraints);
              return true;
            }
          } else if (headLeaf) {
            if (Reaches(su, proxy, -1, new HashSet<TypeProxy>())) {
              // adding a constraint here would cause a bad cycle, so we don't
            } else {
              AssignProxyAndHandleItsConstraints(proxy, TypeProxy.HeadWithProxyArgs(su), keepConstraints);
              return true;
            }
          }
        }
      }
      return false;
    }

    bool AssignKnownEndsFullstrength(TypeProxy proxy) {
      Contract.Requires(proxy != null);
      // ----- continue with full strength
      // If the meet of the subtypes exists, use it
      var meets = new List<Type>();
      foreach (var su in proxy.Subtypes) {
        if (su is TypeProxy) {
          continue;  // don't include proxies in the meet computation
        }
        int i = 0;
        for (; i < meets.Count; i++) {
          var j = Type.Meet(meets[i], su, builtIns);
          if (j != null) {
            meets[i] = j;
            break;
          }
        }
        if (i == meets.Count) {
          // we went to the end without finding a place to meet up
          meets.Add(su);
        }
      }
      if (meets.Count == 1 && !Reaches(meets[0], proxy, 1, new HashSet<TypeProxy>())) {
        // we were able to compute a meet of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, meets[0]);
        return true;
      }
      // If the join of the supertypes exists, use it
      var joins = new List<Type>();
      foreach (var su in proxy.Supertypes) {
        if (su is TypeProxy) {
          continue;  // don't include proxies in the join computation
        }
        int i = 0;
        for (; i < joins.Count; i++) {
          var j = Type.Join(joins[i], su, builtIns);
          if (j != null) {
            joins[i] = j;
            break;
          }
        }
        if (i == joins.Count) {
          // we went to the end without finding a place to join in
          joins.Add(su);
        }
      }
      if (joins.Count == 1 && !(joins[0] is ArtificialType) && !Reaches(joins[0], proxy, -1, new HashSet<TypeProxy>())) {
        // we were able to compute a join of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, joins[0]);
        return true;
      }

      return false;
    }

    bool AssignKnownEndsFullstrength_SubDirection(TypeProxy proxy) {
      Contract.Requires(proxy != null && proxy.T == null);
      // If the meet of the subtypes exists, use it
      var meets = new List<Type>();
      var proxySubs = new HashSet<TypeProxy>();
      proxySubs.Add(proxy);
      foreach (var su in proxy.SubtypesKeepConstraints_WithAssignable(AllXConstraints)) {
        if (su is TypeProxy) {
          proxySubs.Add((TypeProxy)su);
        } else {
          int i = 0;
          for (; i < meets.Count; i++) {
            var j = Type.Meet(meets[i], su, builtIns);
            if (j != null) {
              meets[i] = j;
              break;
            }
          }
          if (i == meets.Count) {
            // we went to the end without finding a place to meet up
            meets.Add(su);
          }
        }
      }
      if (meets.Count == 1 && !Reaches(meets[0], proxy, 1, new HashSet<TypeProxy>())) {
        // We were able to compute a meet of all the subtyping constraints, so use it.
        // Well, maybe.  If "meets[0]" denotes a non-null type and "proxy" is something
        // that could be assigned "null", then set "proxy" to the nullable version of "meets[0]".
        // Stated differently, think of an applicable "IsNullableRefType" constraint as
        // being part of the meet computation, essentially throwing in a "...?".
        // Except: If the meet is a tight bound--meaning, it is also a join--then pick it
        // after all, because that seems to give rise to less confusing error messages.
        if (meets[0].IsNonNullRefType) {
          Type join = null;
          if (JoinOfAllSupertypes(proxy, ref join, new HashSet<TypeProxy>(), false) && join != null && Type.SameHead(meets[0], join)) {
            // leave it
          } else {
            CloseOverAssignableRhss(proxySubs);
            if (HasApplicableNullableRefTypeConstraint(proxySubs)) {
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("DEBUG: Found meet {0} for proxy {1}, but weakening it to {2}", meets[0], proxy, meets[0].NormalizeExpand());
              }
              AssignProxyAndHandleItsConstraints(proxy, meets[0].NormalizeExpand(), true);
              return true;
            }
          }
        }
        AssignProxyAndHandleItsConstraints(proxy, meets[0], true);
        return true;
      }
      return false;
    }

    private void CloseOverAssignableRhss(ISet<TypeProxy> proxySet) {
      Contract.Requires(proxySet != null);
      while (true) {
        var moreChanges = false;
        foreach (var xc in AllXConstraints) {
          if (xc.ConstraintName == "Assignable") {
            var source = xc.Types[0].Normalize() as TypeProxy;
            var sink = xc.Types[1].Normalize() as TypeProxy;
            if (source != null && sink != null && proxySet.Contains(source) && !proxySet.Contains(sink)) {
              proxySet.Add(sink);
              moreChanges = true;
            }
          }
        }
        if (!moreChanges) {
          return;
        }
      }
    }
    private bool HasApplicableNullableRefTypeConstraint(ISet<TypeProxy> proxySet) {
      Contract.Requires(proxySet != null);
      var nullableProxies = new HashSet<TypeProxy>();
      foreach (var xc in AllXConstraints) {
        if (xc.ConstraintName == "IsNullableRefType") {
          var npr = xc.Types[0].Normalize() as TypeProxy;
          if (npr != null) {
            nullableProxies.Add(npr);
          }
        }
      }
      return proxySet.Any(nullableProxies.Contains);
    }
    private bool HasApplicableNullableRefTypeConstraint_SubDirection(TypeProxy proxy) {
      Contract.Requires(proxy != null);
      var nullableProxies = new HashSet<TypeProxy>();
      foreach (var xc in AllXConstraints) {
        if (xc.ConstraintName == "IsNullableRefType") {
          var npr = xc.Types[0].Normalize() as TypeProxy;
          if (npr != null) {
            nullableProxies.Add(npr);
          }
        }
      }
      return HasApplicableNullableRefTypeConstraint_SubDirection_aux(proxy, nullableProxies, new HashSet<TypeProxy>());
    }
    private bool HasApplicableNullableRefTypeConstraint_SubDirection_aux(TypeProxy proxy, ISet<TypeProxy> nullableProxies, ISet<TypeProxy> visitedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(nullableProxies != null);
      Contract.Requires(visitedProxies != null);

      if (visitedProxies.Contains(proxy)) {
        return false;
      }
      visitedProxies.Add(proxy);

      if (nullableProxies.Contains(proxy)) {
        return true;
      }

      foreach (var sub in proxy.SubtypesKeepConstraints_WithAssignable(AllXConstraints)) {
        var psub = sub as TypeProxy;
        if (psub != null && HasApplicableNullableRefTypeConstraint_SubDirection_aux(psub, nullableProxies, visitedProxies)) {
          return true;
        }
      }
      return false;
    }

    bool AssignKnownEndsFullstrength_SuperDirection(TypeProxy proxy) {
      Contract.Requires(proxy != null && proxy.T == null);
      // First, compute the the meet of the Assignable LHSs.  Then, compute
      // the join of that meet and the supertypes.
      var meets = new List<Type>();
      foreach (var xc in AllXConstraints) {
        if (xc.ConstraintName == "Assignable" && xc.Types[1].Normalize() == proxy) {
          var su = xc.Types[0].NormalizeExpandKeepConstraints();
          if (su is TypeProxy) {
            continue;  // don't include proxies in the meet computation
          }
          int i = 0;
          for (; i < meets.Count; i++) {
            var j = Type.Meet(meets[i], su, builtIns);
            if (j != null) {
              meets[i] = j;
              break;
            }
          }
          if (i == meets.Count) {
            // we went to the end without finding a place to meet in
            meets.Add(su);
          }
        }
      }
      // If the join of the supertypes exists, use it
      var joins = new List<Type>(meets);
      foreach (var su in proxy.SupertypesKeepConstraints) {
        if (su is TypeProxy) {
          continue;  // don't include proxies in the join computation
        }
        int i = 0;
        for (; i < joins.Count; i++) {
          var j = Type.Join(joins[i], su, builtIns);
          if (j != null) {
            joins[i] = j;
            break;
          }
        }
        if (i == joins.Count) {
          // we went to the end without finding a place to join in
          joins.Add(su);
        }
      }
      if (joins.Count == 1 && !(joins[0] is ArtificialType) && !Reaches(joins[0], proxy, -1, new HashSet<TypeProxy>())) {
        // we were able to compute a join of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, joins[0], true);
        return true;
      }
      return false;
    }

    int _reaches_recursion;
    private bool Reaches(Type t, TypeProxy proxy, int direction, HashSet<TypeProxy> visited) {
      if (_reaches_recursion == 20) {
        Contract.Assume(false);  // possible infinite recursion
      }
      _reaches_recursion++;
      var b = Reaches_aux(t, proxy, direction, visited);
      _reaches_recursion--;
      return b;
    }
    private bool Reaches_aux(Type t, TypeProxy proxy, int direction, HashSet<TypeProxy> visited) {
      Contract.Requires(t != null);
      Contract.Requires(proxy != null);
      Contract.Requires(visited != null);
      t = t.NormalizeExpand();
      var tproxy = t as TypeProxy;
      if (tproxy == null) {
        var polarities = ConstrainTypeHead(t, t);
        Contract.Assert(polarities != null);
        Contract.Assert(polarities.Count <= t.TypeArgs.Count);
        for (int i = 0; i < polarities.Count; i++) {
          if (Reaches(t.TypeArgs[i], proxy, direction * polarities[i], visited)) {
            return true;
          }
        }
        return false;
      } else if (tproxy == proxy) {
        return true;
      } else if (visited.Contains(tproxy)) {
        return false;
      } else {
        visited.Add(tproxy);
        if (0 <= direction && tproxy.Subtypes.Any(su => Reaches(su, proxy, direction, visited))) {
          return true;
        }
        if (direction <= 0 && tproxy.Supertypes.Any(su => Reaches(su, proxy, direction, visited))) {
          return true;
        }
        return false;
      }
    }

    [System.Diagnostics.Conditional("TI_DEBUG_PRINT")]
    void PrintTypeConstraintState(int lbl) {
      if (!DafnyOptions.O.TypeInferenceDebug) {
        return;
      }
      Console.WriteLine("DEBUG: ---------- type constraints ---------- {0} {1}", lbl, lbl == 0 && currentMethod != null ? currentMethod.Name : "");
      foreach (var constraint in AllTypeConstraints) {
        var super = constraint.Super.Normalize();
        var sub = constraint.Sub.Normalize();
        Console.WriteLine("    {0} :> {1}", super is IntVarietiesSupertype ? "int-like" : super is RealVarietiesSupertype ? "real-like" : super.ToString(), sub);
      }
      foreach (var xc in AllXConstraints) {
        Console.WriteLine("    {0}", xc);
      }
      Console.WriteLine();
      if (lbl % 2 == 1) {
        Console.WriteLine("DEBUG: --------------------------------------");
      }
    }

    /// <summary>
    /// Attempts to fully solve all type constraints.
    /// Upon failure, reports errors.
    /// Clears all constraints.
    /// </summary>
    void SolveAllTypeConstraints() {
      PrintTypeConstraintState(0);
      PartiallySolveTypeConstraints(true);
      PrintTypeConstraintState(1);
      foreach (var constraint in AllTypeConstraints) {
        if (Type.IsSupertype(constraint.Super, constraint.Sub)) {
          // unexpected condition -- PartiallySolveTypeConstraints is supposed to have continued until no more sub-typing constraints can be satisfied
          Contract.Assume(false, string.Format("DEBUG: Unexpectedly satisfied supertype relation ({0} :> {1}) |||| ", constraint.Super, constraint.Sub));
        } else {
          constraint.FlagAsError();
        }
      }
      foreach (var xc in AllXConstraints) {
        bool convertedIntoOtherTypeConstraints, moreXConstraints;
        if (xc.Confirm(this, true, out convertedIntoOtherTypeConstraints, out moreXConstraints)) {
          // unexpected condition -- PartiallySolveTypeConstraints is supposed to have continued until no more XConstraints were confirmable
          Contract.Assume(false, string.Format("DEBUG: Unexpectedly confirmed XConstraint: {0} |||| ", xc));
        } else if (xc.CouldBeAnything()) {
          // suppress the error message; it will later be flagged as an underspecified type
        } else {
          xc.errorMsg.FlagAsError();
        }
      }
      TypeConstraint.ReportErrors(reporter);
      AllTypeConstraints.Clear();
      AllXConstraints.Clear();
    }

    public class TypeConstraint
    {
      public readonly Type Super;
      public readonly Type Sub;
      public readonly bool KeepConstraints;

      private static List<ErrorMsg> ErrorsToBeReported = new List<ErrorMsg>();
      public static void ReportErrors(ErrorReporter reporter) {
        Contract.Requires(reporter != null);
        foreach (var err in ErrorsToBeReported) {
          err.ReportAsError(reporter);
        }
        ErrorsToBeReported.Clear();
      }
      abstract public class ErrorMsg
      {
        public abstract IToken Tok { get; }
        bool reported;
        public void FlagAsError() {
          TypeConstraint.ErrorsToBeReported.Add(this);
        }
        internal void ReportAsError(ErrorReporter reporter) {
          Contract.Requires(reporter != null);
          if (!reported) {  // this "reported" bit is checked only for the top-level message, but this message and all nested ones get their "reported" bit set to "true" as a result
            Reporting(reporter, "");
          }
        }
        private void Reporting(ErrorReporter reporter, string suffix) {
          Contract.Requires(reporter != null);
          Contract.Requires(suffix != null);
          if (this is ErrorMsgWithToken) {
            var err = (ErrorMsgWithToken)this;
            Contract.Assert(err.Tok != null);
            reporter.Error(MessageSource.Resolver, err.Tok, err.Msg + suffix, err.MsgArgs);
          } else {
            var err = (ErrorMsgWithBase)this;
            err.BaseMsg.Reporting(reporter, " (" + string.Format(err.Msg, err.MsgArgs) + ")" + suffix);
          }
          reported = true;
        }
      }
      public class ErrorMsgWithToken : ErrorMsg
      {
        readonly IToken tok;
        public override IToken Tok {
          get { return tok; }
        }
        public readonly string Msg;
        public readonly object[] MsgArgs;
        public ErrorMsgWithToken(IToken tok, string msg, params object[] msgArgs) {
          Contract.Requires(tok != null);
          Contract.Requires(msg != null);
          Contract.Requires(msgArgs != null);
          this.tok = tok;
          this.Msg = msg;
          this.MsgArgs = msgArgs;
        }
      }
      public class ErrorMsgWithBase : ErrorMsg
      {
        public override IToken Tok {
          get { return BaseMsg.Tok; }
        }
        public readonly ErrorMsg BaseMsg;
        public readonly string Msg;
        public readonly object[] MsgArgs;
        public ErrorMsgWithBase(ErrorMsg baseMsg, string msg, params object[] msgArgs) {
          Contract.Requires(baseMsg != null);
          Contract.Requires(msg != null);
          Contract.Requires(msgArgs != null);
          BaseMsg = baseMsg;
          Msg = msg;
          MsgArgs = msgArgs;
        }
      }
      public readonly ErrorMsg errorMsg;
      public TypeConstraint(Type super, Type sub, ErrorMsg errMsg, bool keepConstraints) {
        Contract.Requires(super != null);
        Contract.Requires(sub != null);
        Contract.Requires(errMsg != null);
        Super = super;
        Sub = sub;
        errorMsg = errMsg;
        KeepConstraints = keepConstraints;
      }
      public void FlagAsError() {
        errorMsg.FlagAsError();
      }
    }

    // ------------------------------------------------------------------------------------------------------
    // ----- Visitors ---------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region Visitors
    class ResolverBottomUpVisitor : BottomUpVisitor
    {
      protected Resolver resolver;
      public ResolverBottomUpVisitor(Resolver resolver) {
        Contract.Requires(resolver != null);
        this.resolver = resolver;
      }
    }
    abstract class ResolverTopDownVisitor<T> : TopDownVisitor<T>
    {
      protected Resolver resolver;
      public ResolverTopDownVisitor(Resolver resolver) {
        Contract.Requires(resolver != null);
        this.resolver = resolver;
      }
    }
#endregion Visitors

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckTypeInference -----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region CheckTypeInference
    private void CheckTypeInference_Member(MemberDecl member) {
      if (member is ConstantField) {
        var field = (ConstantField) member;
        if (field.Rhs != null) {
          CheckTypeInference(field.Rhs, new NoContext(member.EnclosingClass.Module));
        }
        CheckTypeInference(field.Type, new NoContext(member.EnclosingClass.Module), field.tok, "const");
      } else if (member is Method) {
        var m = (Method)member;
        m.Req.Iter(mfe => CheckTypeInference_MaybeFreeExpression(mfe, m));
        m.Ens.Iter(mfe => CheckTypeInference_MaybeFreeExpression(mfe, m));
        CheckTypeInference_Specification_FrameExpr(m.Mod, m);
        CheckTypeInference_Specification_Expr(m.Decreases, m);
        if (m.Body != null) {
          CheckTypeInference(m.Body, m);
        }
      } else if (member is Function) {
        var f = (Function)member;
        var errorCount = reporter.Count(ErrorLevel.Error);
        f.Req.Iter(e => CheckTypeInference(e.E, f));
        f.Ens.Iter(e => CheckTypeInference(e.E, f));
        f.Reads.Iter(fe => CheckTypeInference(fe.E, f));
        CheckTypeInference_Specification_Expr(f.Decreases, f);
        if (f.Body != null) {
          CheckTypeInference(f.Body, f);
        }
        if (errorCount == reporter.Count(ErrorLevel.Error) && f is FixpointPredicate) {
          var cop = (FixpointPredicate)f;
          CheckTypeInference_Member(cop.PrefixPredicate);
        }
      }
    }

    private void CheckTypeInference_MaybeFreeExpression(MaybeFreeExpression mfe, ICodeContext codeContext) {
      Contract.Requires(mfe != null);
      Contract.Requires(codeContext != null);
      foreach (var e in Attributes.SubExpressions(mfe.Attributes)) {
        CheckTypeInference(e, codeContext);
      }
      CheckTypeInference(mfe.E, codeContext);
    }
    private void CheckTypeInference_Specification_Expr(Specification<Expression> spec, ICodeContext codeContext) {
      Contract.Requires(spec != null);
      Contract.Requires(codeContext != null);
      foreach (var e in Attributes.SubExpressions(spec.Attributes)) {
        CheckTypeInference(e, codeContext);
      }
      spec.Expressions.Iter(e => CheckTypeInference(e, codeContext));
    }
    private void CheckTypeInference_Specification_FrameExpr(Specification<FrameExpression> spec, ICodeContext codeContext) {
      Contract.Requires(spec != null);
      Contract.Requires(codeContext != null);
      foreach (var e in Attributes.SubExpressions(spec.Attributes)) {
        CheckTypeInference(e, codeContext);
      }
      spec.Expressions.Iter(fe => CheckTypeInference(fe.E, codeContext));
    }
    void CheckTypeInference(Expression expr, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Requires(codeContext != null);
      PartiallySolveTypeConstraints(true);
      var c = new CheckTypeInference_Visitor(this, codeContext);
      c.Visit(expr);
    }
    void CheckTypeInference(Type type, ICodeContext codeContext, IToken tok, string what) {
      Contract.Requires(type != null);
      Contract.Requires(codeContext != null);
      Contract.Requires(tok != null);
      Contract.Requires(what != null);
      PartiallySolveTypeConstraints(true);
      var c = new CheckTypeInference_Visitor(this, codeContext);
      c.CheckTypeIsDetermined(tok, type, what);
    }
    void CheckTypeInference(Statement stmt, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      PartiallySolveTypeConstraints(true);
      var c = new CheckTypeInference_Visitor(this, codeContext);
      c.Visit(stmt);
    }
    class CheckTypeInference_Visitor : ResolverBottomUpVisitor
    {
      readonly ICodeContext codeContext;
      public CheckTypeInference_Visitor(Resolver resolver, ICodeContext codeContext)
        : base(resolver) {
        Contract.Requires(resolver != null);
        Contract.Requires(codeContext != null);
        this.codeContext = codeContext;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is VarDeclStmt) {
          var s = (VarDeclStmt)stmt;
          foreach (var local in s.Locals) {
            CheckTypeIsDetermined(local.Tok, local.Type, "local variable");
            CheckTypeArgsContainNoOrdinal(local.Tok, local.type);
          }
        } else if (stmt is LetStmt) {
          var s = (LetStmt)stmt;
          s.LocalVars.Iter(local => CheckTypeIsDetermined(local.Tok, local.Type, "local variable"));
          s.LocalVars.Iter(local => CheckTypeArgsContainNoOrdinal(local.Tok, local.Type));

        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          s.BoundVars.Iter(bv => CheckTypeIsDetermined(bv.tok, bv.Type, "bound variable"));
          s.Bounds = DiscoverBestBounds_MultipleVars(s.BoundVars, s.Range, true, ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable);
          s.BoundVars.Iter(bv => CheckTypeArgsContainNoOrdinal(bv.tok, bv.Type));

        } else if (stmt is AssignSuchThatStmt) {
          var s = (AssignSuchThatStmt)stmt;
          if (s.AssumeToken == null) {
            var varLhss = new List<IVariable>();
            foreach (var lhs in s.Lhss) {
              var ide = (IdentifierExpr)lhs.Resolved;  // successful resolution implies all LHS's are IdentifierExpr's
              varLhss.Add(ide.Var);
            }
            s.Bounds = DiscoverBestBounds_MultipleVars(varLhss, s.Expr, true, ComprehensionExpr.BoundedPool.PoolVirtues.None);
          }
          foreach (var lhs in s.Lhss) {
            var what = lhs is IdentifierExpr ? string.Format("variable '{0}'", ((IdentifierExpr)lhs).Name) : "LHS";
            CheckTypeArgsContainNoOrdinal(lhs.tok, lhs.Type);
          }
        } else if (stmt is CalcStmt) {
          var s = (CalcStmt)stmt;
          // The resolution of the calc statement builds up .Steps and .Result, which are of the form E0 OP E1, where
          // E0 and E1 are expressions from .Lines.  These additional expressions still need to have their .ResolvedOp
          // fields filled in, so we visit them (but not their subexpressions) here.
          foreach (var e in s.Steps) {
            Visit(e);
          }
          Visit(s.Result);
        }
      }
      protected override void VisitOneExpr(Expression expr) {
        if (expr is LiteralExpr) {
          var e = (LiteralExpr)expr;
          var t = e.Type as BitvectorType;
          if (t != null) {
            var n = (BigInteger)e.Value;
            // check that the given literal fits into the bitvector width
            if (BigInteger.Pow(2, t.Width) <= n) {
              resolver.reporter.Error(MessageSource.Resolver, e.tok, "bitvector literal ({0}) is too large for the type {1}", e.Value, t);
            }
          }
        } else if (expr is ComprehensionExpr) {
          var e = (ComprehensionExpr)expr;
          foreach (var bv in e.BoundVars) {
            if (!IsDetermined(bv.Type.Normalize())) {
              resolver.reporter.Error(MessageSource.Resolver, bv.tok, "type of bound variable '{0}' could not be determined; please specify the type explicitly", bv.Name);
            } else if (codeContext is FixpointPredicate) {
              CheckContainsNoOrdinal(bv.tok, bv.Type, string.Format("type of bound variable '{0}' is not allowed to use type ORDINAL", bv.Name));
            }
          }
          // apply bounds discovery to quantifiers, finite sets, and finite maps
          string what = null;
          Expression whereToLookForBounds = null;
          var polarity = true;
          if (e is QuantifierExpr) {
            what = "quantifier";
            whereToLookForBounds = ((QuantifierExpr)e).LogicalBody();
            polarity = e is ExistsExpr;
          } else if (e is SetComprehension) {
            what = "set comprehension";
            whereToLookForBounds = e.Range;
          } else if (e is MapComprehension) {
            what = "map comprehension";
            whereToLookForBounds = e.Range;
          } else {
            Contract.Assume(e is LambdaExpr);  // otherwise, unexpected ComprehensionExpr
          }
          if (whereToLookForBounds != null) {
            e.Bounds = DiscoverBestBounds_MultipleVars_AllowReordering(e.BoundVars, whereToLookForBounds, polarity, ComprehensionExpr.BoundedPool.PoolVirtues.None);
            if (2 <= DafnyOptions.O.Allocated && (codeContext is Function || codeContext is ConstantField || codeContext is RedirectingTypeDecl)) {
              // functions are not allowed to depend on the set of allocated objects
              foreach (var bv in ComprehensionExpr.BoundedPool.MissingBounds(e.BoundVars, e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc)) {
                var msgFormat = "a {0} involved in a {3} definition is not allowed to depend on the set of allocated references; Dafny's heuristics can't figure out a bound for the values of '{1}'";
                if (bv.Type.IsTypeParameter) {
                  var tp = bv.Type.AsTypeParameter;
                  msgFormat += " (perhaps declare its type, '{2}', as '{2}(!new)')";
                }
                var declKind = codeContext is RedirectingTypeDecl ? ((RedirectingTypeDecl)codeContext).WhatKind : ((MemberDecl)codeContext).WhatKind;
                resolver.reporter.Error(MessageSource.Resolver, e, msgFormat, what, bv.Name, bv.Type, declKind);
              }
            }
            if ((e is SetComprehension && ((SetComprehension)e).Finite) || (e is MapComprehension && ((MapComprehension)e).Finite)) {
              // the comprehension had better produce a finite set
              if (e is SetComprehension && e.Type.HasFinitePossibleValues) {
                // This means the set is finite, regardless of if the Range is bounded.  So, we don't give any error here.
                // However, if this expression is used in a non-ghost context (which is not yet known at this stage of
                // resolution), the resolver will generate an error about that later.
              } else {
                // we cannot be sure that the set/map really is finite
                foreach (var bv in ComprehensionExpr.BoundedPool.MissingBounds(e.BoundVars, e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.Finite)) {
                  resolver.reporter.Error(MessageSource.Resolver, e, "a {0} must produce a finite set, but Dafny's heuristics can't figure out how to produce a bounded set of values for '{1}'", what, bv.Name);
                }
              }
            }
          }


          if (e is ExistsExpr && e.Range == null) {
            var binBody = ((ExistsExpr)e).Term as BinaryExpr;
            if (binBody != null && binBody.Op == BinaryExpr.Opcode.Imp) {  // check Op, not ResolvedOp, in order to distinguish ==> and <==
              // apply the wisdom of Claude Marche: issue a warning here
              resolver.reporter.Warning(MessageSource.Resolver, e.tok,
                "the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; " +
                "if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning");
            }
          }

        } else if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          if (e.Member is Function || e.Member is Method) {
            foreach (var p in e.TypeApplication) {
              if (!IsDetermined(p.Normalize())) {
                resolver.reporter.Error(MessageSource.Resolver, e.tok, "type '{0}' to the {2} '{1}' is not determined", p, e.Member.Name, e.Member.WhatKind);
              } else {
                CheckContainsNoOrdinal(e.tok, p, string.Format("type '{0}' to the {2} '{1}' is not allowed to use ORDINAL", p, e.Member.Name, e.Member.WhatKind));
              }
            }
          }
        } else if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          foreach (var p in e.TypeArgumentSubstitutions) {
            if (!IsDetermined(p.Value.Normalize())) {
              resolver.reporter.Error(MessageSource.Resolver, e.tok, "type variable '{0}' in the function call to '{1}' could not be determined{2}", p.Key.Name, e.Name,
                (e.Name.StartsWith("reveal_"))
                ? ". If you are making an opaque function, make sure that the function can be called."
                : ""
              );
            } else {
              CheckContainsNoOrdinal(e.tok, p.Value, string.Format("type argument to function call '{1}' (for type variable '{0}') is not allowed to use type ORDINAL", p.Key.Name, e.Name));
            }
          }
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          foreach (var p in e.LHSs) {
            foreach (var x in p.Vars) {
              if (!IsDetermined(x.Type.Normalize())) {
                resolver.reporter.Error(MessageSource.Resolver, x.tok, "the type of the bound variable '{0}' could not be determined", x.Name);
              } else {
                CheckTypeArgsContainNoOrdinal(x.tok, x.Type);
              }
            }
          }
        } else if (expr is IdentifierExpr) {
          // by specializing for IdentifierExpr, error messages will be clearer
          CheckTypeIsDetermined(expr.tok, expr.Type, "variable");
        } else if (CheckTypeIsDetermined(expr.tok, expr.Type, "expression")) {
          if (expr is BinaryExpr) {
            var e = (BinaryExpr)expr;
            e.ResolvedOp = ResolveOp(e.Op, e.E1.Type);
            // Check for useless comparisons with "null"
            Expression other = null;  // if "null" if one of the operands, then "other" is the other
            if (e.E0 is LiteralExpr && ((LiteralExpr)e.E0).Value == null) {
              other = e.E1;
            } else if (e.E1 is LiteralExpr && ((LiteralExpr)e.E1).Value == null) {
              other = e.E0;
            }
            if (other != null) {
              bool sense = true;
              switch (e.ResolvedOp) {
                case BinaryExpr.ResolvedOpcode.NeqCommon:
                  sense = false;
                  goto case BinaryExpr.ResolvedOpcode.EqCommon;
                case BinaryExpr.ResolvedOpcode.EqCommon: {
                    var nntUdf = other.Type.AsNonNullRefType;
                    if (nntUdf != null) {
                      string name = null;
                      string hint = "";
                      other = other.Resolved;
                      if (other is IdentifierExpr) {
                        name = string.Format("variable '{0}'", ((IdentifierExpr)other).Name);
                      } else if (other is MemberSelectExpr) {
                        var field = ((MemberSelectExpr)other).Member as Field;
                        // The type of the field may be a formal type parameter, in which case the hint is omitted
                        if (field.Type.IsNonNullRefType) {
                          name = string.Format("field '{0}'", field.Name);
                        }
                      }
                      if (name != null) {
                        // The following relies on that a NonNullTypeDecl has a .Rhs that is a
                        // UserDefinedType denoting the possibly null type declaration and that
                        // these two types have the same number of type arguments.
                        var nonNullTypeDecl = (NonNullTypeDecl)nntUdf.ResolvedClass;
                        var possiblyNullUdf = (UserDefinedType)nonNullTypeDecl.Rhs;
                        var possiblyNullTypeDecl = (ClassDecl)possiblyNullUdf.ResolvedClass;
                        Contract.Assert(nonNullTypeDecl.TypeArgs.Count == possiblyNullTypeDecl.TypeArgs.Count);
                        Contract.Assert(nonNullTypeDecl.TypeArgs.Count == nntUdf.TypeArgs.Count);
                        var ty = new UserDefinedType(nntUdf.tok, possiblyNullUdf.Name, possiblyNullTypeDecl, nntUdf.TypeArgs);

                        hint = string.Format(" (to make it possible for {0} to have the value 'null', declare its type to be '{1}')", name, ty);
                      }
                      resolver.reporter.Warning(MessageSource.Resolver, e.tok,
                        string.Format("the type of the other operand is a non-null type, so this comparison with 'null' will always return '{0}'{1}",
                        sense ? "false" : "true", hint));
                    }
                    break;
                  }
                case BinaryExpr.ResolvedOpcode.NotInSet:
                case BinaryExpr.ResolvedOpcode.NotInSeq:
                case BinaryExpr.ResolvedOpcode.NotInMultiSet:
                  sense = false;
                  goto case BinaryExpr.ResolvedOpcode.InSet;
                case BinaryExpr.ResolvedOpcode.InSet:
                case BinaryExpr.ResolvedOpcode.InSeq:
                case BinaryExpr.ResolvedOpcode.InMultiSet: {
                    var ty = other.Type.NormalizeExpand();
                    var what = ty is SetType ? "set" : ty is SeqType ? "seq" : "multiset";
                    if (((CollectionType)ty).Arg.IsNonNullRefType) {
                      resolver.reporter.Warning(MessageSource.Resolver, e.tok,
                        string.Format("the type of the other operand is a {0} of non-null elements, so the {1}inclusion test of 'null' will always return '{2}'",
                        what, sense ? "" : "non-", sense ? "false" : "true"));
                    }
                    break;
                  }
                case BinaryExpr.ResolvedOpcode.NotInMap:
                  goto case BinaryExpr.ResolvedOpcode.InMap;
                case BinaryExpr.ResolvedOpcode.InMap: {
                    var ty = other.Type.NormalizeExpand();
                    if (((MapType)ty).Domain.IsNonNullRefType) {
                      resolver.reporter.Warning(MessageSource.Resolver, e.tok,
                        string.Format("the type of the other operand is a map to a non-null type, so the inclusion test of 'null' will always return '{0}'",
                        sense ? "false" : "true"));
                    }
                    break;
                  }
                default:
                  break;
              }
            }
          } else if (expr is NegationExpression) {
            var e = (NegationExpression)expr;
            Expression zero;
            if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
              zero = new LiteralExpr(e.tok, Basetypes.BigDec.ZERO);
            } else {
              Contract.Assert(e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType);
              zero = new LiteralExpr(e.tok, 0);
            }
            zero.Type = expr.Type;
            var subtract = new BinaryExpr(e.tok, BinaryExpr.Opcode.Sub, zero, e.E);
            subtract.Type = expr.Type;
            subtract.ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;
            e.ResolvedExpression = subtract;
          }
        }
      }
      public static bool IsDetermined(Type t) {
        Contract.Requires(t != null);
        Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);
        // all other proxies indicate the type has not yet been determined, provided their type parameters have been
        return !(t is TypeProxy) && t.TypeArgs.All(tt => IsDetermined(tt.Normalize()));
      }
      ISet<TypeProxy> UnderspecifiedTypeProxies = new HashSet<TypeProxy>();
      public bool CheckTypeIsDetermined(IToken tok, Type t, string what) {
        Contract.Requires(tok != null);
        Contract.Requires(t != null);
        Contract.Requires(what != null);
        t = t.NormalizeExpand();

        if (t is TypeProxy) {
          var proxy = (TypeProxy)t;
          if (!UnderspecifiedTypeProxies.Contains(proxy)) {
            // report an error for this TypeProxy only once
            resolver.reporter.Error(MessageSource.Resolver, tok, "the type of this {0} is underspecified", what);
            UnderspecifiedTypeProxies.Add(proxy);
          }
          return false;
        }
        // Recurse on type arguments:
        return t.TypeArgs.All(rg => CheckTypeIsDetermined(tok, rg, what));
      }
      public void CheckTypeArgsContainNoOrdinal(IToken tok, Type t) {
        Contract.Requires(tok != null);
        Contract.Requires(t != null);
        t = t.NormalizeExpand();
        t.TypeArgs.Iter(rg => CheckContainsNoOrdinal(tok, rg, "an ORDINAL type is not allowed to be used as a type argument"));
      }
      public void CheckContainsNoOrdinal(IToken tok, Type t, string errMsg) {
        Contract.Requires(tok != null);
        Contract.Requires(t != null);
        Contract.Requires(errMsg != null);
        t = t.NormalizeExpand();
        if (t.IsBigOrdinalType) {
          resolver.reporter.Error(MessageSource.Resolver, tok, errMsg);
        }
        t.TypeArgs.Iter(rg => CheckContainsNoOrdinal(tok, rg, errMsg));
      }
    }
#endregion CheckTypeInference

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckExpression --------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region CheckExpression
    /// <summary>
    /// This method computes ghost interests in the statement portion of StmtExpr's and
    /// checks for hint restrictions in any CalcStmt.
    /// </summary>
    void CheckExpression(Expression expr, Resolver resolver, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Requires(resolver != null);
      Contract.Requires(codeContext != null);
      var v = new CheckExpression_Visitor(resolver, codeContext);
      v.Visit(expr);
    }
    /// <summary>
    /// This method computes ghost interests in the statement portion of StmtExpr's and
    /// checks for hint restrictions in any CalcStmt.
    /// </summary>
    void CheckExpression(Statement stmt, Resolver resolver, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolver != null);
      Contract.Requires(codeContext != null);
      var v = new CheckExpression_Visitor(resolver, codeContext);
      v.Visit(stmt);
    }
    class CheckExpression_Visitor : ResolverBottomUpVisitor
    {
      readonly ICodeContext CodeContext;
      public CheckExpression_Visitor(Resolver resolver, ICodeContext codeContext)
        : base(resolver) {
        Contract.Requires(resolver != null);
        Contract.Requires(codeContext != null);
        CodeContext = codeContext;
      }
      protected override void VisitOneExpr(Expression expr) {
        if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          resolver.ComputeGhostInterest(e.S, true, CodeContext);
        }
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is CalcStmt) {
          var s = (CalcStmt)stmt;
          foreach (var h in s.Hints) {
            resolver.CheckHintRestrictions(h, new HashSet<LocalVariable>());
          }
        }
      }
    }
#endregion

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckTailRecursive -----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region CheckTailRecursive
    enum TailRecursionStatus
    {
      NotTailRecursive, // contains code that makes the enclosing method body not tail recursive (in way that is supported)
      CanBeFollowedByAnything, // the code just analyzed does not do any recursive calls
      TailCallSpent, // the method body is tail recursive, provided that all code that follows it in the method body is ghost
    }

    /// <summary>
    /// Checks if "stmts" can be considered tail recursive, and (provided "reportsError" is true) reports an error if not.
    /// Note, the current implementation is rather conservative in its analysis; upon need, the
    /// algorithm could be improved.
    /// In the current implementation, "enclosingMethod" is not allowed to be a mutually recursive method.
    ///
    /// The incoming value of "tailCall" is not used, but it's nevertheless a 'ref' parameter to allow the
    /// body to return the incoming value or to omit assignments to it.
    /// If the return value is CanBeFollowedByAnything, "tailCall" is unchanged.
    /// If the return value is TailCallSpent, "tailCall" shows one of the calls where the tail call was spent.  (Note,
    /// there could be several if the statements have branches.)
    /// If the return value is NoTailRecursive, "tailCall" could be anything.  In this case, an error
    /// message has been reported (provided "reportsErrors" is true).
    /// </summary>
    TailRecursionStatus CheckTailRecursive(List<Statement> stmts, Method enclosingMethod, ref CallStmt tailCall, bool reportErrors) {
      Contract.Requires(stmts != null);
      var status = TailRecursionStatus.CanBeFollowedByAnything;
      foreach (var s in stmts) {
        if (!s.IsGhost) {
          if (s is ReturnStmt && ((ReturnStmt)s).hiddenUpdate == null) {
            return status;
          }
          if (status == TailRecursionStatus.TailCallSpent) {
            // a tail call cannot be followed by non-ghost code
            if (reportErrors) {
              reporter.Error(MessageSource.Resolver, tailCall.Tok, "this recursive call is not recognized as being tail recursive, because it is followed by non-ghost code");
            }
            return TailRecursionStatus.NotTailRecursive;
          }
          status = CheckTailRecursive(s, enclosingMethod, ref tailCall, reportErrors);
          if (status == TailRecursionStatus.NotTailRecursive) {
            return status;
          }
        }
      }
      return status;
    }

    void DetermineTailRecursion(Function f) {
      Contract.Requires(f != null);
      bool tail = true;
      if (Attributes.ContainsBool(f.Attributes, "tailrecursion", ref tail) && tail) {
        reporter.Error(MessageSource.Resolver, f.tok, "sorry, tail-call functions are not supported");
      }
    }

    void DetermineTailRecursion(Method m) {
      Contract.Requires(m != null);
      bool tail = true;
      bool hasTailRecursionPreference = Attributes.ContainsBool(m.Attributes, "tailrecursion", ref tail);
      if (hasTailRecursionPreference && !tail) {
        // the user specifically requested no tail recursion, so do nothing else
      } else if (hasTailRecursionPreference && tail && m.IsGhost) {
        reporter.Error(MessageSource.Resolver, m.tok, "tail recursion can be specified only for methods that will be compiled, not for ghost methods");
      } else {
        var module = m.EnclosingClass.Module;
        var sccSize = module.CallGraph.GetSCCSize(m);
        if (hasTailRecursionPreference && 2 <= sccSize) {
          reporter.Error(MessageSource.Resolver, m.tok, "sorry, tail-call optimizations are not supported for mutually recursive methods");
        } else if (hasTailRecursionPreference || sccSize == 1) {
          CallStmt tailCall = null;
          var status = CheckTailRecursive(m.Body.Body, m, ref tailCall, hasTailRecursionPreference);
          if (status != TailRecursionStatus.NotTailRecursive) {
            m.IsTailRecursive = true;
            if (tailCall != null) {
              // this means there was at least one recursive call
              reporter.Info(MessageSource.Resolver, m.tok, "tail recursive");
            }
          }
        }
      }
    }

    /// <summary>
    /// See CheckTailRecursive(List Statement, ...), including its description of "tailCall".
    /// In the current implementation, "enclosingMethod" is not allowed to be a mutually recursive method.
    /// </summary>
    TailRecursionStatus CheckTailRecursive(Statement stmt, Method enclosingMethod, ref CallStmt tailCall, bool reportErrors) {
      Contract.Requires(stmt != null);
      if (stmt.IsGhost) {
        return TailRecursionStatus.NotTailRecursive;
      }
      if (stmt is PrintStmt) {
      } else if (stmt is RevealStmt) {
      } else if (stmt is BreakStmt) {
      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        if (s.hiddenUpdate != null) {
          return CheckTailRecursive(s.hiddenUpdate, enclosingMethod, ref tailCall, reportErrors);
        }
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        var tRhs = s.Rhs as TypeRhs;
        if (tRhs != null && tRhs.InitCall != null && tRhs.InitCall.Method == enclosingMethod) {
          // It's a recursive call.  However, it is not a tail call, because after the "new" allocation
          // and init call have taken place, the newly allocated object has yet to be assigned to
          // the LHS of the assignment statement.
          if (reportErrors) {
            reporter.Error(MessageSource.Resolver, tRhs.InitCall.Tok,
              "the recursive call to '{0}' is not tail recursive, because the assignment of the LHS happens after the call",
              tRhs.InitCall.Method.Name);
          }
          return TailRecursionStatus.NotTailRecursive;
        }
      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        if (s.Body != null) {
          return CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
        }
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        if (s.Method == enclosingMethod) {
          // It's a recursive call.  It can be considered a tail call only if the LHS of the call are the
          // formal out-parameters of the method
          for (int i = 0; i < s.Lhs.Count; i++) {
            var formal = enclosingMethod.Outs[i];
            if (!formal.IsGhost) {
              var lhs = s.Lhs[i] as IdentifierExpr;
              if (lhs != null && lhs.Var == formal) {
                // all is good
              } else {
                if (reportErrors) {
                  reporter.Error(MessageSource.Resolver, s.Tok,
                    "the recursive call to '{0}' is not tail recursive because the actual out-parameter{1} is not the formal out-parameter '{2}'",
                    s.Method.Name, s.Lhs.Count == 1 ? "" : " " + i, formal.Name);
                }
                return TailRecursionStatus.NotTailRecursive;
              }
            }
          }
          // Moreover, it can be considered a tail recursive call only if the type parameters are the same
          // as in the caller.
          var classTypeParameterCount = s.Method.EnclosingClass.TypeArgs.Count;
          Contract.Assert(s.MethodSelect.TypeApplication.Count == classTypeParameterCount + s.Method.TypeArgs.Count);
          for (int i = 0; i < s.Method.TypeArgs.Count; i++) {
            var formal = s.Method.TypeArgs[i];
            var actual = s.MethodSelect.TypeApplication[classTypeParameterCount + i].AsTypeParameter;
            if (formal != actual) {
              if (reportErrors) {
                reporter.Error(MessageSource.Resolver, s.Tok,
                  "the recursive call to '{0}' is not tail recursive because the actual type parameter{1} is not the formal type parameter '{2}'",
                  s.Method.Name, s.Method.TypeArgs.Count == 1 ? "" : " " + i, formal.Name);
              }
              return TailRecursionStatus.NotTailRecursive;
            }
          }
          tailCall = s;
          return TailRecursionStatus.TailCallSpent;
        }
      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        return CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        var stThen = CheckTailRecursive(s.Thn, enclosingMethod, ref tailCall, reportErrors);
        if (stThen == TailRecursionStatus.NotTailRecursive) {
          return stThen;
        }
        var stElse = s.Els == null ? TailRecursionStatus.CanBeFollowedByAnything : CheckTailRecursive(s.Els, enclosingMethod, ref tailCall, reportErrors);
        if (stElse == TailRecursionStatus.NotTailRecursive) {
          return stElse;
        } else if (stThen == TailRecursionStatus.TailCallSpent || stElse == TailRecursionStatus.TailCallSpent) {
          return TailRecursionStatus.TailCallSpent;
        }
      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        var status = TailRecursionStatus.CanBeFollowedByAnything;
        foreach (var alt in s.Alternatives) {
          var st = CheckTailRecursive(alt.Body, enclosingMethod, ref tailCall, reportErrors);
          if (st == TailRecursionStatus.NotTailRecursive) {
            return st;
          } else if (st == TailRecursionStatus.TailCallSpent) {
            status = st;
          }
        }
        return status;
      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        var status = TailRecursionStatus.NotTailRecursive;
        if (s.Body != null) {
          status = CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
        }
        if (status != TailRecursionStatus.CanBeFollowedByAnything) {
          if (status == TailRecursionStatus.NotTailRecursive) {
            // an error has already been reported
          } else if (reportErrors) {
            reporter.Error(MessageSource.Resolver, tailCall.Tok, "a recursive call inside a loop is not recognized as being a tail call");
          }
          return TailRecursionStatus.NotTailRecursive;
        }
      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        foreach (var alt in s.Alternatives) {
          var status = CheckTailRecursive(alt.Body, enclosingMethod, ref tailCall, reportErrors);
          if (status != TailRecursionStatus.CanBeFollowedByAnything) {
            if (status == TailRecursionStatus.NotTailRecursive) {
              // an error has already been reported
            } else if (reportErrors) {
              reporter.Error(MessageSource.Resolver, tailCall.Tok, "a recursive call inside a loop is not recognized as being a tail call");
            }
            return TailRecursionStatus.NotTailRecursive;
          }
        }
      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        var status = TailRecursionStatus.NotTailRecursive;
        if (s.Body != null) {
          status = CheckTailRecursive(s.Body, enclosingMethod, ref tailCall, reportErrors);
        }
        if (status != TailRecursionStatus.CanBeFollowedByAnything) {
          if (status == TailRecursionStatus.NotTailRecursive) {
            // an error has already been reported
          } else if (reportErrors) {
            reporter.Error(MessageSource.Resolver, tailCall.Tok, "a recursive call inside a forall statement is not a tail call");
          }
          return TailRecursionStatus.NotTailRecursive;
        }
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        var status = TailRecursionStatus.CanBeFollowedByAnything;
        foreach (var kase in s.Cases) {
          var st = CheckTailRecursive(kase.Body, enclosingMethod, ref tailCall, reportErrors);
          if (st == TailRecursionStatus.NotTailRecursive) {
            return st;
          } else if (st == TailRecursionStatus.TailCallSpent) {
            status = st;
          }
        }
        return status;
      } else if (stmt is AssignSuchThatStmt) {
      } else if (stmt is AssignOrReturnStmt) {
        // TODO this should be the conservative choice, but probably we can consider this to be tail-recursive
        // under some conditions? However, how does this interact with compiling to exceptions?
        return TailRecursionStatus.NotTailRecursive;
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        return CheckTailRecursive(s.ResolvedStatements, enclosingMethod, ref tailCall, reportErrors);
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Update != null) {
          return CheckTailRecursive(s.Update, enclosingMethod, ref tailCall, reportErrors);
        }
      } else if (stmt is LetStmt) {
      } else {
        Contract.Assert(false);  // unexpected statement type
      }
      return TailRecursionStatus.CanBeFollowedByAnything;
    }
#endregion CheckTailRecursive

    // ------------------------------------------------------------------------------------------------------
    // ----- FuelAdjustmentChecks ---------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region FuelAdjustmentChecks

    protected void CheckForFuelAdjustments(IToken tok, Attributes attrs, ModuleDefinition currentModule) {
      List<List<Expression>> results = Attributes.FindAllExpressions(attrs, "fuel");

      if (results != null) {
        foreach (List<Expression> args in results) {
          if (args != null && args.Count >= 2) {
            // Try to extract the function from the first argument
            MemberSelectExpr selectExpr = args[0].Resolved as MemberSelectExpr;
            if (selectExpr != null) {
              Function f = selectExpr.Member as Function;
              if (f != null) {
                f.IsFueled = true;
                if (f.IsProtected && currentModule != f.EnclosingClass.Module) {
                  reporter.Error(MessageSource.Resolver, tok, "cannot adjust fuel for protected function {0} from another module", f.Name);
                }
                if (args.Count >= 3) {
                  LiteralExpr literalLow = args[1] as LiteralExpr;
                  LiteralExpr literalHigh = args[2] as LiteralExpr;
                  if (literalLow != null && literalLow.Value is BigInteger && literalHigh != null && literalHigh.Value is BigInteger) {
                    BigInteger low = (BigInteger)literalLow.Value;
                    BigInteger high = (BigInteger)literalHigh.Value;
                    if (!(high == low + 1 || (low == 0 && high == 0))) {
                      reporter.Error(MessageSource.Resolver, tok, "fuel setting for function {0} must have high value == 1 + low value", f.Name);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    public class FuelAdjustment_Context
    {
      public ModuleDefinition currentModule;
      public FuelAdjustment_Context(ModuleDefinition currentModule) {
        this.currentModule = currentModule;
      }
    }

    class FuelAdjustment_Visitor : ResolverTopDownVisitor<FuelAdjustment_Context>
    {
      public FuelAdjustment_Visitor(Resolver resolver)
        : base(resolver) {
        Contract.Requires(resolver != null);
      }

      protected override bool VisitOneStmt(Statement stmt, ref FuelAdjustment_Context st) {
        resolver.CheckForFuelAdjustments(stmt.Tok, stmt.Attributes, st.currentModule);
        return true;
      }
    }

#endregion FuelAdjustmentChecks

    // ------------------------------------------------------------------------------------------------------
    // ----- FixpointPredicateChecks ------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region FixpointPredicateChecks
    enum CallingPosition { Positive, Negative, Neither }
    static CallingPosition Invert(CallingPosition cp) {
      switch (cp) {
        case CallingPosition.Positive: return CallingPosition.Negative;
        case CallingPosition.Negative: return CallingPosition.Positive;
        default: return CallingPosition.Neither;
      }
    }

    class FindFriendlyCalls_Visitor : ResolverTopDownVisitor<CallingPosition>
    {
      public readonly bool IsCoContext;
      public readonly bool ContinuityIsImportant;
      public FindFriendlyCalls_Visitor(Resolver resolver, bool co, bool continuityIsImportant)
        : base(resolver)
      {
        Contract.Requires(resolver != null);
        this.IsCoContext = co;
        this.ContinuityIsImportant = continuityIsImportant;
      }

      protected override bool VisitOneExpr(Expression expr, ref CallingPosition cp) {
        if (expr is UnaryOpExpr) {
          var e = (UnaryOpExpr)expr;
          if (e.Op == UnaryOpExpr.Opcode.Not) {
            // for the sub-parts, use Invert(cp)
            cp = Invert(cp);
            return true;
          }
        } else if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          switch (e.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.And:
            case BinaryExpr.ResolvedOpcode.Or:
              return true;  // do the sub-parts with the same "cp"
            case BinaryExpr.ResolvedOpcode.Imp:
              Visit(e.E0, Invert(cp));
              Visit(e.E1, cp);
              return false;  // don't recurse (again) on the sub-parts
            default:
              break;
          }
        } else if (expr is MatchExpr) {
          var e = (MatchExpr)expr;
          Visit(e.Source, CallingPosition.Neither);
          var theCp = cp;
          e.Cases.Iter(kase => Visit(kase.Body, theCp));
          return false;
        } else if (expr is ITEExpr) {
          var e = (ITEExpr)expr;
          Visit(e.Test, CallingPosition.Neither);
          Visit(e.Thn, cp);
          Visit(e.Els, cp);
          return false;
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          foreach (var rhs in e.RHSs) {
            Visit(rhs, CallingPosition.Neither);
          }
          var cpBody = cp;
          if (!e.Exact) {
            // a let-such-that expression introduces an existential that may depend on the _k in an inductive/co predicate, so we disallow recursive calls in the body of the let-such-that
            if (IsCoContext && cp == CallingPosition.Positive) {
              cpBody = CallingPosition.Neither;
            } else if (!IsCoContext && cp == CallingPosition.Negative) {
              cpBody = CallingPosition.Neither;
            }
          }
          Visit(e.Body, cpBody);
          return false;
        } else if (expr is QuantifierExpr) {
          var e = (QuantifierExpr)expr;
          Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
          var cpos = IsCoContext ? cp : Invert(cp);
          if (ContinuityIsImportant) {
            if ((cpos == CallingPosition.Positive && e is ExistsExpr) || (cpos == CallingPosition.Negative && e is ForallExpr)) {
              if (e.Bounds.Exists(bnd => bnd == null || (bnd.Virtues & ComprehensionExpr.BoundedPool.PoolVirtues.Finite) == 0)) {
                // To ensure continuity of fixpoint predicates, don't allow calls under an existential (resp. universal) quantifier
                // for co-predicates (resp. inductive predicates).
                cp = CallingPosition.Neither;
              }
            }
          }
          Visit(e.LogicalBody(), cp);
          return false;
        } else if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          Visit(e.E, cp);
          Visit(e.S, CallingPosition.Neither);
          return false;
        } else if (expr is ConcreteSyntaxExpression) {
          // do the sub-parts with the same "cp"
          return true;
        }
        // do the sub-parts with cp := Neither
        cp = CallingPosition.Neither;
        return true;
      }
    }


    void KNatMismatchError(IToken tok, string contextName, FixpointPredicate.KType contextK, FixpointPredicate.KType calleeK) {
      var hint = contextK == FixpointPredicate.KType.Unspecified ? string.Format(" (perhaps try declaring '{0}' as '{0}[nat]')", contextName) : "";
      reporter.Error(MessageSource.Resolver, tok,
        "this call does not type check, because the context uses a _k parameter of type {0} whereas the callee uses a _k parameter of type {1}{2}",
        contextK == FixpointPredicate.KType.Nat ? "nat" : "ORDINAL",
        calleeK == FixpointPredicate.KType.Nat ? "nat" : "ORDINAL",
        hint);
    }

    class FixpointPredicateChecks_Visitor : FindFriendlyCalls_Visitor
    {
      readonly FixpointPredicate context;
      public FixpointPredicateChecks_Visitor(Resolver resolver, FixpointPredicate context)
        : base(resolver, context is CoPredicate, context.KNat) {
        Contract.Requires(resolver != null);
        Contract.Requires(context != null);
        this.context = context;
      }
      protected override bool VisitOneExpr(Expression expr, ref CallingPosition cp) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          if (ModuleDefinition.InSameSCC(context, e.Function)) {
            var article = context is InductivePredicate ? "an" : "a";
            // we're looking at a recursive call
            if (!(context is InductivePredicate ? e.Function is InductivePredicate : e.Function is CoPredicate)) {
              resolver.reporter.Error(MessageSource.Resolver, e, "a recursive call from {0} {1} can go only to other {1}s", article, context.WhatKind);
            } else if (context.KNat != ((FixpointPredicate)e.Function).KNat) {
              resolver.KNatMismatchError(e.tok, context.Name, context.TypeOfK, ((FixpointPredicate)e.Function).TypeOfK);
            } else if (cp != CallingPosition.Positive) {
              var msg = string.Format("{0} {1} can be called recursively only in positive positions", article, context.WhatKind);
              if (ContinuityIsImportant && cp == CallingPosition.Neither) {
                // this may be inside an non-friendly quantifier
                msg += string.Format(" and cannot sit inside an unbounded {0} quantifier", context is InductivePredicate ? "universal" : "existential");
              } else {
                // we don't care about the continuity restriction or
                // the fixpoint-call is not inside an quantifier, so don't bother mentioning the part of existentials/universals in the error message
              }
              resolver.reporter.Error(MessageSource.Resolver, e, msg);
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.Yes;
              resolver.reporter.Info(MessageSource.Resolver, e.tok, e.Function.Name + "#[_k - 1]");
            }
          }
          // do the sub-parts with cp := Neither
          cp = CallingPosition.Neither;
          return true;
        }
        return base.VisitOneExpr(expr, ref cp);
      }
      protected override bool VisitOneStmt(Statement stmt, ref CallingPosition st) {
        if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          if (ModuleDefinition.InSameSCC(context, s.Method)) {
            // we're looking at a recursive call
            var article = context is InductivePredicate ? "an" : "a";
            resolver.reporter.Error(MessageSource.Resolver, stmt.Tok, "a recursive call from {0} {1} can go only to other {1}s", article, context.WhatKind);
          }
          // do the sub-parts with the same "cp"
          return true;
        } else {
          return base.VisitOneStmt(stmt, ref st);
        }
      }
    }

    void FixpointPredicateChecks(Expression expr, FixpointPredicate context, CallingPosition cp) {
      Contract.Requires(expr != null);
      Contract.Requires(context != null);
      var v = new FixpointPredicateChecks_Visitor(this, context);
      v.Visit(expr, cp);
    }
#endregion FixpointPredicateChecks

    // ------------------------------------------------------------------------------------------------------
    // ----- FixpointLemmaChecks ----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region FixpointLemmaChecks
    class FixpointLemmaChecks_Visitor : ResolverBottomUpVisitor
    {
      FixpointLemma context;
      public FixpointLemmaChecks_Visitor(Resolver resolver, FixpointLemma context)
        : base(resolver) {
        Contract.Requires(resolver != null);
        Contract.Requires(context != null);
        this.context = context;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          if (s.Method is FixpointLemma || s.Method is PrefixLemma) {
            // all is cool
          } else {
            // the call goes from a fixpoint-lemma context to a non-fixpoint-lemma callee
            if (ModuleDefinition.InSameSCC(context, s.Method)) {
              // we're looking at a recursive call (to a non-fixpoint-lemma)
              var article = context is InductiveLemma ? "an" : "a";
              resolver.reporter.Error(MessageSource.Resolver, s.Tok, "a recursive call from {0} {1} can go only to other {1}s and prefix lemmas", article, context.WhatKind);
            }
          }
        }
      }
      protected override void VisitOneExpr(Expression expr)
      {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          // the call goes from a colemma context to a non-colemma callee
          if (ModuleDefinition.InSameSCC(context, e.Function)) {
            // we're looking at a recursive call (to a non-colemma)
            resolver.reporter.Error(MessageSource.Resolver, e.tok, "a recursive call from a colemma can go only to other colemmas and prefix lemmas");
          }
        }
      }
    }
    void FixpointLemmaChecks(Statement stmt, FixpointLemma context) {
      Contract.Requires(stmt != null);
      Contract.Requires(context != null);
      var v = new FixpointLemmaChecks_Visitor(this, context);
      v.Visit(stmt);
    }
#endregion FixpointLemmaChecks

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckEqualityTypes -----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region CheckEqualityTypes
    class CheckEqualityTypes_Visitor : ResolverTopDownVisitor<bool>
    {
      public CheckEqualityTypes_Visitor(Resolver resolver)
        : base(resolver) {
        Contract.Requires(resolver != null);
      }
      protected override bool VisitOneStmt(Statement stmt, ref bool st) {
        if (stmt.IsGhost) {
          return false;  // no need to recurse to sub-parts, since all sub-parts must be ghost as well
        } else if (stmt is VarDeclStmt) {
          var s = (VarDeclStmt)stmt;
          foreach (var v in s.Locals) {
            if (!v.IsGhost) {
              CheckEqualityTypes_Type(v.Tok, v.Type);
            }
          }
        } else if (stmt is LetStmt) {
          var s = (LetStmt)stmt;
          foreach (var v in s.LocalVars) {
            CheckEqualityTypes_Type(v.Tok, v.Type);
          }
        } else if (stmt is AssignStmt) {
          var s = (AssignStmt)stmt;
          var tRhs = s.Rhs as TypeRhs;
          if (tRhs != null && tRhs.Type is UserDefinedType) {
            var udt = (UserDefinedType)tRhs.Type;
            var formalTypeArgs = udt.ResolvedClass.TypeArgs;
            var actualTypeArgs = tRhs.Type.TypeArgs;
            Contract.Assert(formalTypeArgs.Count == actualTypeArgs.Count);
            var i = 0;
            foreach (var argType in actualTypeArgs) {
              var formalTypeArg = formalTypeArgs[i];
              string whatIsWrong, hint;
              if (!CheckCharacteristics(formalTypeArg.Characteristics, argType, out whatIsWrong, out hint)) {
                resolver.reporter.Error(MessageSource.Resolver, tRhs.Tok, "type parameter{0} ({1}) passed to type {2} must support {4} (got {3}){5}",
                  actualTypeArgs.Count == 1 ? "" : " " + i, formalTypeArg.Name, udt.ResolvedClass.Name, argType, whatIsWrong, hint);
              }
              CheckEqualityTypes_Type(tRhs.Tok, argType);
              i++;
            }
          }
        } else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          // don't recurse on the specification parts, which are ghost
          if (s.Guard != null) {
            Visit(s.Guard, st);
          }
          // don't recurse on the body, if it's a dirty loop
          if (s.Body != null) {
            Visit(s.Body, st);
          }
          return false;
        } else if (stmt is AlternativeLoopStmt) {
          var s = (AlternativeLoopStmt)stmt;
          // don't recurse on the specification parts, which are ghost
          foreach (var alt in s.Alternatives) {
            Visit(alt.Guard, st);
            foreach (var ss in alt.Body) {
              Visit(ss, st);
            }
          }
          return false;
        } else if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          var subst = s.MethodSelect.TypeArgumentSubstitutions();
          Contract.Assert(s.Method.TypeArgs.Count <= subst.Count);
          var i = 0;
          foreach (var formalTypeArg in s.Method.TypeArgs) {
            var actualTypeArg = subst[formalTypeArg];
            CheckEqualityTypes_Type(s.Tok, actualTypeArg);
            string whatIsWrong, hint;
            if (!CheckCharacteristics(formalTypeArg.Characteristics, actualTypeArg, out whatIsWrong, out hint)) {
              resolver.reporter.Error(MessageSource.Resolver, s.Tok, "type parameter{0} ({1}) passed to method {2} must support {4} (got {3}){5}",
                s.Method.TypeArgs.Count == 1 ? "" : " " + i, formalTypeArg.Name, s.Method.Name, actualTypeArg, whatIsWrong, hint);
            }
            i++;
          }
          // recursively visit all subexpressions (which are all actual parameters) passed in for non-ghost formal parameters
          Contract.Assert(s.Lhs.Count == s.Method.Outs.Count);
          i = 0;
          foreach (var ee in s.Lhs) {
            if (!s.Method.Outs[i].IsGhost) {
              Visit(ee, st);
            }
            i++;
          }
          Visit(s.Receiver, st);
          Contract.Assert(s.Args.Count == s.Method.Ins.Count);
          i = 0;
          foreach (var ee in s.Args) {
            if (!s.Method.Ins[i].IsGhost) {
              Visit(ee, st);
            }
            i++;
          }
          return false;  // we've done what there is to be done
        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          foreach (var v in s.BoundVars) {
            CheckEqualityTypes_Type(v.Tok, v.Type);
          }
          // do substatements and subexpressions, except attributes and ensures clauses, since they are not compiled
          foreach (var ss in s.SubStatements) {
            Visit(ss, st);
          }
          if (s.Range != null) {
            Visit(s.Range, st);
          }
          return false;  // we're done
        }
        return true;
      }
      bool CheckCharacteristics(TypeParameter.TypeParameterCharacteristics formal, Type actual, out string whatIsWrong, out string hint) {
        Contract.Ensures(Contract.Result<bool>() || (Contract.ValueAtReturn(out whatIsWrong) != null && Contract.ValueAtReturn(out hint) != null));
        if (formal.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified && !actual.SupportsEquality) {
          whatIsWrong = "equality";
          hint = TypeEqualityErrorMessageHint(actual);
          return false;
        }
        if (formal.MustSupportZeroInitialization && !Compiler.HasZeroInitializer(actual)) {
          whatIsWrong = "zero initialization";
          hint = "";
          return false;
        }
        whatIsWrong = null;
        hint = null;
        return true;
      }
      protected override bool VisitOneExpr(Expression expr, ref bool st) {
        if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          var t0 = e.E0.Type.NormalizeExpand();
          var t1 = e.E1.Type.NormalizeExpand();
          switch (e.Op) {
            case BinaryExpr.Opcode.Eq:
            case BinaryExpr.Opcode.Neq:
              // First, check some special cases that can always be compared against--for example, a datatype value (like Nil) that takes no parameters
              if (CanCompareWith(e.E0)) {
                // that's cool
              } else if (CanCompareWith(e.E1)) {
                // oh yeah!
              } else if (!t0.SupportsEquality) {
                resolver.reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
              } else if (!t1.SupportsEquality) {
                resolver.reporter.Error(MessageSource.Resolver, e.E1, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t1, TypeEqualityErrorMessageHint(t1));
              }
              break;
            default:
              switch (e.ResolvedOp) {
                // Note, all operations on sets, multisets, and maps are guaranteed to work because of restrictions placed on how
                // these types are instantiated.  (Except: This guarantee does not apply to equality on maps, because the Range type
                // of maps is not restricted, only the Domain type.  However, the equality operator is checked above.)
                case BinaryExpr.ResolvedOpcode.InSeq:
                case BinaryExpr.ResolvedOpcode.NotInSeq:
                case BinaryExpr.ResolvedOpcode.Prefix:
                case BinaryExpr.ResolvedOpcode.ProperPrefix:
                  if (!t1.SupportsEquality) {
                    resolver.reporter.Error(MessageSource.Resolver, e.E1, "{0} can only be applied to expressions of sequence types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t1, TypeEqualityErrorMessageHint(t1));
                  } else if (!t0.SupportsEquality) {
                    if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSeq) {
                      resolver.reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
                    } else {
                      resolver.reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of sequence types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
                    }
                  }
                  break;
                default:
                  break;
              }
              break;
          }
        } else if (expr is ComprehensionExpr) {
          var e = (ComprehensionExpr)expr;
          foreach (var bv in e.BoundVars) {
            CheckEqualityTypes_Type(bv.tok, bv.Type);
          }
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          foreach (var bv in e.BoundVars) {
            CheckEqualityTypes_Type(bv.tok, bv.Type);
          }
        } else if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          if (e.Member is Function || e.Member is Method) {
            var i = 0;
            foreach (var tp in ((ICallable)e.Member).TypeArgs) {
              var actualTp = e.TypeApplication[e.Member.EnclosingClass.TypeArgs.Count + i];
              CheckEqualityTypes_Type(e.tok, actualTp);
              string whatIsWrong, hint;
              if (!CheckCharacteristics(tp.Characteristics, actualTp, out whatIsWrong, out hint)) {
                resolver.reporter.Error(MessageSource.Resolver, e.tok, "type parameter{0} ({1}) passed to {2} '{3}' must support {5} (got {4}){6}",
                  ((ICallable)e.Member).TypeArgs.Count == 1 ? "" : " " + i, tp.Name, e.Member.WhatKind, e.Member.Name, actualTp, whatIsWrong, hint);
              }
              i++;
            }
          }
        } else if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          Contract.Assert(e.Function.TypeArgs.Count <= e.TypeArgumentSubstitutions.Count);
          var i = 0;
          foreach (var formalTypeArg in e.Function.TypeArgs) {
            var actualTypeArg = e.TypeArgumentSubstitutions[formalTypeArg];
            CheckEqualityTypes_Type(e.tok, actualTypeArg);
            string whatIsWrong, hint;
            if (!CheckCharacteristics(formalTypeArg.Characteristics, actualTypeArg, out whatIsWrong, out hint)) {
              resolver.reporter.Error(MessageSource.Resolver, e.tok, "type parameter{0} ({1}) passed to function {2} must support {4} (got {3}){5}",
                e.Function.TypeArgs.Count == 1 ? "" : " " + i, formalTypeArg.Name, e.Function.Name, actualTypeArg, whatIsWrong, hint);
            }
            i++;
          }
          // recursively visit all subexpressions (which are all actual parameters) passed in for non-ghost formal parameters
          Visit(e.Receiver, st);
          Contract.Assert(e.Args.Count == e.Function.Formals.Count);
          i = 0;
          foreach (var ee in e.Args) {
            if (!e.Function.Formals[i].IsGhost) {
              Visit(ee, st);
            }
            i++;
          }
          return false;  // we've done what there is to be done
        } else if (expr is SetDisplayExpr || expr is MultiSetDisplayExpr || expr is MapDisplayExpr || expr is SeqConstructionExpr || expr is MultiSetFormingExpr || expr is StaticReceiverExpr) {
          // This catches other expressions whose type may potentially be illegal
          CheckEqualityTypes_Type(expr.tok, expr.Type);
        }
        return true;
      }

      private bool CanCompareWith(Expression expr) {
        Contract.Requires(expr != null);
        if (expr.Type.SupportsEquality) {
          return true;
        }
        expr = expr.Resolved;
        if (expr is DatatypeValue) {
          var e = (DatatypeValue)expr;
          for (int i = 0; i < e.Ctor.Formals.Count; i++) {
            if (e.Ctor.Formals[i].IsGhost) {
              return false;
            } else if (!CanCompareWith(e.Arguments[i])) {
              return false;
            }
          }
          return true;
        } else if (expr is DisplayExpression) {
          var e = (DisplayExpression)expr;
          return e.Elements.Count == 0;
        } else if (expr is MapDisplayExpr) {
          var e = (MapDisplayExpr)expr;
          return e.Elements.Count == 0;
        }
        return false;
      }

      public void CheckEqualityTypes_Type(IToken tok, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(type != null);
        type = type.Normalize();  // we only do a .Normalize() here, because we want to keep stop at any type synonym or subset type
        if (type is BasicType) {
          // fine
        } else if (type is SetType) {
          var st = (SetType)type;
          var argType = st.Arg;
          if (!argType.SupportsEquality) {
            resolver.reporter.Error(MessageSource.Resolver, tok, "{2}set argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType), st.Finite ? "" : "i");
          }
          CheckEqualityTypes_Type(tok, argType);

        } else if (type is MultiSetType) {
          var argType = ((MultiSetType)type).Arg;
          if (!argType.SupportsEquality) {
            resolver.reporter.Error(MessageSource.Resolver, tok, "multiset argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType));
          }
          CheckEqualityTypes_Type(tok, argType);

        } else if (type is MapType) {
          var mt = (MapType)type;
          if (!mt.Domain.SupportsEquality) {
            resolver.reporter.Error(MessageSource.Resolver, tok, "{2}map domain type must support equality (got {0}){1}", mt.Domain, TypeEqualityErrorMessageHint(mt.Domain), mt.Finite ? "" : "i");
          }
          CheckEqualityTypes_Type(tok, mt.Domain);
          CheckEqualityTypes_Type(tok, mt.Range);

        } else if (type is SeqType) {
          Type argType = ((SeqType)type).Arg;
          CheckEqualityTypes_Type(tok, argType);

        } else if (type is UserDefinedType) {
          var udt = (UserDefinedType)type;
          List<TypeParameter> formalTypeArgs = null;
          if (udt.ResolvedClass != null) {
            formalTypeArgs = udt.ResolvedClass.TypeArgs;
          } else if (udt.ResolvedParam is OpaqueType_AsParameter) {
            var t = (OpaqueType_AsParameter)udt.ResolvedParam;
            formalTypeArgs = t.TypeArgs;
          }
          if (formalTypeArgs == null) {
            Contract.Assert(udt.TypeArgs.Count == 0);
          } else {
            Contract.Assert(formalTypeArgs.Count == udt.TypeArgs.Count);
            var i = 0;
            foreach (var argType in udt.TypeArgs) {
              var formalTypeArg = formalTypeArgs[i];
              string whatIsWrong, hint;
              if (!CheckCharacteristics(formalTypeArg.Characteristics, argType, out whatIsWrong, out hint)) {
                resolver.reporter.Error(MessageSource.Resolver, tok, "type parameter{0} ({1}) passed to type {2} must support {4} (got {3}){5}",
                  udt.TypeArgs.Count == 1 ? "" : " " + i, formalTypeArg.Name, udt.ResolvedClass.Name, argType, whatIsWrong, hint);
              }
              CheckEqualityTypes_Type(tok, argType);
              i++;
            }
          }

        } else if (type is TypeProxy) {
          // the type was underconstrained; this is checked elsewhere, but it is not in violation of the equality-type test
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
        }
      }

      string TypeEqualityErrorMessageHint(Type argType) {
        Contract.Requires(argType != null);
        var tp = argType.AsTypeParameter;
        if (tp != null) {
          return string.Format(" (perhaps try declaring type parameter '{0}' on line {1} as '{0}(==)', which says it can only be instantiated with a type that supports equality)", tp.Name, tp.tok.line);
        }
        return "";
      }
    }
    void CheckEqualityTypes_Stmt(Statement stmt) {
      Contract.Requires(stmt != null);
      var v = new CheckEqualityTypes_Visitor(this);
      v.Visit(stmt, false);
    }
    void CheckEqualityTypes(Expression expr) {
      Contract.Requires(expr != null);
      var v = new CheckEqualityTypes_Visitor(this);
      v.Visit(expr, false);
    }
    public void CheckEqualityTypes_Type(IToken tok, Type type) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      var v = new CheckEqualityTypes_Visitor(this);
      v.CheckEqualityTypes_Type(tok, type);
    }

#endregion CheckEqualityTypes

    // ------------------------------------------------------------------------------------------------------
    // ----- ComputeGhostInterest ---------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region ComputeGhostInterest
    public void ComputeGhostInterest(Statement stmt, bool mustBeErasable, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      var visitor = new GhostInterest_Visitor(codeContext, this);
      visitor.Visit(stmt, mustBeErasable);
    }
    class GhostInterest_Visitor
    {
      readonly ICodeContext codeContext;
      readonly Resolver resolver;
      public GhostInterest_Visitor(ICodeContext codeContext, Resolver resolver) {
        Contract.Requires(codeContext != null);
        Contract.Requires(resolver != null);
        this.codeContext = codeContext;
        this.resolver = resolver;
      }
      protected void Error(Statement stmt, string msg, params object[] msgArgs) {
        Contract.Requires(stmt != null);
        Contract.Requires(msg != null);
        Contract.Requires(msgArgs != null);
        resolver.reporter.Error(MessageSource.Resolver, stmt, msg, msgArgs);
      }
      protected void Error(Expression expr, string msg, params object[] msgArgs) {
        Contract.Requires(expr != null);
        Contract.Requires(msg != null);
        Contract.Requires(msgArgs != null);
        resolver.reporter.Error(MessageSource.Resolver, expr, msg, msgArgs);
      }
      protected void Error(IToken tok, string msg, params object[] msgArgs) {
        Contract.Requires(tok != null);
        Contract.Requires(msg != null);
        Contract.Requires(msgArgs != null);
        resolver.reporter.Error(MessageSource.Resolver, tok, msg, msgArgs);
      }
      /// <summary>
      /// This method does three things, in order:
      /// 0. Sets .IsGhost to "true" if the statement is ghost.  This often depends on some guard of the statement
      ///    (like the guard of an "if" statement) or the LHS of the statement (if it is an assignment).
      ///    Note, if "mustBeErasable", then the statement is already in a ghost context.
      ///    statement itself is ghost) or and the statement assigns to a non-ghost field
      /// 1. Determines if the statement and all its subparts are legal under its computed .IsGhost setting.
      /// 2. ``Upgrades'' .IsGhost to "true" if, after investigation of the substatements of the statement, it
      ///    turns out that the statement can be erased during compilation.
      /// Notes:
      /// * Both step (0) and step (2) sets the .IsGhost field.  What step (0) does affects only the
      ///   rules of resolution, whereas step (2) makes a note for the later compilation phase.
      /// * It is important to do step (0) before step (1)--that is, it is important to set the statement's ghost
      ///   status before descending into its sub-statements--because break statements look at the ghost status of
      ///   its enclosing statements.
      /// * The method called by a StmtExpr must be ghost; however, this is checked elsewhere.  For
      ///   this reason, it is not necessary to visit all subexpressions, unless the subexpression
      ///   matter for the ghost checking/recording of "stmt".
      /// </summary>
      public void Visit(Statement stmt, bool mustBeErasable) {
        Contract.Requires(stmt != null);
        Contract.Assume(!codeContext.IsGhost || mustBeErasable);  // (this is really a precondition) codeContext.IsGhost ==> mustBeErasable

        if (stmt is PredicateStmt) {
          stmt.IsGhost = true;
          var assertStmt = stmt as AssertStmt;
          if (assertStmt != null && assertStmt.Proof != null) {
            Visit(assertStmt.Proof, true);
          }

        } else if (stmt is PrintStmt) {
          var s = (PrintStmt)stmt;
          if (mustBeErasable) {
            Error(stmt, "print statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
          } else {
            s.Args.Iter(resolver.CheckIsCompilable);
          }

        } else if (stmt is RevealStmt) {
          var s = (RevealStmt)stmt;
          s.ResolvedStatements.Iter(ss => Visit(ss, mustBeErasable));
          s.IsGhost = s.ResolvedStatements.All(ss => ss.IsGhost);
        } else if (stmt is BreakStmt) {
          var s = (BreakStmt)stmt;
          s.IsGhost = mustBeErasable;
          if (s.IsGhost && !s.TargetStmt.IsGhost) {
            var targetIsLoop = s.TargetStmt is WhileStmt || s.TargetStmt is AlternativeLoopStmt;
            Error(stmt, "ghost-context break statement is not allowed to break out of non-ghost " + (targetIsLoop ? "loop" : "structure"));
          }

        } else if (stmt is ProduceStmt) {
          var s = (ProduceStmt)stmt;
          var kind = stmt is YieldStmt ? "yield" : "return";
          if (mustBeErasable && !codeContext.IsGhost) {
            Error(stmt, "{0} statement is not allowed in this context (because it is guarded by a specification-only expression)", kind);
          }
          if (s.hiddenUpdate != null) {
            Visit(s.hiddenUpdate, mustBeErasable);
          }

        } else if (stmt is AssignSuchThatStmt) {
          var s = (AssignSuchThatStmt)stmt;
          s.IsGhost = mustBeErasable || s.AssumeToken != null || s.Lhss.Any(AssignStmt.LhsIsToGhost);
          if (mustBeErasable && !codeContext.IsGhost) {
            foreach (var lhs in s.Lhss) {
              var gk = AssignStmt.LhsIsToGhost_Which(lhs);
              if (gk != AssignStmt.NonGhostKind.IsGhost) {
                Error(lhs, "cannot assign to {0} in a ghost context", AssignStmt.NonGhostKind_To_String(gk));
              }
            }
          } else if (!mustBeErasable && s.AssumeToken == null && resolver.UsesSpecFeatures(s.Expr)) {
            foreach (var lhs in s.Lhss) {
              var gk = AssignStmt.LhsIsToGhost_Which(lhs);
              if (gk != AssignStmt.NonGhostKind.IsGhost) {
                Error(lhs, "{0} cannot be assigned a value that depends on a ghost", AssignStmt.NonGhostKind_To_String(gk));
              }
            }
          }

        } else if (stmt is UpdateStmt) {
          var s = (UpdateStmt)stmt;
          s.ResolvedStatements.Iter(ss => Visit(ss, mustBeErasable));
          s.IsGhost = s.ResolvedStatements.All(ss => ss.IsGhost);

        } else if (stmt is AssignOrReturnStmt) {
          stmt.IsGhost = false; // TODO when do we want to allow this feature in ghost code? Note that return changes control flow

        } else if (stmt is VarDeclStmt) {
          var s = (VarDeclStmt)stmt;
          if (mustBeErasable) {
            foreach (var local in s.Locals) {
              // a local variable in a specification-only context might as well be ghost
              local.IsGhost = true;
            }
          }
          s.IsGhost = (s.Update == null || s.Update.IsGhost) && s.Locals.All(v => v.IsGhost);
          if (s.Update != null) {
            Visit(s.Update, mustBeErasable);
          }

        } else if (stmt is LetStmt) {
          var s = (LetStmt)stmt;
          if (mustBeErasable) {
            foreach (var local in s.LocalVars) {
              local.IsGhost = true;
            }
          }
          s.IsGhost = s.LocalVars.All(v => v.IsGhost);

        } else if (stmt is AssignStmt) {
          var s = (AssignStmt)stmt;
          var lhs = s.Lhs.Resolved;
          var gk = AssignStmt.LhsIsToGhost_Which(lhs);
          if (gk == AssignStmt.NonGhostKind.IsGhost) {
            s.IsGhost = true;
            if (s.Rhs is TypeRhs) {
              Error(s.Rhs.Tok, "'new' is not allowed in ghost contexts");
            }
          } else if (gk == AssignStmt.NonGhostKind.Variable && codeContext.IsGhost) {
            // cool
          } else if (mustBeErasable) {
            Error(stmt, "Assignment to {0} is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)",
              AssignStmt.NonGhostKind_To_String(gk));
          } else {
            if (gk == AssignStmt.NonGhostKind.Field) {
              var mse = (MemberSelectExpr)lhs;
              resolver.CheckIsCompilable(mse.Obj);
            } else if (gk == AssignStmt.NonGhostKind.ArrayElement) {
              resolver.CheckIsCompilable(lhs);
            }
            if (s.Rhs is ExprRhs) {
              var rhs = (ExprRhs)s.Rhs;
              resolver.CheckIsCompilable(rhs.Expr);
            } else if (s.Rhs is HavocRhs) {
              // cool
            } else {
              var rhs = (TypeRhs)s.Rhs;
              if (rhs.ArrayDimensions != null) {
                rhs.ArrayDimensions.ForEach(resolver.CheckIsCompilable);
                if (rhs.ElementInit != null) {
                  resolver.CheckIsCompilable(rhs.ElementInit);
                }
                if (rhs.InitDisplay != null) {
                  rhs.InitDisplay.ForEach(resolver.CheckIsCompilable);
                }
              }
              if (rhs.InitCall != null) {
                rhs.InitCall.Args.ForEach(resolver.CheckIsCompilable);
              }
            }
          }

        } else if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          var callee = s.Method;
          Contract.Assert(callee != null);  // follows from the invariant of CallStmt
          s.IsGhost = callee.IsGhost;
          // check in-parameters
          if (mustBeErasable) {
            if (!s.IsGhost) {
              Error(s, "only ghost methods can be called from this context");
            }
          } else {
            int j;
            if (!callee.IsGhost) {
              resolver.CheckIsCompilable(s.Receiver);
              j = 0;
              foreach (var e in s.Args) {
                Contract.Assume(j < callee.Ins.Count);  // this should have already been checked by the resolver
                if (!callee.Ins[j].IsGhost) {
                  resolver.CheckIsCompilable(e);
                }
                j++;
              }
            }
            j = 0;
            foreach (var e in s.Lhs) {
              var resolvedLhs = e.Resolved;
              if (callee.IsGhost || callee.Outs[j].IsGhost) {
                // LHS must denote a ghost
                if (resolvedLhs is IdentifierExpr) {
                  var ll = (IdentifierExpr)resolvedLhs;
                  if (!ll.Var.IsGhost) {
                    if (ll is AutoGhostIdentifierExpr && ll.Var is LocalVariable) {
                      // the variable was actually declared in this statement, so auto-declare it as ghost
                      ((LocalVariable)ll.Var).MakeGhost();
                    } else {
                      Error(s, "actual out-parameter{0} is required to be a ghost variable", s.Lhs.Count == 1 ? "" : " " + j);
                    }
                  }
                } else if (resolvedLhs is MemberSelectExpr) {
                  var ll = (MemberSelectExpr)resolvedLhs;
                  if (!ll.Member.IsGhost) {
                    Error(s, "actual out-parameter{0} is required to be a ghost field", s.Lhs.Count == 1 ? "" : " " + j);
                  }
                } else {
                  // this is an array update, and arrays are always non-ghost
                  Error(s, "actual out-parameter{0} is required to be a ghost variable", s.Lhs.Count == 1 ? "" : " " + j);
                }
              }
              j++;
            }
          }

        } else if (stmt is BlockStmt) {
          var s = (BlockStmt)stmt;
          s.IsGhost = mustBeErasable;  // set .IsGhost before descending into substatements (since substatements may do a 'break' out of this block)
          s.Body.Iter(ss => Visit(ss, mustBeErasable));
          s.IsGhost = s.IsGhost || s.Body.All(ss => ss.IsGhost);  // mark the block statement as ghost if all its substatements are ghost

        } else if (stmt is IfStmt) {
          var s = (IfStmt)stmt;
          s.IsGhost = mustBeErasable || (s.Guard != null && resolver.UsesSpecFeatures(s.Guard));
          if (!mustBeErasable && s.IsGhost) {
            resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost if");
          }
          Visit(s.Thn, s.IsGhost);
          if (s.Els != null) {
            Visit(s.Els, s.IsGhost);
          }
          // if both branches were all ghost, then we can mark the enclosing statement as ghost as well
          s.IsGhost = s.IsGhost || (s.Thn.IsGhost && (s.Els == null || s.Els.IsGhost));

        } else if (stmt is AlternativeStmt) {
          var s = (AlternativeStmt)stmt;
          s.IsGhost = mustBeErasable || s.Alternatives.Exists(alt => resolver.UsesSpecFeatures(alt.Guard));
          if (!mustBeErasable && s.IsGhost) {
            resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost if");
          }
          s.Alternatives.Iter(alt => alt.Body.Iter(ss => Visit(ss, s.IsGhost)));
          s.IsGhost = s.IsGhost || s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost));

        } else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          s.IsGhost = mustBeErasable || (s.Guard != null && resolver.UsesSpecFeatures(s.Guard));
          if (!mustBeErasable && s.IsGhost) {
            resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost while");
          }
          if (s.IsGhost && s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
            Error(s, "'decreases *' is not allowed on ghost loops");
          }
          if (s.IsGhost && s.Mod.Expressions != null) {
            s.Mod.Expressions.Iter(resolver.DisallowNonGhostFieldSpecifiers);
          }
          if (s.Body != null) {
            Visit(s.Body, s.IsGhost);
          }
          s.IsGhost = s.IsGhost || s.Body == null || (!s.Decreases.Expressions.Exists(e => e is WildcardExpr) && s.Body.IsGhost);

        } else if (stmt is AlternativeLoopStmt) {
          var s = (AlternativeLoopStmt)stmt;
          s.IsGhost = mustBeErasable || s.Alternatives.Exists(alt => resolver.UsesSpecFeatures(alt.Guard));
          if (!mustBeErasable && s.IsGhost) {
            resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost while");
          }
          if (s.IsGhost && s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
            Error(s, "'decreases *' is not allowed on ghost loops");
          }
          if (s.IsGhost && s.Mod.Expressions != null) {
            s.Mod.Expressions.Iter(resolver.DisallowNonGhostFieldSpecifiers);
          }
          s.Alternatives.Iter(alt => alt.Body.Iter(ss => Visit(ss, s.IsGhost)));
          s.IsGhost = s.IsGhost || (!s.Decreases.Expressions.Exists(e => e is WildcardExpr) && s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost)));

        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          s.IsGhost = mustBeErasable || s.Kind != ForallStmt.BodyKind.Assign || resolver.UsesSpecFeatures(s.Range);
          if (s.Body != null) {
            Visit(s.Body, s.IsGhost);
          }
          s.IsGhost = s.IsGhost || s.Body == null || s.Body.IsGhost;

          if (!s.IsGhost) {
            // Since we've determined this is a non-ghost forall statement, we now check that the bound variables have compilable bounds.
            var uncompilableBoundVars = s.UncompilableBoundVars();
            if (uncompilableBoundVars.Count != 0) {
              foreach (var bv in uncompilableBoundVars) {
                Error(s, "forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{0}'", bv.Name);
              }
            }
          }

        } else if (stmt is ModifyStmt) {
          var s = (ModifyStmt)stmt;
          s.IsGhost = mustBeErasable;
          if (s.IsGhost) {
            s.Mod.Expressions.Iter(resolver.DisallowNonGhostFieldSpecifiers);
          }
          if (s.Body != null) {
            Visit(s.Body, mustBeErasable);
          }

        } else if (stmt is CalcStmt) {
          var s = (CalcStmt)stmt;
          s.IsGhost = true;
          foreach (var h in s.Hints) {
            Visit(h, true);
          }

        } else if (stmt is MatchStmt) {
          var s = (MatchStmt)stmt;
          s.IsGhost = mustBeErasable || resolver.UsesSpecFeatures(s.Source);
          if (!mustBeErasable && s.IsGhost) {
            resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost match");
          }
          s.Cases.Iter(kase => kase.Body.Iter(ss => Visit(ss, s.IsGhost)));
          s.IsGhost = s.IsGhost || s.Cases.All(kase => kase.Body.All(ss => ss.IsGhost));

        } else if (stmt is SkeletonStatement) {
          var s = (SkeletonStatement)stmt;
          s.IsGhost = mustBeErasable;
          if (s.S != null) {
            Visit(s.S, mustBeErasable);
            s.IsGhost = s.IsGhost || s.S.IsGhost;
          }

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
      }
    }
#endregion

    // ------------------------------------------------------------------------------------------------------
    // ----- FillInDefaultLoopDecreases ---------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region FillInDefaultLoopDecreases
    class FillInDefaultLoopDecreases_Visitor : ResolverBottomUpVisitor
    {
      readonly ICallable EnclosingMethod;
      public FillInDefaultLoopDecreases_Visitor(Resolver resolver, ICallable enclosingMethod)
        : base(resolver) {
        Contract.Requires(resolver != null);
        Contract.Requires(enclosingMethod != null);
        EnclosingMethod = enclosingMethod;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          resolver.FillInDefaultLoopDecreases(s, s.Guard, s.Decreases.Expressions, EnclosingMethod);
        } else if (stmt is AlternativeLoopStmt) {
          var s = (AlternativeLoopStmt)stmt;
          resolver.FillInDefaultLoopDecreases(s, null, s.Decreases.Expressions, EnclosingMethod);
        }
      }
    }
#endregion FillInDefaultLoopDecreases

    // ------------------------------------------------------------------------------------------------------
    // ----- ReportMoreAdditionalInformation ----------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region ReportOtherAdditionalInformation_Visitor
    class ReportOtherAdditionalInformation_Visitor : ResolverBottomUpVisitor
    {
      public ReportOtherAdditionalInformation_Visitor(Resolver resolver)
        : base(resolver) {
        Contract.Requires(resolver != null);
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          if (s.Kind == ForallStmt.BodyKind.Call) {
            var cs = (CallStmt)s.S0;
            // show the callee's postcondition as the postcondition of the 'forall' statement
            // TODO:  The following substitutions do not correctly take into consideration variable capture; hence, what the hover text displays may be misleading
            var argsSubstMap = new Dictionary<IVariable, Expression>();  // maps formal arguments to actuals
            Contract.Assert(cs.Method.Ins.Count == cs.Args.Count);
            for (int i = 0; i < cs.Method.Ins.Count; i++) {
              argsSubstMap.Add(cs.Method.Ins[i], cs.Args[i]);
            }
            var substituter = new Translator.AlphaConverting_Substituter(cs.Receiver, argsSubstMap, new Dictionary<TypeParameter, Type>());
            if (!Attributes.Contains(s.Attributes, "auto_generated")) {
              foreach (var ens in cs.Method.Ens) {
                var p = substituter.Substitute(ens.E);  // substitute the call's actuals for the method's formals
                resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ensures " + Printer.ExprToString(p));
              }
            }
          }
        }
      }
    }
#endregion ReportOtherAdditionalInformation_Visitor

    // ------------------------------------------------------------------------------------------------------
    // ----- ReportMoreAdditionalInformation ----------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
#region CheckDividedConstructorInit
    class CheckDividedConstructorInit_Visitor : ResolverTopDownVisitor<int>
    {
      public CheckDividedConstructorInit_Visitor(Resolver resolver)
        : base(resolver)
      {
        Contract.Requires(resolver != null);
      }
      public void CheckInit(List<Statement> initStmts) {
        Contract.Requires(initStmts != null);
        initStmts.Iter(CheckInit);
      }
      /// <summary>
      /// This method almost does what Visit(Statement) does, except that it handles assignments to
      /// fields differently.
      /// </summary>
      void CheckInit(Statement stmt) {
        Contract.Requires(stmt != null);
        // Visit(stmt) would do:
        //     stmt.SubExpressions.Iter(Visit);    (*)
        //     stmt.SubStatements.Iter(Visit);     (**)
        //     VisitOneStmt(stmt);                 (***)
        // We may do less for (*), we always use CheckInit instead of Visit in (**), and we do (***) the same.
        if (stmt is AssignStmt) {
          var s = stmt as AssignStmt;
          // The usual visitation of s.SubExpressions.Iter(Visit) would do the following:
          //   Attributes.SubExpressions(s.Attributes).Iter(Visit);  (+)
          //   Visit(s.Lhs);                                         (++)
          //   s.Rhs.SubExpressions.Iter(Visit);                     (+++)
          // Here, we may do less; in particular, we may omit (++).
          Attributes.SubExpressions(s.Attributes).Iter(VisitExpr);  // (+)
          var mse = s.Lhs as MemberSelectExpr;
          if (mse != null && Expression.AsThis(mse.Obj) != null) {
            if (s.Rhs is ExprRhs) {
              // This is a special case we allow.  Omit s.Lhs in the recursive visits.  That is, we omit (++).
              // Furthermore, because the assignment goes to a field of "this" and won't be available until after
              // the "new;", we can allow certain specific (and useful) uses of "this" in the RHS.
              s.Rhs.SubExpressions.Iter(LiberalRHSVisit);  // (+++)
            } else {
              s.Rhs.SubExpressions.Iter(VisitExpr);  // (+++)
            }
          } else {
            VisitExpr(s.Lhs);  // (++)
            s.Rhs.SubExpressions.Iter(VisitExpr);  // (+++)
          }
        } else {
          stmt.SubExpressions.Iter(VisitExpr);  // (*)
        }
        stmt.SubStatements.Iter(CheckInit);  // (**)
        int dummy = 0;
        VisitOneStmt(stmt, ref dummy);  // (***)
      }
      void VisitExpr(Expression expr) {
        Contract.Requires(expr != null);
        Visit(expr, 0);
      }
      protected override bool VisitOneExpr(Expression expr, ref int unused) {
        if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          if (e.Member.IsInstanceIndependentConstant && Expression.AsThis(e.Obj) != null) {
            return false;  // don't continue the recursion
          }
        } else if (expr is ThisExpr && !(expr is ImplicitThisExpr_ConstructorCall)) {
          resolver.reporter.Error(MessageSource.Resolver, expr.tok, "in the first division of the constructor body (before 'new;'), 'this' can only be used to assign to its fields");
        }
        return base.VisitOneExpr(expr, ref unused);
      }
      void LiberalRHSVisit(Expression expr) {
        Contract.Requires(expr != null);
        // It is important not to allow "this" to flow into something that can be used (for compilation or
        // verification purposes) before the "new;", because, to the verifier, "this" has not yet been allocated.
        // The verifier is told that everything reachable from the heap is expected to be allocated and satisfy all
        // the usual properties, so "this" had better not become reachable from the heap until after the "new;"
        // that does the actual allocation of "this".
        // Within these restrictions, we can allow the (not yet fully available) value "this" to flow into values
        // stored in fields of "this".  Such values are naked occurrences of "this" and "this" occurring
        // as part of constructing a value type.  Since by this rule, "this" may be part of the value stored in
        // a field of "this", we must apply the same rules to uses of the values of fields of "this".
        if (expr is ConcreteSyntaxExpression) {
        } else if (expr is ThisExpr) {
        } else if (expr is MemberSelectExpr && IsThisDotField((MemberSelectExpr)expr)) {
        } else if (expr is SetDisplayExpr) {
        } else if (expr is MultiSetDisplayExpr) {
        } else if (expr is SeqDisplayExpr) {
        } else if (expr is MapDisplayExpr) {
        } else if (expr is BinaryExpr && IsCollectionOperator(((BinaryExpr)expr).ResolvedOp)) {
        } else if (expr is DatatypeValue) {
        } else if (expr is ITEExpr) {
          var e = (ITEExpr)expr;
          VisitExpr(e.Test);
          LiberalRHSVisit(e.Thn);
          LiberalRHSVisit(e.Els);
          return;
        } else {
          // defer to the usual Visit
          VisitExpr(expr);
          return;
        }
        expr.SubExpressions.Iter(LiberalRHSVisit);
      }
      static bool IsThisDotField(MemberSelectExpr expr) {
        Contract.Requires(expr != null);
        return Expression.AsThis(expr.Obj) != null && expr.Member is Field;
      }
      static bool IsCollectionOperator(BinaryExpr.ResolvedOpcode op) {
        switch (op) {
          // sets:  +, *, -
          case BinaryExpr.ResolvedOpcode.Union:
          case BinaryExpr.ResolvedOpcode.Intersection:
          case BinaryExpr.ResolvedOpcode.SetDifference:
          // multisets: +, *, -
          case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          case BinaryExpr.ResolvedOpcode.MultiSetDifference:
           // sequences: +
          case BinaryExpr.ResolvedOpcode.Concat:
          // maps: +
          case BinaryExpr.ResolvedOpcode.MapUnion:
            return true;
          default:
            return false;
        }
      }
    }
#endregion

    // ------------------------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------

    bool InferRequiredEqualitySupport(TypeParameter tp, Type type) {
      Contract.Requires(tp != null);
      Contract.Requires(type != null);

      type = type.Normalize();  // we only do a .Normalize() here, because we want to keep stop at any type synonym or subset type
      if (type is BasicType) {
      } else if (type is SetType) {
        var st = (SetType)type;
        return st.Arg.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, st.Arg);
      } else if (type is MultiSetType) {
        var ms = (MultiSetType)type;
        return ms.Arg.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, ms.Arg);
      } else if (type is MapType) {
        var mt = (MapType)type;
        return mt.Domain.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, mt.Domain) || InferRequiredEqualitySupport(tp, mt.Range);
      } else if (type is SeqType) {
        var sq = (SeqType)type;
        return InferRequiredEqualitySupport(tp, sq.Arg);
      } else if (type is UserDefinedType) {
        var udt = (UserDefinedType)type;
        List<TypeParameter> formalTypeArgs = null;
        if (udt.ResolvedClass != null) {
          formalTypeArgs = udt.ResolvedClass.TypeArgs;
        } else if (udt.ResolvedParam is OpaqueType_AsParameter) {
          var t = (OpaqueType_AsParameter)udt.ResolvedParam;
          formalTypeArgs = t.TypeArgs;
        }
        if (formalTypeArgs == null) {
          Contract.Assert(udt.TypeArgs.Count == 0);
        } else {
          Contract.Assert(formalTypeArgs.Count == udt.TypeArgs.Count);
          var i = 0;
          foreach (var argType in udt.TypeArgs) {
            var formalTypeArg = formalTypeArgs[i];
            if ((formalTypeArg.MustSupportEquality && argType.AsTypeParameter == tp) || InferRequiredEqualitySupport(tp, argType)) {
              return true;
            }
            i++;
          }
        }
        if (udt.ResolvedClass is TypeSynonymDecl) {
          var syn = (TypeSynonymDecl)udt.ResolvedClass;
          if (syn.IsRevealedInScope(Type.GetScope())) {
            return InferRequiredEqualitySupport(tp, syn.RhsWithArgument(udt.TypeArgs));
          }
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return false;
    }

    TopLevelDeclWithMembers currentClass;
    Method currentMethod;
    bool inBodyInitContext;  // "true" only if "currentMethod is Constructor"
    readonly Scope<TypeParameter>/*!*/
      allTypeParameters = new Scope<TypeParameter>();
    readonly Scope<IVariable>/*!*/ scope = new Scope<IVariable>();
    Scope<Statement>/*!*/ enclosingStatementLabels = new Scope<Statement>();
    Scope<Label>/*!*/ dominatingStatementLabels = new Scope<Label>();
    List<Statement> loopStack = new List<Statement>();  // the enclosing loops (from which it is possible to break out)

    /// <summary>
    /// This method resolves the types that have been given after the 'extends' keyword.  Then, it populates
    /// the string->MemberDecl table for "cl" to make sure that all inherited names are accounted for.  Further
    /// checks are done later, elsewhere.
    /// </summary>
    void RegisterInheritedMembers(ClassDecl cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);
      currentClass = cl;

      if (cl.TraitsTyp.Count > 0 && cl.TypeArgs.Count > 0) {
        reporter.Error(MessageSource.Resolver, cl.tok, "sorry, traits are currently supported only for classes that take no type arguments");  // TODO: do the work to remove this limitation
      }

      // Resolve names of traits extended
      foreach (var tt in cl.TraitsTyp) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType_ClassName(cl.tok, tt, new NoContext(cl.Module), ResolveTypeOptionEnum.DontInfer, null);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var udt = tt as UserDefinedType;
          if (udt != null && udt.ResolvedClass is NonNullTypeDecl && ((NonNullTypeDecl)udt.ResolvedClass).ViewAsClass is TraitDecl) {
            var trait = (TraitDecl)((NonNullTypeDecl)udt.ResolvedClass).ViewAsClass;
            //disallowing inheritance in multi module case
            bool termination = true;
            if (cl.Module == trait.Module || (Attributes.ContainsBool(trait.Attributes, "termination", ref termination) && !termination)) {
              // all is good (or the user takes responsibility for the lack of termination checking)
              cl.TraitsObj.Add(trait);
            } else {
              reporter.Error(MessageSource.Resolver, udt.tok, "class '{0}' is in a different module than trait '{1}'. A class may only extend a trait in the same module.", cl.Name, trait.FullName);
            }
          } else {
            reporter.Error(MessageSource.Resolver, udt != null ? udt.tok : cl.tok, "a class can only extend traits (found '{0}')", tt);
          }
        }
      }

      // Inherit members from traits.  What we do here is simply to register names, and in particular to register
      // names that are no already in the class.
      var members = classMembers[cl];
      foreach (var trait in cl.TraitsObj) {
        foreach (var traitMember in trait.Members) {
          MemberDecl classMember;
          if (members.TryGetValue(traitMember.Name, out classMember)) {
            // the class already declares or inherits a member with this name, so we take no further action at this time
          } else {
            // register the trait member in the class
            members.Add(traitMember.Name, traitMember);
          }
        }
      }

      currentClass = null;
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveClassMemberTypes(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      currentClass = cl;

      foreach (MemberDecl member in cl.Members) {
        member.EnclosingClass = cl;
        if (member is Field) {
          if (member is ConstantField) {
            var m = (ConstantField)member;
            ResolveType(member.tok, ((Field)member).Type, m, ResolveTypeOptionEnum.DontInfer, null);
          } else {
            // In the following, we pass in a NoContext, because any cycle formed by a redirecting-type constraints would have to
            // dereference the heap, and such constraints are not allowed to dereference the heap so an error will be produced
            // even if we don't detect this cycle.
            ResolveType(member.tok, ((Field)member).Type, new NoContext(cl.Module), ResolveTypeOptionEnum.DontInfer, null);
          }
        } else if (member is Function) {
          var f = (Function)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, true, f);
          ResolveFunctionSignature(f);
          allTypeParameters.PopMarker();
          if (f is FixpointPredicate && ec == reporter.Count(ErrorLevel.Error)) {
            var ff = ((FixpointPredicate)f).PrefixPredicate;  // note, may be null if there was an error before the prefix predicate was generated
            if (ff != null) {
              ff.EnclosingClass = cl;
              allTypeParameters.PushMarker();
              ResolveTypeParameters(ff.TypeArgs, true, ff);
              ResolveFunctionSignature(ff);
              allTypeParameters.PopMarker();
            }
          }

        } else if (member is Method) {
          var m = (Method)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, true, m);
          ResolveMethodSignature(m);
          allTypeParameters.PopMarker();
          var com = m as FixpointLemma;
          if (com != null && com.PrefixLemma != null && ec == reporter.Count(ErrorLevel.Error)) {
            var mm = com.PrefixLemma;
            // resolve signature of the prefix lemma
            mm.EnclosingClass = cl;
            allTypeParameters.PushMarker();
            ResolveTypeParameters(mm.TypeArgs, true, mm);
            ResolveMethodSignature(mm);
            allTypeParameters.PopMarker();
          }

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
      }

      currentClass = null;
    }

    void InheritTraitMembers(ClassDecl cl) {
      Contract.Requires(cl != null);

      var refinementTransformer = new RefinementTransformer(reporter);
      //merging class members with parent members if any
      var clMembers = classMembers[cl];
      foreach (TraitDecl trait in cl.TraitsObj) {
        //merging current class members with the inheriting trait
        foreach (var traitMember in trait.Members) {
          var clMember = clMembers[traitMember.Name];
          if (clMember == traitMember) {
            // The member is the one inherited from the trait (and the class does not itself define a member with this name).  This
            // is fine for fields and for functions and methods with bodies.  However, for a body-less function or method, the class
            // is required to at least redeclare the member with its signature.  (It should also provide a stronger specification,
            // but that will be checked by the verifier.  And it should also have a body, but that will be checked by the compiler.)
            if (traitMember is Field) {
              var field = (Field)traitMember;
              if (!field.IsStatic) {
                cl.InheritedMembers.Add(field);
              }
            } else if (traitMember is Function) {
              var func = (Function)traitMember;
              if (func.Body == null) {
                reporter.Error(MessageSource.Resolver, cl.tok, "class '{0}' does not implement trait function '{1}.{2}'", cl.Name, trait.Name, traitMember.Name);
              } else if (!func.IsStatic) {
                cl.InheritedMembers.Add(func);
              }
            } else if (traitMember is Method) {
              var method = (Method)traitMember;
              if (method.Body == null) {
                reporter.Error(MessageSource.Resolver, cl.tok, "class '{0}' does not implement trait method '{1}.{2}'", cl.Name, trait.Name, traitMember.Name);
              } else if (!method.IsStatic) {
                cl.InheritedMembers.Add(method);
              }
            }
          } else if (clMember.EnclosingClass != cl) {
            // The class inherits the member from two places
            reporter.Error(MessageSource.Resolver, clMember.tok, "member name '{0}' in class '{1}' inherited from both traits '{2}' and '{3}'", traitMember.Name, cl.Name, clMember.EnclosingClass.Name, trait.Name);

          } else if (traitMember is Field) {
            // The class is not allowed to do anything with the field other than silently inherit it.
            if (clMember is Field) {
              reporter.Error(MessageSource.Resolver, clMember.tok, "field '{0}' is inherited from trait '{1}' and is not allowed to be re-declared", traitMember.Name, trait.Name);
            } else {
              reporter.Error(MessageSource.Resolver, clMember.tok, "member name '{0}' in class '{1}' clashes with inherited field from trait '{2}'", traitMember.Name, cl.Name, trait.Name);
            }

          } else if (traitMember is Method) {
            var traitMethod = (Method)traitMember;
            if (traitMethod.Body != null) {
              // The method was defined in the trait, so the class is not allowed to do anything with the method other than silently inherit it.
              reporter.Error(MessageSource.Resolver, clMember.tok, "member '{0}' in class '{1}' overrides fully defined method inherited from trait '{2}'", clMember.Name, cl.Name, trait.Name);
            } else if (!(clMember is Method)) {
              reporter.Error(MessageSource.Resolver, clMember.tok, "non-method member '{0}' overrides method '{1}' inherited from trait '{2}'", clMember.Name, traitMethod.Name, trait.Name);
            } else {
              var classMethod = (Method)clMember;

              // Copy trait's extern attribute onto class if class does not provide one
              if(!Attributes.Contains(classMethod.Attributes, "extern") && Attributes.Contains(traitMethod.Attributes, "extern")) {
                var traitExternArgs = Attributes.FindExpressions(traitMethod.Attributes, "extern");
                classMethod.Attributes = new Attributes("extern", traitExternArgs, classMethod.Attributes);
              }

              classMethod.OverriddenMethod = traitMethod;
              //adding a call graph edge from the trait method to that of class
              cl.Module.CallGraph.AddEdge(traitMethod, classMethod);

              refinementTransformer.CheckOverride_MethodParameters(classMethod, traitMethod);

              var traitMethodAllowsNonTermination = Contract.Exists(traitMethod.Decreases.Expressions, e => e is WildcardExpr);
              var classMethodAllowsNonTermination = Contract.Exists(classMethod.Decreases.Expressions, e => e is WildcardExpr);
              if (classMethodAllowsNonTermination && !traitMethodAllowsNonTermination) {
                reporter.Error(MessageSource.Resolver, classMethod.tok, "not allowed to override a terminating method with a possibly non-terminating method ('{0}')", classMethod.Name);
              }
            }

          } else if (traitMember is Function) {
            var traitFunction = (Function)traitMember;
            if (traitFunction.Body != null) {
              // The function was defined in the trait, so the class is not allowed to do anything with the function other than silently inherit it.
              reporter.Error(MessageSource.Resolver, clMember.tok, "member '{0}' in class '{1}' overrides fully defined function inherited from trait '{2}'", clMember.Name, cl.Name, trait.Name);
            } else if (!(clMember is Function)) {
              reporter.Error(MessageSource.Resolver, clMember.tok, "non-function member '{0}' overrides function '{1}' inherited from trait '{2}'", clMember.Name, traitFunction.Name, trait.Name);
            } else {
              var classFunction = (Function)clMember;
              classFunction.OverriddenFunction = traitFunction;
              //adding a call graph edge from the trait method to that of class
              cl.Module.CallGraph.AddEdge(traitFunction, classFunction);

              refinementTransformer.CheckOverride_FunctionParameters(classFunction, traitFunction);
            }

          } else {
            Contract.Assert(false);  // unexpected member
          }
        }
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed, and that all types in class members have been resolved
    /// </summary>
    void ResolveClassMemberBodies(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Requires(AllTypeConstraints.Count == 0);
      Contract.Ensures(currentClass == null);
      Contract.Ensures(AllTypeConstraints.Count == 0);

      currentClass = cl;
      foreach (MemberDecl member in cl.Members) {
        Contract.Assert(VisibleInScope(member));
        if (member is ConstantField) {
          // don't do anything here, because const fields have already been resolved
        } else if (member is Field) {
          var opts = new ResolveOpts(new NoContext(currentClass.Module), false);
          ResolveAttributes(member.Attributes, member, opts);
        } else if (member is Function) {
          var f = (Function)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, false, f);
          ResolveFunction(f);
          allTypeParameters.PopMarker();
          if (f is FixpointPredicate && ec == reporter.Count(ErrorLevel.Error)) {
            var ff = ((FixpointPredicate)f).PrefixPredicate;
            if (ff != null) {
              allTypeParameters.PushMarker();
              ResolveTypeParameters(ff.TypeArgs, false, ff);
              ResolveFunction(ff);
              allTypeParameters.PopMarker();
            }
          }

        } else if (member is Method) {
          var m = (Method)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, false, m);
          ResolveMethod(m);
          allTypeParameters.PopMarker();

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
        Contract.Assert(AllTypeConstraints.Count == 0);
      }
      currentClass = null;
    }

    /// <summary>
    /// Checks if "expr" is a constant (that is, heap independent) expression that can be assigned to "field".
    /// If it is, return "true". Otherwise, report an error and return "false".
    /// This method also adds dependency edges to the module's call graph and checks for self-loops. If a self-loop
    /// is detected, "false" is returned.
    /// </summary>
    bool CheckIsConstantExpr(ConstantField field, Expression expr) {
      Contract.Requires(field != null);
      Contract.Requires(expr != null);
      if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member is Field && ((Field)e.Member).IsMutable) {
          reporter.Error(MessageSource.Resolver, field.tok, "only constants are allowed in the expression to initialize constant {0}", field.Name);
          return false;
        }
        if (e.Member is ICallable) {
          var other = (ICallable)e.Member;
          field.EnclosingModule.CallGraph.AddEdge(field, other);
        }
        // okay so far; now, go on checking subexpressions
      }
      return expr.SubExpressions.All(e => CheckIsConstantExpr(field, e));
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveCtorTypes(DatatypeDecl/*!*/ dt, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ coDependencies) {
      Contract.Requires(dt != null);
      Contract.Requires(dependencies != null);
      Contract.Requires(coDependencies != null);
      foreach (DatatypeCtor ctor in dt.Ctors) {

        ctor.EnclosingDatatype = dt;

        allTypeParameters.PushMarker();
        ResolveCtorSignature(ctor, dt.TypeArgs);
        allTypeParameters.PopMarker();

        if (dt is IndDatatypeDecl) {
          // The dependencies of interest among inductive datatypes are all (inductive data)types mentioned in the parameter types
          var idt = (IndDatatypeDecl)dt;
          dependencies.AddVertex(idt);
          foreach (Formal p in ctor.Formals) {
            AddDatatypeDependencyEdge(idt, p.Type, dependencies);
          }
        } else {
          // The dependencies of interest among codatatypes are just the top-level types of parameters.
          var codt = (CoDatatypeDecl)dt;
          coDependencies.AddVertex(codt);
          foreach (var p in ctor.Formals) {
            var co = p.Type.AsCoDatatype;
            if (co != null && codt.Module == co.Module) {
              coDependencies.AddEdge(codt, co);
            }
          }
        }
      }
    }

    void AddDatatypeDependencyEdge(IndDatatypeDecl dt, Type tp, Graph<IndDatatypeDecl> dependencies) {
      Contract.Requires(dt != null);
      Contract.Requires(tp != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

      tp = tp.NormalizeExpand();
      var dependee = tp.AsIndDatatype;
      if (dependee != null && dt.Module == dependee.Module) {
        dependencies.AddEdge(dt, dependee);
        foreach (var ta in ((UserDefinedType)tp).TypeArgs) {
          AddDatatypeDependencyEdge(dt, ta, dependencies);
        }
      }
    }

    /// <summary>
    /// Check that the SCC of 'startingPoint' can be carved up into stratospheres in such a way that each
    /// datatype has some value that can be constructed from datatypes in lower stratospheres only.
    /// The algorithm used here is quadratic in the number of datatypes in the SCC.  Since that number is
    /// deemed to be rather small, this seems okay.
    ///
    /// As a side effect of this checking, the DefaultCtor field is filled in (for every inductive datatype
    /// that passes the check).  It may be that several constructors could be used as the default, but
    /// only the first one encountered as recorded.  This particular choice is slightly more than an
    /// implementation detail, because it affects how certain cycles among inductive datatypes (having
    /// to do with the types used to instantiate type parameters of datatypes) are used.
    ///
    /// The role of the SCC here is simply to speed up this method.  It would still be correct if the
    /// equivalence classes in the given SCC were unions of actual SCC's.  In particular, this method
    /// would still work if "dependencies" consisted of one large SCC containing all the inductive
    /// datatypes in the module.
    /// </summary>
    void SccStratosphereCheck(IndDatatypeDecl startingPoint, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies) {
      Contract.Requires(startingPoint != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

      var scc = dependencies.GetSCC(startingPoint);
      int totalCleared = 0;
      while (true) {
        int clearedThisRound = 0;
        foreach (var dt in scc) {
          if (dt.DefaultCtor != null) {
            // previously cleared
          } else if (ComputeDefaultCtor(dt)) {
            Contract.Assert(dt.DefaultCtor != null);  // should have been set by the successful call to StratosphereCheck)
            clearedThisRound++;
            totalCleared++;
          }
        }
        if (totalCleared == scc.Count) {
          // all is good
          return;
        } else if (clearedThisRound != 0) {
          // some progress was made, so let's keep going
        } else {
          // whatever is in scc-cleared now failed to pass the test
          foreach (var dt in scc) {
            if (dt.DefaultCtor == null) {
              reporter.Error(MessageSource.Resolver, dt, "because of cyclic dependencies among constructor argument types, no instances of datatype '{0}' can be constructed", dt.Name);
            }
          }
          return;
        }
      }
    }

    /// <summary>
    /// Check that the datatype has some constructor all whose argument types can be constructed.
    /// Returns 'true' and sets dt.DefaultCtor if that is the case.
    /// </summary>
    bool ComputeDefaultCtor(IndDatatypeDecl dt) {
      Contract.Requires(dt != null);
      Contract.Requires(dt.DefaultCtor == null);  // the intention is that this method be called only when DefaultCtor hasn't already been set
      Contract.Ensures(!Contract.Result<bool>() || dt.DefaultCtor != null);

      // Stated differently, check that there is some constuctor where no argument type goes to the same stratum.
      DatatypeCtor defaultCtor = null;
      List<TypeParameter> lastTypeParametersUsed = null;
      foreach (DatatypeCtor ctor in dt.Ctors) {
        List<TypeParameter>  typeParametersUsed = new List<TypeParameter>();
        foreach (Formal p in ctor.Formals) {
          if (!CheckCanBeConstructed(p.Type, typeParametersUsed)) {
            // the argument type (has a component which) is not yet known to be constructable
            goto NEXT_OUTER_ITERATION;
          }
        }
        // this constructor satisfies the requirements, check to see if it is a better fit than the
        // one found so far. By "better" it means fewer type arguments. Between the ones with
        // the same number of the type arguments, pick the one shows first.
        if (defaultCtor == null || typeParametersUsed.Count < lastTypeParametersUsed.Count)  {
          defaultCtor = ctor;
          lastTypeParametersUsed = typeParametersUsed;
        }

      NEXT_OUTER_ITERATION: { }
      }

      if (defaultCtor != null) {
        dt.DefaultCtor = defaultCtor;
        dt.TypeParametersUsedInConstructionByDefaultCtor = new bool[dt.TypeArgs.Count];
        for (int i = 0; i < dt.TypeArgs.Count; i++) {
          dt.TypeParametersUsedInConstructionByDefaultCtor[i] = lastTypeParametersUsed.Contains(dt.TypeArgs[i]);
        }
        return true;
      }

      // no constructor satisfied the requirements, so this is an illegal datatype declaration
      return false;
    }

    bool CheckCanBeConstructed(Type tp, List<TypeParameter> typeParametersUsed) {
      tp = tp.NormalizeExpand();
      var dependee = tp.AsIndDatatype;
      if (dependee == null) {
        // the type is not an inductive datatype, which means it is always possible to construct it
        if (tp.IsTypeParameter) {
          typeParametersUsed.Add(((UserDefinedType)tp).ResolvedParam);
        }
        return true;
      } else if (dependee.DefaultCtor == null) {
        // the type is an inductive datatype that we don't yet know how to construct
        return false;
      }
      // also check the type arguments of the inductive datatype
      Contract.Assert(((UserDefinedType)tp).TypeArgs.Count == dependee.TypeParametersUsedInConstructionByDefaultCtor.Length);
      var i = 0;
      foreach (var ta in ((UserDefinedType)tp).TypeArgs) {  // note, "tp" is known to be a UserDefinedType, because that follows from tp being an inductive datatype
        if (dependee.TypeParametersUsedInConstructionByDefaultCtor[i] && !CheckCanBeConstructed(ta, typeParametersUsed)) {
          return false;
        }
        i++;
      }
      return true;
    }

    void DetermineEqualitySupport(IndDatatypeDecl startingPoint, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies) {
      Contract.Requires(startingPoint != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

      var scc = dependencies.GetSCC(startingPoint);
      // First, the simple case:  If any parameter of any inductive datatype in the SCC is of a codatatype type, then
      // the whole SCC is incapable of providing the equality operation.  Also, if any parameter of any inductive datatype
      // is a ghost, then the whole SCC is incapable of providing the equality operation.
      foreach (var dt in scc) {
        Contract.Assume(dt.EqualitySupport == IndDatatypeDecl.ES.NotYetComputed);
        foreach (var ctor in dt.Ctors) {
          foreach (var arg in ctor.Formals) {
            var anotherIndDt = arg.Type.AsIndDatatype;
            if (arg.IsGhost ||
                (anotherIndDt != null && anotherIndDt.EqualitySupport == IndDatatypeDecl.ES.Never) ||
                arg.Type.IsCoDatatype ||
                arg.Type.IsArrowType) {
              // arg.Type is known never to support equality
              // So, go around the entire SCC and record what we learnt
              foreach (var ddtt in scc) {
                ddtt.EqualitySupport = IndDatatypeDecl.ES.Never;
              }
              return;  // we are done
            }
          }
        }
      }

      // Now for the more involved case:  we need to determine which type parameters determine equality support for each datatype in the SCC
      // We start by seeing where each datatype's type parameters are used in a place known to determine equality support.
      bool thingsChanged = false;
      foreach (var dt in scc) {
        if (dt.TypeArgs.Count == 0) {
          // if the datatype has no type parameters, we certainly won't find any type parameters being used in the arguments types to the constructors
          continue;
        }
        foreach (var ctor in dt.Ctors) {
          foreach (var arg in ctor.Formals) {
            var typeArg = arg.Type.AsTypeParameter;
            if (typeArg != null) {
              typeArg.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
              thingsChanged = true;
            } else {
              var otherDt = arg.Type.AsIndDatatype;
              if (otherDt != null && otherDt.EqualitySupport == IndDatatypeDecl.ES.ConsultTypeArguments) {  // datatype is in a different SCC
                var otherUdt = (UserDefinedType)arg.Type.NormalizeExpand();
                var i = 0;
                foreach (var otherTp in otherDt.TypeArgs) {
                  if (otherTp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype) {
                    var tp = otherUdt.TypeArgs[i].AsTypeParameter;
                    if (tp != null) {
                      tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
                      thingsChanged = true;
                    }
                  }
                }
              }
            }
          }
        }
      }
      // Then we propagate this information up through the SCC
      while (thingsChanged) {
        thingsChanged = false;
        foreach (var dt in scc) {
          if (dt.TypeArgs.Count == 0) {
            // if the datatype has no type parameters, we certainly won't find any type parameters being used in the arguments types to the constructors
            continue;
          }
          foreach (var ctor in dt.Ctors) {
            foreach (var arg in ctor.Formals) {
              var otherDt = arg.Type.AsIndDatatype;
              if (otherDt != null && otherDt.EqualitySupport == IndDatatypeDecl.ES.NotYetComputed) { // otherDt lives in the same SCC
                var otherUdt = (UserDefinedType)arg.Type.NormalizeExpand();
                var i = 0;
                foreach (var otherTp in otherDt.TypeArgs) {
                  if (otherTp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype) {
                    var tp = otherUdt.TypeArgs[i].AsTypeParameter;
                    if (tp != null && !tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype) {
                      tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
                      thingsChanged = true;
                    }
                  }
                  i++;
                }
              }
            }
          }
        }
      }
      // Now that we have computed the .NecessaryForEqualitySupportOfSurroundingInductiveDatatype values, mark the datatypes as ones
      // where equality support should be checked by looking at the type arguments.
      foreach (var dt in scc) {
        dt.EqualitySupport = IndDatatypeDecl.ES.ConsultTypeArguments;
      }
    }

    void ResolveAttributes(Attributes attrs, IAttributeBearingDeclaration attributeHost, ResolveOpts opts) {
      Contract.Requires(opts != null);
      // order does not matter much for resolution, so resolve them in reverse order
      foreach (var attr in attrs.AsEnumerable()) {
        if (attributeHost != null && attr is UserSuppliedAttributes) {
          var usa = (UserSuppliedAttributes)attr;
          usa.Recognized = IsRecognizedAttribute(usa, attributeHost);
        }
        if (attr.Args != null) {
          foreach (var arg in attr.Args) {
            Contract.Assert(arg != null);
            int prevErrors = reporter.Count(ErrorLevel.Error);
            ResolveExpression(arg, opts);
            if (prevErrors == reporter.Count(ErrorLevel.Error)) {
              CheckTypeInference(arg, opts.codeContext);
            }
          }
        }
      }
    }

    /// <summary>
    /// Check to see if the attribute is one that is supported by Dafny.  What check performed here is,
    /// unfortunately, just an approximation, since the usage rules of a particular attribute is checked
    /// elsewhere (for example, in the compiler or verifier).  It would be nice to improve this.
    /// </summary>
    bool IsRecognizedAttribute(UserSuppliedAttributes a, IAttributeBearingDeclaration host) {
      Contract.Requires(a != null);
      Contract.Requires(host != null);
      switch (a.Name) {
        case "opaque":
          return host is Function && !(host is FixpointPredicate);
        case "trigger":
          return host is ComprehensionExpr || host is SetComprehension || host is MapComprehension;
        case "timeLimit":
        case "timeLimitMultiplier":
          return host is TopLevelDecl;
        case "tailrecursive":
          return host is Method && !((Method)host).IsGhost;
        case "autocontracts":
          return host is ClassDecl;
        case "autoreq":
          return host is Function;
        case "abstemious":
          return host is Function;
        default:
          return false;
      }
    }

    void ResolveTypeParameters(List<TypeParameter/*!*/>/*!*/ tparams, bool emitErrors, TypeParameter.ParentType/*!*/ parent) {
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
        var r = allTypeParameters.Push(tp.Name, tp);
        if (emitErrors) {
          if (r == Scope<TypeParameter>.PushResult.Duplicate) {
            reporter.Error(MessageSource.Resolver, tp, "Duplicate type-parameter name: {0}", tp.Name);
          } else if (r == Scope<TypeParameter>.PushResult.Shadow) {
            reporter.Warning(MessageSource.Resolver, tp.tok, "Shadowed type-parameter name: {0}", tp.Name);
          }
        }
      }
    }

    void ScopePushAndReport(Scope<IVariable> scope, IVariable v, string kind) {
      Contract.Requires(scope != null);
      Contract.Requires(v != null);
      Contract.Requires(kind != null);
      ScopePushAndReport(scope, v.Name, v, v.Tok, kind);
    }

    void ScopePushAndReport<Thing>(Scope<Thing> scope, string name, Thing thing, IToken tok, string kind) where Thing : class {
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
          reporter.Error(MessageSource.Resolver, tok, "Duplicate {0} name: {1}", kind, name);
          break;
        case Scope<Thing>.PushResult.Shadow:
          reporter.Warning(MessageSource.Resolver, tok, "Shadowed {0} name: {1}", kind, name);
          break;
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveFunctionSignature(Function f) {
      Contract.Requires(f != null);
      scope.PushMarker();
      if (f.SignatureIsOmitted) {
        reporter.Error(MessageSource.Resolver, f, "function signature can be omitted only in refining functions");
      }
      var option = f.TypeArgs.Count == 0 ? new ResolveTypeOption(f) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      foreach (Formal p in f.Formals) {
        ScopePushAndReport(scope, p, "parameter");
        ResolveType(p.tok, p.Type, f, option, f.TypeArgs);
        AddTypeDependencyEdges(f, p.Type);
      }
      if (f.Result != null) {
        ScopePushAndReport(scope, f.Result, "parameter/return");
        ResolveType(f.Result.tok, f.Result.Type, f, option, f.TypeArgs);
      } else {
        ResolveType(f.tok, f.ResultType, f, option, f.TypeArgs);
      }
      AddTypeDependencyEdges(f, f.ResultType);
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveFunction(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(AllTypeConstraints.Count == 0);
      Contract.Ensures(AllTypeConstraints.Count == 0);

      bool warnShadowingOption = DafnyOptions.O.WarnShadowing;  // save the original warnShadowing value
      bool warnShadowing = false;

      scope.PushMarker();
      if (f.IsStatic) {
        scope.AllowInstance = false;
      }
      foreach (Formal p in f.Formals) {
        scope.Push(p.Name, p);
      }
      ResolveAttributes(f.Attributes, f, new ResolveOpts(f, false));
      // take care of the warnShadowing attribute
      if (Attributes.ContainsBool(f.Attributes, "warnShadowing", ref warnShadowing)) {
        DafnyOptions.O.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }
      foreach (MaybeFreeExpression e in f.Req) {
        Expression r = e.E;
        ResolveExpression(r, new ResolveOpts(f, f is TwoStateFunction));
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(r, "Precondition must be a boolean (got {0})");
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpression(fr, FrameExpressionUse.Reads, f);
      }
      foreach (MaybeFreeExpression e in f.Ens) {
        Expression r = e.E;
        if (f.Result != null) {
          scope.PushMarker();
          scope.Push(f.Result.Name, f.Result);  // function return only visible in post-conditions
        }
        ResolveExpression(r, new ResolveOpts(f, f is TwoStateFunction, false, true, false));  // since this is a function, the postcondition is still a one-state predicate, unless it's a two-state function
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(r, "Postcondition must be a boolean (got {0})");
        if (f.Result != null) {
          scope.PopMarker();
        }
      }
      ResolveAttributes(f.Decreases.Attributes, null, new ResolveOpts(f, f is TwoStateFunction));
      foreach (Expression r in f.Decreases.Expressions) {
        ResolveExpression(r, new ResolveOpts(f, f is TwoStateFunction));
        // any type is fine
      }
      SolveAllTypeConstraints();

      if (f.Body != null) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(f.Body, new ResolveOpts(f, f is TwoStateFunction));
        Contract.Assert(f.Body.Type != null);  // follows from postcondition of ResolveExpression
        AddAssignableConstraint(f.tok, f.ResultType, f.Body.Type, "Function body type mismatch (expected {0}, got {1})");
        SolveAllTypeConstraints();
      }

      scope.PopMarker();

      DafnyOptions.O.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
    }

    public enum FrameExpressionUse { Reads, Modifies, Unchanged }

    void ResolveFrameExpression(FrameExpression fe, FrameExpressionUse use, ICodeContext codeContext) {
      Contract.Requires(fe != null);
      Contract.Requires(codeContext != null);
      ResolveExpression(fe.E, new ResolveOpts(codeContext, codeContext is TwoStateLemma || use == FrameExpressionUse.Unchanged));
      Type t = fe.E.Type;
      Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
      var eventualRefType = new InferredTypeProxy();
      if (use == FrameExpressionUse.Reads) {
        AddXConstraint(fe.E.tok, "ReadsFrame", t, eventualRefType, "a reads-clause expression must denote an object or a collection of objects (instead got {0})");
      } else {
        AddXConstraint(fe.E.tok, "ModifiesFrame", t, eventualRefType,
          use == FrameExpressionUse.Modifies ?
          "a modifies-clause expression must denote an object or a collection of objects (instead got {0})" :
          "an unchanged expression must denote an object or a collection of objects (instead got {0})");
      }
      if (fe.FieldName != null) {
        NonProxyType nptype;
        MemberDecl member = ResolveMember(fe.E.tok, eventualRefType, fe.FieldName, out nptype);
        UserDefinedType ctype = (UserDefinedType)nptype;  // correctness of cast follows from the DenotesClass test above
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Field)) {
          reporter.Error(MessageSource.Resolver, fe.E, "member {0} in type {1} does not refer to a field", fe.FieldName, ctype.Name);
        } else if (member is ConstantField) {
          reporter.Error(MessageSource.Resolver, fe.E, "expression is not allowed to refer to constant field {0}", fe.FieldName);
        } else {
          Contract.Assert(ctype != null && ctype.ResolvedClass != null);  // follows from postcondition of ResolveMember
          fe.Field = (Field)member;
        }
      }
    }

    /// <summary>
    /// This method can be called even if the resolution of "fe" failed; in that case, this method will
    /// not issue any error message.
    /// </summary>
    void DisallowNonGhostFieldSpecifiers(FrameExpression fe) {
      Contract.Requires(fe != null);
      if (fe.Field != null && !fe.Field.IsGhost) {
        reporter.Error(MessageSource.Resolver, fe.E, "in a ghost context, only ghost fields can be mentioned as modifies frame targets ({0})", fe.FieldName);
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethodSignature(Method m) {
      Contract.Requires(m != null);

      scope.PushMarker();
      if (m.SignatureIsOmitted) {
        reporter.Error(MessageSource.Resolver, m, "method signature can be omitted only in refining methods");
      }
      var option = m.TypeArgs.Count == 0 ? new ResolveTypeOption(m) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      // resolve in-parameters
      foreach (Formal p in m.Ins) {
        ScopePushAndReport(scope, p, "parameter");
        ResolveType(p.tok, p.Type, m, option, m.TypeArgs);
        AddTypeDependencyEdges(m, p.Type);
      }
      // resolve out-parameters
      foreach (Formal p in m.Outs) {
        ScopePushAndReport(scope, p, "parameter");
        ResolveType(p.tok, p.Type, m, option, m.TypeArgs);
        AddTypeDependencyEdges(m, p.Type);
      }
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethod(Method m) {
      Contract.Requires(m != null);
      Contract.Requires(AllTypeConstraints.Count == 0);
      Contract.Ensures(AllTypeConstraints.Count == 0);

      try {
        currentMethod = m;

        bool warnShadowingOption = DafnyOptions.O.WarnShadowing;  // save the original warnShadowing value
        bool warnShadowing = false;
        // take care of the warnShadowing attribute
        if (Attributes.ContainsBool(m.Attributes, "warnShadowing", ref warnShadowing)) {
          DafnyOptions.O.WarnShadowing = warnShadowing;  // set the value according to the attribute
        }

        // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
        scope.PushMarker();
        if (m.IsStatic || m is Constructor) {
          scope.AllowInstance = false;
        }
        foreach (Formal p in m.Ins) {
          scope.Push(p.Name, p);
        }

        // Start resolving specification...
        foreach (MaybeFreeExpression e in m.Req) {
          ResolveAttributes(e.Attributes, null, new ResolveOpts(m, m is TwoStateLemma));
          ResolveExpression(e.E, new ResolveOpts(m, m is TwoStateLemma));
          Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
        }

        ResolveAttributes(m.Mod.Attributes, null, new ResolveOpts(m, false));
        foreach (FrameExpression fe in m.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, m);
          if (m is Lemma || m is TwoStateLemma || m is FixpointLemma) {
            reporter.Error(MessageSource.Resolver, fe.tok, "{0}s are not allowed to have modifies clauses", m.WhatKind);
          } else if (m.IsGhost) {
            DisallowNonGhostFieldSpecifiers(fe);
          }
        }
        ResolveAttributes(m.Decreases.Attributes, null, new ResolveOpts(m, false));
        foreach (Expression e in m.Decreases.Expressions) {
          ResolveExpression(e, new ResolveOpts(m, m is TwoStateLemma));
          // any type is fine
        }

        if (m is Constructor) {
          scope.PopMarker();
          // start the scope again, but this time allowing instance
          scope.PushMarker();
          foreach (Formal p in m.Ins) {
            scope.Push(p.Name, p);
          }
        }

        // Add out-parameters to a new scope that will also include the outermost-level locals of the body
        // Don't care about any duplication errors among the out-parameters, since they have already been reported
        scope.PushMarker();
        if (m is FixpointLemma && m.Outs.Count != 0) {
          reporter.Error(MessageSource.Resolver, m.Outs[0].tok, "{0}s are not allowed to have out-parameters", m.WhatKind);
        } else {
          foreach (Formal p in m.Outs) {
            scope.Push(p.Name, p);
          }
        }

        // ... continue resolving specification
        foreach (MaybeFreeExpression e in m.Ens) {
          ResolveAttributes(e.Attributes, null, new ResolveOpts(m, true));
          ResolveExpression(e.E, new ResolveOpts(m, true));
          Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
        }
        SolveAllTypeConstraints();

        // Resolve body
        if (m.Body != null) {
          var com = m as FixpointLemma;
          if (com != null && com.PrefixLemma != null) {
            // The body may mentioned the implicitly declared parameter _k.  Throw it into the
            // scope before resolving the body.
            var k = com.PrefixLemma.Ins[0];
            scope.Push(k.Name, k);  // we expect no name conflict for _k
          }

          dominatingStatementLabels.PushMarker();
          foreach (var req in m.Req) {
            if (req.Label != null) {
              if (dominatingStatementLabels.Find(req.Label.Name) != null) {
                reporter.Error(MessageSource.Resolver, req.Label.Tok, "assert label shadows a dominating label");
              } else {
                var rr = dominatingStatementLabels.Push(req.Label.Name, req.Label);
                Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
              }
            }
          }
          ResolveBlockStatement(m.Body, m);
          dominatingStatementLabels.PopMarker();
          SolveAllTypeConstraints();
        }

        // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for colemmas)
        ResolveAttributes(m.Attributes, m, new ResolveOpts(m, false));

        DafnyOptions.O.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
        scope.PopMarker();  // for the out-parameters and outermost-level locals
        scope.PopMarker();  // for the in-parameters
      } finally {
        currentMethod = null;
      }
    }

    void ResolveCtorSignature(DatatypeCtor ctor, List<TypeParameter> dtTypeArguments) {
      Contract.Requires(ctor != null);
      Contract.Requires(ctor.EnclosingDatatype != null);
      Contract.Requires(dtTypeArguments != null);
      foreach (Formal p in ctor.Formals) {
        ResolveType(p.tok, p.Type, ctor.EnclosingDatatype, ResolveTypeOptionEnum.AllowPrefix, dtTypeArguments);
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveIteratorSignature(IteratorDecl iter) {
      Contract.Requires(iter != null);
      scope.PushMarker();
      if (iter.SignatureIsOmitted) {
        reporter.Error(MessageSource.Resolver, iter, "iterator signature can be omitted only in refining methods");
      }
      var initiallyNoTypeArguments = iter.TypeArgs.Count == 0;
      var option = initiallyNoTypeArguments ? new ResolveTypeOption(iter) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      // resolve the types of the parameters
      var prevErrorCount = reporter.Count(ErrorLevel.Error);
      foreach (var p in iter.Ins.Concat(iter.Outs)) {
        ResolveType(p.tok, p.Type, iter, option, iter.TypeArgs);
      }
      // resolve the types of the added fields (in case some of these types would cause the addition of default type arguments)
      if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
        foreach (var p in iter.OutsHistoryFields) {
          ResolveType(p.tok, p.Type, iter, option, iter.TypeArgs);
        }
      }
      if (iter.TypeArgs.Count != iter.NonNullTypeDecl.TypeArgs.Count) {
        // Apparently, the type resolution automatically added type arguments to the iterator. We'll add these to the
        // corresponding non-null type as well.
        Contract.Assert(initiallyNoTypeArguments);
        Contract.Assert(iter.NonNullTypeDecl.TypeArgs.Count == 0);
        var nnt = iter.NonNullTypeDecl;
        nnt.TypeArgs.AddRange(iter.TypeArgs.ConvertAll(tp => new TypeParameter(tp.tok, tp.Name, tp.VarianceSyntax, tp.Characteristics)));
        var varUdt = (UserDefinedType)nnt.Var.Type;
        Contract.Assert(varUdt.TypeArgs.Count == 0);
        varUdt.TypeArgs = nnt.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      }
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      var initialErrorCount = reporter.Count(ErrorLevel.Error);

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      scope.PushMarker();
      scope.AllowInstance = false;  // disallow 'this' from use, which means that the special fields and methods added are not accessible in the syntactically given spec
      iter.Ins.ForEach(p => scope.Push(p.Name, p));

      // Start resolving specification...
      // we start with the decreases clause, because the _decreases<n> fields were only given type proxies before; we'll know
      // the types only after resolving the decreases clause (and it may be that some of resolution has already seen uses of
      // these fields; so, with no further ado, here we go
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        ResolveExpression(e, new ResolveOpts(iter, false));
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        // If the following type constraint does not hold, then: Bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
        ConstrainSubtypeRelation(d.Type, e.Type, e, "type of field {0} is {1}, but has been constrained elsewhere to be of type {2}", d.Name, e.Type, d.Type);
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpression(fe, FrameExpressionUse.Reads, iter);
      }
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpression(fe, FrameExpressionUse.Modifies, iter);
      }
      foreach (MaybeFreeExpression e in iter.Requires) {
        ResolveExpression(e.E, new ResolveOpts(iter, false));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
      }

      scope.PopMarker();  // for the in-parameters

      // We resolve the rest of the specification in an instance context.  So mentions of the in- or yield-parameters
      // get resolved as field dereferences (with an implicit "this")
      scope.PushMarker();
      currentClass = iter;
      Contract.Assert(scope.AllowInstance);

      foreach (MaybeFreeExpression e in iter.YieldRequires) {
        ResolveExpression(e.E, new ResolveOpts(iter, false));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Yield precondition must be a boolean (got {0})");
      }
      foreach (MaybeFreeExpression e in iter.YieldEnsures) {
        ResolveExpression(e.E, new ResolveOpts(iter, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Yield postcondition must be a boolean (got {0})");
      }
      foreach (MaybeFreeExpression e in iter.Ensures) {
        ResolveExpression(e.E, new ResolveOpts(iter, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
      }
      SolveAllTypeConstraints();

      ResolveAttributes(iter.Attributes, iter, new ResolveOpts(iter, false));

      var postSpecErrorCount = reporter.Count(ErrorLevel.Error);

      // Resolve body
      if (iter.Body != null) {
        dominatingStatementLabels.PushMarker();
        foreach (var req in iter.Requires) {
          if (req.Label != null) {
            if (dominatingStatementLabels.Find(req.Label.Name) != null) {
              reporter.Error(MessageSource.Resolver, req.Label.Tok, "assert label shadows a dominating label");
            } else {
              var rr = dominatingStatementLabels.Push(req.Label.Name, req.Label);
              Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
            }
          }
        }
        ResolveBlockStatement(iter.Body, iter);
        dominatingStatementLabels.PopMarker();
        SolveAllTypeConstraints();
      }

      currentClass = null;
      scope.PopMarker();  // pop off the AllowInstance setting

      if (postSpecErrorCount == initialErrorCount) {
        CreateIteratorMethodSpecs(iter);
      }
    }

    /// <summary>
    /// Assumes the specification of the iterator itself has been successfully resolved.
    /// </summary>
    void CreateIteratorMethodSpecs(IteratorDecl iter) {
      Contract.Requires(iter != null);

      // ---------- here comes the constructor ----------
      // same requires clause as the iterator itself
      iter.Member_Init.Req.AddRange(iter.Requires);
      var ens = iter.Member_Init.Ens;
      foreach (var p in iter.Ins) {
        // ensures this.x == x;
        ens.Add(new MaybeFreeExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new IdentifierExpr(p.tok, p.Name))));
      }
      foreach (var p in iter.OutsHistoryFields) {
        // ensures this.ys == [];
        ens.Add(new MaybeFreeExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new SeqDisplayExpr(p.tok, new List<Expression>()))));
      }
      // ensures this.Valid();
      var valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>());
      ens.Add(new MaybeFreeExpression(valid_call));
      // ensures this._reads == old(ReadsClause);
      var modSetSingletons = new List<Expression>();
      Expression frameSet = new SetDisplayExpr(iter.tok, true, modSetSingletons);
      foreach (var fr in iter.Reads.Expressions) {
        if (fr.FieldName != null) {
          reporter.Error(MessageSource.Resolver, fr.tok, "sorry, a reads clause for an iterator is not allowed to designate specific fields");
        } else if (fr.E.Type.IsRefType) {
          modSetSingletons.Add(fr.E);
        } else {
          frameSet = new BinaryExpr(fr.tok, BinaryExpr.Opcode.Add, frameSet, fr.E);
        }
      }
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"),
        new OldExpr(iter.tok, frameSet))));
      // ensures this._modifies == old(ModifiesClause);
      modSetSingletons = new List<Expression>();
      frameSet = new SetDisplayExpr(iter.tok, true, modSetSingletons);
      foreach (var fr in iter.Modifies.Expressions) {
        if (fr.FieldName != null) {
          reporter.Error(MessageSource.Resolver, fr.tok, "sorry, a modifies clause for an iterator is not allowed to designate specific fields");
        } else if (fr.E.Type.IsRefType) {
          modSetSingletons.Add(fr.E);
        } else {
          frameSet = new BinaryExpr(fr.tok, BinaryExpr.Opcode.Add, frameSet, fr.E);
        }
      }
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"),
        new OldExpr(iter.tok, frameSet))));
      // ensures this._new == {};
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
        new SetDisplayExpr(iter.tok, true, new List<Expression>()))));
      // ensures this._decreases0 == old(DecreasesClause[0]) && ...;
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var p = iter.Decreases.Expressions[i];
        ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), iter.DecreasesFields[i].Name),
          new OldExpr(iter.tok, p))));
      }

      // ---------- here comes predicate Valid() ----------
      var reads = iter.Member_Valid.Reads;
      reads.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));  // reads this;
      reads.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"), null));  // reads this._reads;
      reads.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));  // reads this._new;

      // ---------- here comes method MoveNext() ----------
      // requires this.Valid();
      var req = iter.Member_MoveNext.Req;
      valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>());
      req.Add(new MaybeFreeExpression(valid_call));
      // requires YieldRequires;
      req.AddRange(iter.YieldRequires);
      // modifies this, this._modifies, this._new;
      var mod = iter.Member_MoveNext.Mod.Expressions;
      mod.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));
      mod.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"), null));
      mod.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));
      // ensures fresh(_new - old(_new));
      ens = iter.Member_MoveNext.Ens;
      ens.Add(new MaybeFreeExpression(new UnaryOpExpr(iter.tok, UnaryOpExpr.Opcode.Fresh,
        new BinaryExpr(iter.tok, BinaryExpr.Opcode.Sub,
          new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
          new OldExpr(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"))))));
      // ensures null !in _new
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.NotIn,
        new LiteralExpr(iter.tok),
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"))));
      // ensures more ==> this.Valid();
      valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, new List<Expression>());
      ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp,
        new IdentifierExpr(iter.tok, "more"),
        valid_call)));
      // ensures this.ys == if more then old(this.ys) + [this.y] else old(this.ys);
      Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
      for (int i = 0; i < iter.OutsFields.Count; i++) {
        var y = iter.OutsFields[i];
        var ys = iter.OutsHistoryFields[i];
        var ite = new ITEExpr(iter.tok, false, new IdentifierExpr(iter.tok, "more"),
          new BinaryExpr(iter.tok, BinaryExpr.Opcode.Add,
            new OldExpr(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)),
            new SeqDisplayExpr(iter.tok, new List<Expression>() { new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), y.Name) })),
          new OldExpr(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)));
        var eq = new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name), ite);
        ens.Add(new MaybeFreeExpression(eq));
      }
      // ensures more ==> YieldEnsures;
      foreach (var ye in iter.YieldEnsures) {
        ens.Add(new MaybeFreeExpression(
          new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp, new IdentifierExpr(iter.tok, "more"), ye.E),
          ye.IsFree));
      }
      // ensures !more ==> Ensures;
      foreach (var e in iter.Ensures) {
        ens.Add(new MaybeFreeExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp,
          new UnaryOpExpr(iter.tok, UnaryOpExpr.Opcode.Not, new IdentifierExpr(iter.tok, "more")),
          e.E),
          e.IsFree));
      }
      // decreases this._decreases0, this._decreases1, ...;
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var p = iter.Decreases.Expressions[i];
        iter.Member_MoveNext.Decreases.Expressions.Add(new MemberSelectExpr(p.tok, new ThisExpr(p.tok), iter.DecreasesFields[i].Name));
      }
      iter.Member_MoveNext.Decreases.Attributes = iter.Decreases.Attributes;
    }

    // Like the ResolveTypeOptionEnum, but iff the case of AllowPrefixExtend, it also
    // contains a pointer to its Parent class, to fill in default type parameters properly.
    public class ResolveTypeOption
    {
      public readonly ResolveTypeOptionEnum Opt;
      public readonly TypeParameter.ParentType Parent;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant((Opt == ResolveTypeOptionEnum.AllowPrefixExtend) == (Parent != null));
      }

      public ResolveTypeOption(ResolveTypeOptionEnum opt) {
        Contract.Requires(opt != ResolveTypeOptionEnum.AllowPrefixExtend);
        Parent = null;
        Opt = opt;
      }

      public ResolveTypeOption(TypeParameter.ParentType parent) {
        Contract.Requires(parent != null);
        Opt = ResolveTypeOptionEnum.AllowPrefixExtend;
        Parent = parent;
      }
    }

    /// <summary>
    /// If ResolveType/ResolveTypeLenient encounters a (datatype or class) type "C" with no supplied arguments, then
    /// the ResolveTypeOption says what to do.  The last three options take a List as a parameter, which (would have
    /// been supplied as an argument if C# had datatypes instead of just enums, but since C# doesn't) is supplied
    /// as another parameter (called 'defaultTypeArguments') to ResolveType/ResolveTypeLenient.
    /// </summary>
    public enum ResolveTypeOptionEnum
    {
      /// <summary>
      /// never infer type arguments
      /// </summary>
      DontInfer,
      /// <summary>
      /// create a new InferredTypeProxy type for each needed argument
      /// </summary>
      InferTypeProxies,
      /// <summary>
      /// if at most defaultTypeArguments.Count type arguments are needed, use a prefix of defaultTypeArguments
      /// </summary>
      AllowPrefix,
      /// <summary>
      /// same as AllowPrefix, but if more than defaultTypeArguments.Count type arguments are needed, first
      /// extend defaultTypeArguments to a sufficient length
      /// </summary>
      AllowPrefixExtend,
    }

    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// This method differs from the other ResolveType methods in that it looks at the type name given
    /// as a class name.  In other words, if "type" is given as "C" where "C" is a class, then "type" will
    /// silently resolve to the class "C", not the non-null type "C".  Conversely, if "type" is given
    /// as "C?" where "C" is a class, then an error will be emitted (as, to recover from this error,
    /// "type" will resolve to the class "C".
    /// </summary>
    public void ResolveType_ClassName(IToken tok, Type type, ICodeContext context, ResolveTypeOptionEnum eopt, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      Contract.Requires(eopt != ResolveTypeOptionEnum.AllowPrefixExtend);
      ResolveType(tok, type, context, eopt, defaultTypeArguments);
    }

    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// </summary>
    public void ResolveType(IToken tok, Type type, ICodeContext context, ResolveTypeOptionEnum eopt, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      Contract.Requires(eopt != ResolveTypeOptionEnum.AllowPrefixExtend);
      ResolveType(tok, type, context, new ResolveTypeOption(eopt), defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ICodeContext context, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      Contract.Requires(option != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));
      var r = ResolveTypeLenient(tok, type, context, option, defaultTypeArguments, false);
      Contract.Assert(r == null);
    }

    public class ResolveTypeReturn
    {
      public readonly Type ReplacementType;
      public readonly ExprDotName LastComponent;
      public ResolveTypeReturn(Type replacementType, ExprDotName lastComponent) {
        Contract.Requires(replacementType != null);
        Contract.Requires(lastComponent != null);
        ReplacementType = replacementType;
        LastComponent = lastComponent;
      }
    }
    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// One more thing:  if "allowDanglingDotName" is true, then if the resolution would have produced
    ///   an error message that could have been avoided if "type" denoted an identifier sequence one
    ///   shorter, then return an unresolved replacement type where the identifier sequence is one
    ///   shorter.  (In all other cases, the method returns null.)
    /// </summary>
    public ResolveTypeReturn ResolveTypeLenient(IToken tok, Type type, ICodeContext context, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments, bool allowDanglingDotName) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));
      if (type is BitvectorType) {
        var t = (BitvectorType)type;
        // nothing to resolve, but record the fact that this bitvector width is in use
        builtIns.Bitwidths.Add(t.Width);
      } else if (type is BasicType) {
        // nothing to resolve
      } else if (type is MapType) {
        var mt = (MapType)type;
        var errorCount = reporter.Count(ErrorLevel.Error);
        int typeArgumentCount;
        if (mt.HasTypeArg()) {
          ResolveType(tok, mt.Domain, context, option, defaultTypeArguments);
          ResolveType(tok, mt.Range, context, option, defaultTypeArguments);
          typeArgumentCount = 2;
        } else if (option.Opt == ResolveTypeOptionEnum.DontInfer) {
          mt.SetTypeArgs(new InferredTypeProxy(), new InferredTypeProxy());
          typeArgumentCount = 0;
        } else {
          var inferredTypeArgs = new List<Type>();
          FillInTypeArguments(tok, 2, inferredTypeArgs, defaultTypeArguments, option);
          Contract.Assert(inferredTypeArgs.Count <= 2);
          if (inferredTypeArgs.Count == 1) {
            mt.SetTypeArgs(inferredTypeArgs[0], new InferredTypeProxy());
            typeArgumentCount = 1;
          } else if (inferredTypeArgs.Count == 2) {
            mt.SetTypeArgs(inferredTypeArgs[0], inferredTypeArgs[1]);
            typeArgumentCount = 2;
          } else {
            mt.SetTypeArgs(new InferredTypeProxy(), new InferredTypeProxy());
            typeArgumentCount = 0;
          }
        }
        // defaults and auto have been applied; check if we now have the right number of arguments
        if (2 != typeArgumentCount) {
          reporter.Error(MessageSource.Resolver, tok, "Wrong number of type arguments ({0} instead of 2) passed to type: {1}", typeArgumentCount, mt.CollectionTypeName);
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        var errorCount = reporter.Count(ErrorLevel.Error);
        if (t.HasTypeArg()) {
          ResolveType(tok, t.Arg, context, option, defaultTypeArguments);
        } else if (option.Opt != ResolveTypeOptionEnum.DontInfer) {
          var inferredTypeArgs = new List<Type>();
          FillInTypeArguments(tok, 1, inferredTypeArgs, defaultTypeArguments, option);
          if (inferredTypeArgs.Count != 0) {
            Contract.Assert(inferredTypeArgs.Count == 1);
            t.SetTypeArg(inferredTypeArgs[0]);
          }
        }
        if (!t.HasTypeArg()) {
          // defaults and auto have been applied; check if we now have the right number of arguments
          reporter.Error(MessageSource.Resolver, tok, "Wrong number of type arguments (0 instead of 1) passed to type: {0}", t.CollectionTypeName);
          // add a proxy type, to make sure that CollectionType will have have a non-null Arg
          t.SetTypeArg(new InferredTypeProxy());
        }

      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedClass != null || t.ResolvedParam != null) {
          // Apparently, this type has already been resolved
          return null;
        }
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        if (t.NamePath is ExprDotName) {
          var ret = ResolveDotSuffix_Type((ExprDotName)t.NamePath, new ResolveOpts(context, true), allowDanglingDotName, option, defaultTypeArguments);
          if (ret != null) {
            return ret;
          }
        } else {
          var s = (NameSegment)t.NamePath;
          ResolveNameSegment_Type(s, new ResolveOpts(context, true), option, defaultTypeArguments);
        }
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var r = t.NamePath.Resolved as Resolver_IdentifierExpr;
          if (r == null || !(r.Type is Resolver_IdentifierExpr.ResolverType_Type)) {
            reporter.Error(MessageSource.Resolver, t.tok, "expected type");
          } else if (r.Type is Resolver_IdentifierExpr.ResolverType_Type && r.TypeParamDecl != null) {
            t.ResolvedParam = r.TypeParamDecl;
          } else if (r.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            var d = r.Decl;
            if (d is OpaqueTypeDecl) {
              var dd = (OpaqueTypeDecl)d;
              t.ResolvedParam = dd.TheType;
              // resolve like a type parameter, and it may have type parameters if it's an opaque type
              t.ResolvedClass = d;  // Store the decl, so the compiler will generate the fully qualified name
            } else if (d is SubsetTypeDecl || d is NewtypeDecl) {
              var dd = (RedirectingTypeDecl)d;
              var caller = context as ICallable;
              if (caller != null && !(d is SubsetTypeDecl && caller is SpecialFunction)) {
                caller.EnclosingModule.CallGraph.AddEdge(caller, dd);
                if (caller == d) {
                  // detect self-loops here, since they don't show up in the graph's SSC methods
                  reporter.Error(MessageSource.Resolver, d.tok, "recursive constraint dependency involving a {0}: {1} -> {1}", d.WhatKind, d.Name);
                }
              }
              t.ResolvedClass = d;
            } else if (d is DatatypeDecl) {
              var dd = (DatatypeDecl)d;
              var caller = context as ICallable;
              if (caller != null) {
                caller.EnclosingModule.CallGraph.AddEdge(caller, dd);
              }
              t.ResolvedClass = d;
            } else {
              // d is a coinductive datatype or a class, and it may have type parameters
              t.ResolvedClass = d;
            }
            if (option.Opt == ResolveTypeOptionEnum.DontInfer) {
              // don't add anything
            } else if (d.TypeArgs.Count != t.TypeArgs.Count && t.TypeArgs.Count == 0) {
              FillInTypeArguments(t.tok, d.TypeArgs.Count, t.TypeArgs, defaultTypeArguments, option);
            }
            // defaults and auto have been applied; check if we now have the right number of arguments
            if (d.TypeArgs.Count != t.TypeArgs.Count) {
              reporter.Error(MessageSource.Resolver, t.tok, "Wrong number of type arguments ({0} instead of {1}) passed to {2}: {3}", t.TypeArgs.Count, d.TypeArgs.Count, d.WhatKind, t.Name);
            }

          }
        }
        if (t.ResolvedClass == null && t.ResolvedParam == null) {
          // There was some error. Still, we will set one of them to some value to prevent some crashes in the downstream resolution.  The
          // 0-tuple is convenient, because it is always in scope.
          t.ResolvedClass = builtIns.TupleType(t.tok, 0, false);
          // clear out the TypeArgs since 0-tuple doesn't take TypeArg
          t.TypeArgs = new List<Type>();
        }

      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T != null) {
          ResolveType(tok, t.T, context, option, defaultTypeArguments);
        }
      } else if (type is SelfType) {
        // do nothing.
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return null;
    }

    /// <summary>
    /// Adds to "typeArgs" a list of "n" type arguments, possibly extending "defaultTypeArguments".
    /// </summary>
    static void FillInTypeArguments(IToken tok, int n, List<Type> typeArgs, List<TypeParameter> defaultTypeArguments, ResolveTypeOption option) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);
      Contract.Requires(typeArgs != null && typeArgs.Count == 0);
      if (option.Opt == ResolveTypeOptionEnum.InferTypeProxies) {
        // add type arguments that will be inferred
        for (int i = 0; i < n; i++) {
          typeArgs.Add(new InferredTypeProxy());
        }
      } else if (option.Opt == ResolveTypeOptionEnum.AllowPrefix && defaultTypeArguments.Count < n) {
        // there aren't enough default arguments, so don't do anything
      } else {
        // we'll add arguments
        if (option.Opt == ResolveTypeOptionEnum.AllowPrefixExtend) {
          // extend defaultTypeArguments, if needed
          for (int i = defaultTypeArguments.Count; i < n; i++) {
            var tp = new TypeParameter(tok, "_T" + i, i, option.Parent);
            if (option.Parent is IteratorDecl) {
              tp.Characteristics.MustSupportZeroInitialization = true;
            }
            defaultTypeArguments.Add(tp);
          }
        }
        Contract.Assert(n <= defaultTypeArguments.Count);
        // automatically supply a prefix of the arguments from defaultTypeArguments
        for (int i = 0; i < n; i++) {
          typeArgs.Add(new UserDefinedType(defaultTypeArguments[i]));
        }
      }
    }

    public static bool TypeConstraintsIncludeProxy(Type t, TypeProxy proxy) {
      return TypeConstraintsIncludeProxy_Aux(t, proxy, new HashSet<TypeProxy>());
    }
    static bool TypeConstraintsIncludeProxy_Aux(Type t, TypeProxy proxy, ISet<TypeProxy> visited) {
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);  // t is expected to have been normalized first
      Contract.Requires(proxy != null && proxy.T == null);
      Contract.Requires(visited != null);
      var tproxy = t as TypeProxy;
      if (tproxy != null) {
        if (object.ReferenceEquals(tproxy, proxy)) {
          return true;
        } else if (visited.Contains(tproxy)) {
          return false;
        }
        visited.Add(tproxy);
        foreach (var su in tproxy.Subtypes) {
          if (TypeConstraintsIncludeProxy_Aux(su, proxy, visited)) {
            return true;
          }
        }
        foreach (var su in tproxy.Supertypes) {
          if (TypeConstraintsIncludeProxy_Aux(su, proxy, visited)) {
            return true;
          }
        }
      } else {
        // check type arguments of t
        foreach (var ta in t.TypeArgs) {
          var a = ta.Normalize();
          if (TypeConstraintsIncludeProxy_Aux(a, proxy, visited)) {
            return true;
          }
        }
      }
      return false;
    }

    /// <summary>
    /// Returns a resolved type denoting an array type with dimension "dims" and element type "arg".
    /// Callers are expected to provide "arg" as an already resolved type.  (Note, a proxy type is resolved--
    /// only types that contain identifiers stand the possibility of not being resolved.)
    /// </summary>
    Type ResolvedArrayType(IToken tok, int dims, Type arg, ICodeContext context, bool useClassNameType) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      var at = builtIns.ArrayType(tok, dims, new List<Type> { arg }, false, useClassNameType);
      ResolveType(tok, at, context, ResolveTypeOptionEnum.DontInfer, null);
      return at;
    }

    public void ResolveStatement(Statement stmt, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      if (!(stmt is ForallStmt)) {  // forall statements do their own attribute resolution below
        ResolveAttributes(stmt.Attributes, stmt, new ResolveOpts(codeContext, true));
      }
      if (stmt is PredicateStmt) {
        PredicateStmt s = (PredicateStmt)stmt;
        var assertStmt = stmt as AssertStmt;
        if (assertStmt != null && assertStmt.Label != null) {
          if (dominatingStatementLabels.Find(assertStmt.Label.Name) != null) {
            reporter.Error(MessageSource.Resolver, assertStmt.Label.Tok, "assert label shadows a dominating label");
          } else {
            var rr = dominatingStatementLabels.Push(assertStmt.Label.Name, assertStmt.Label);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
        ResolveExpression(s.Expr, new ResolveOpts(codeContext, true));
        Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(s.Expr, "condition is expected to be of type bool, but is {0}");
        if (assertStmt != null && assertStmt.Proof != null) {
          // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave a the proof body
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(assertStmt.Proof, codeContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        }

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        var opts = new ResolveOpts(codeContext, false);
        s.Args.Iter(e => ResolveExpression(e, opts));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        foreach (var expr in s.Exprs) {
          var name = RevealStmt.SingleName(expr);
          var labeledAssert = name == null ? null : dominatingStatementLabels.Find(name) as AssertLabel;
          if (labeledAssert != null) {
            s.LabeledAsserts.Add(labeledAssert);
          } else {
            var opts = new ResolveOpts(codeContext, false, true, false, false);
            if (expr is ApplySuffix) {
              var e = (ApplySuffix)expr;
              var methodCallInfo = ResolveApplySuffix(e, opts, true);
              if (methodCallInfo == null) {
                reporter.Error(MessageSource.Resolver, expr.tok, "function {0} does not have the reveal lemma", e.Lhs);
              } else {
                var call = new CallStmt(methodCallInfo.Tok, s.EndTok, new List<Expression>(), methodCallInfo.Callee, methodCallInfo.Args);
                s.ResolvedStatements.Add(call);
              }
            } else {
              ResolveExpression(expr, opts);
            }
            foreach (var a in s.ResolvedStatements) {
              ResolveStatement(a, codeContext);
            }
          }
        }
      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          Statement target = enclosingStatementLabels.Find(s.TargetLabel);
          if (target == null) {
            reporter.Error(MessageSource.Resolver, s, "break label is undefined or not in scope: {0}", s.TargetLabel);
          } else {
            s.TargetStmt = target;
          }
        } else {
          if (loopStack.Count < s.BreakCount) {
            reporter.Error(MessageSource.Resolver, s, "trying to break out of more loop levels than there are enclosing loops");
          } else {
            Statement target = loopStack[loopStack.Count - s.BreakCount];
            if (target.Labels == null) {
              // make sure there is a label, because the compiler and translator will want to see a unique ID
              target.Labels = new LList<Label>(new Label(target.Tok, null), null);
            }
            s.TargetStmt = target;
          }
        }

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        if (stmt is YieldStmt && !(codeContext is IteratorDecl)) {
          reporter.Error(MessageSource.Resolver, stmt, "yield statement is allowed only in iterators");
        } else if (stmt is ReturnStmt && !(codeContext is Method)) {
          reporter.Error(MessageSource.Resolver, stmt, "return statement is allowed only in method");
        } else if (inBodyInitContext) {
          reporter.Error(MessageSource.Resolver, stmt, "return statement is not allowed before 'new;' in a constructor");
        }
        var s = (ProduceStmt)stmt;
        if (s.rhss != null) {
          var cmc = codeContext as IMethodCodeContext;
          if (cmc == null) {
            // an error has already been reported above
          } else if (cmc.Outs.Count != s.rhss.Count) {
            reporter.Error(MessageSource.Resolver, s, "number of {2} parameters does not match declaration (found {0}, expected {1})", s.rhss.Count, cmc.Outs.Count, kind);
          } else {
            Contract.Assert(s.rhss.Count > 0);
            // Create a hidden update statement using the out-parameter formals, resolve the RHS, and check that the RHS is good.
            List<Expression> formals = new List<Expression>();
            foreach (Formal f in cmc.Outs) {
              Expression produceLhs;
              if (stmt is ReturnStmt) {
                var ident = new IdentifierExpr(f.tok, f.Name);
                // resolve it here to avoid capture into more closely declared local variables
                ident.Var = f;
                ident.Type = ident.Var.Type;
                Contract.Assert(f.Type != null);
                produceLhs = ident;
              } else {
                var yieldIdent = new MemberSelectExpr(f.tok, new ImplicitThisExpr(f.tok), f.Name);
                ResolveExpression(yieldIdent, new ResolveOpts(codeContext, true));
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
            }
            s.hiddenUpdate = new UpdateStmt(s.Tok, s.EndTok, formals, s.rhss, true);
            // resolving the update statement will check for return/yield statement specifics.
            ResolveStatement(s.hiddenUpdate, codeContext);
          }
        } else {// this is a regular return/yield statement.
          s.hiddenUpdate = null;
        }
      } else if (stmt is ConcreteUpdateStatement) {
        ResolveConcreteUpdateStmt((ConcreteUpdateStatement)stmt, codeContext);
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // We have four cases.
        Contract.Assert(s.Update == null || s.Update is AssignSuchThatStmt || s.Update is UpdateStmt || s.Update is AssignOrReturnStmt);
        // 0.  There is no .Update.  This is easy, we will just resolve the locals.
        // 1.  The .Update is an AssignSuchThatStmt.  This is also straightforward:  first
        //     resolve the locals, which adds them to the scope, and then resolve the .Update.
        // 2.  The .Update is an UpdateStmt, which, resolved, means either a CallStmt or a bunch
        //     of parallel AssignStmt's.  Here, the right-hand sides should be resolved before
        //     the local variables have been added to the scope, but the left-hand sides should
        //     resolve to the newly introduced variables.
        // 3.  The .Update is a ":-" statement, for which resolution does two steps:
        //     First, desugar, then run the regular resolution on the desugared AST.
        // To accommodate these options, we first reach into the UpdateStmt, if any, to resolve
        // the left-hand sides of the UpdateStmt.  This will have the effect of shielding them
        // from a subsequent resolution (since expression resolution will do nothing if the .Type
        // field is already assigned.
        // Alright, so it is:

        // Resolve the types of the locals
        foreach (var local in s.Locals) {
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(local.Tok, local.OptionalType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
            local.type = local.OptionalType;
          } else {
            local.type = new InferredTypeProxy();
          }
        }
        // Resolve the UpdateStmt, if any
        if (s.Update is UpdateStmt) {
          var upd = (UpdateStmt)s.Update;
          // resolve the LHS
          Contract.Assert(upd.Lhss.Count == s.Locals.Count);
          for (int i = 0; i < upd.Lhss.Count; i++) {
            var local = s.Locals[i];
            var lhs = (IdentifierExpr)upd.Lhss[i];  // the LHS in this case will be an IdentifierExpr, because that's how the parser creates the VarDeclStmt
            Contract.Assert(lhs.Type == null);  // not yet resolved
            lhs.Var = local;
            lhs.Type = local.Type;
          }
          // resolve the whole thing
          ResolveConcreteUpdateStmt(s.Update, codeContext);
        }
        if (s.Update is AssignOrReturnStmt) {
          var assignOrRet = (AssignOrReturnStmt)s.Update;
          // resolve the LHS
          Contract.Assert(assignOrRet.Lhss.Count == 1);
          Contract.Assert(s.Locals.Count == 1);
          var local = s.Locals[0];
          var lhs = (IdentifierExpr)assignOrRet.Lhss[0];  // the LHS in this case will be an IdentifierExpr, because that's how the parser creates the VarDeclStmt
          Contract.Assert(lhs.Type == null);  // not yet resolved
          lhs.Var = local;
          lhs.Type = local.Type;

          // resolve the whole thing
          ResolveAssignOrReturnStmt(assignOrRet, codeContext);
        }
        // Add the locals to the scope
        foreach (var local in s.Locals) {
          ScopePushAndReport(scope, local, "local-variable");
        }
        // With the new locals in scope, it's now time to resolve the attributes on all the locals
        foreach (var local in s.Locals) {
          ResolveAttributes(local.Attributes, local, new ResolveOpts(codeContext, true));
        }
        // Resolve the AssignSuchThatStmt, if any
        if (s.Update is AssignSuchThatStmt) {
          ResolveConcreteUpdateStmt(s.Update, codeContext);
        }
        // Update the VarDeclStmt's ghost status according to its components
        foreach (var local in s.Locals)
        {
          if (Attributes.Contains(local.Attributes, "assumption"))
          {
            if (currentMethod == null)
            {
              reporter.Error(MessageSource.Resolver, local.Tok, "assumption variable can only be declared in a method");
            }
            ConstrainSubtypeRelation(Type.Bool, local.type, local.Tok, "assumption variable must be of type 'bool'");
            if (!local.IsGhost) {
              reporter.Error(MessageSource.Resolver, local.Tok, "assumption variable must be ghost");
            }
          }
        }
      } else if (stmt is LetStmt) {
        LetStmt s = (LetStmt)stmt;
        foreach (var local in s.LocalVars) {
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(local.Tok, local.OptionalType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
            local.type = local.OptionalType;
          } else {
            local.type = new InferredTypeProxy();
          }
        }
        ResolveExpression(s.RHS, new ResolveOpts(codeContext, true));
        ResolveCasePattern(s.LHS, s.RHS.Type, codeContext);
        // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
        var c = 0;
        foreach (var bv in s.LHS.Vars) {
          ScopePushAndReport(scope, bv, "local_variable");
          c++;
        }
        if (c == 0) {
          // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
          reporter.Error(MessageSource.Resolver, s.LHS.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
        }
      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(s.Lhs, new ResolveOpts(codeContext, true));  // allow ghosts for now, tighted up below
        bool lhsResolvedSuccessfully = reporter.Count(ErrorLevel.Error) == prevErrorCount;
        Contract.Assert(s.Lhs.Type != null);  // follows from postcondition of ResolveExpression
        // check that LHS denotes a mutable variable or a field
        var lhs = s.Lhs.Resolved;
        if (lhs is IdentifierExpr) {
          IVariable var = ((IdentifierExpr)lhs).Var;
          if (var == null) {
            // the LHS didn't resolve correctly; some error would already have been reported
          } else {
            CheckIsLvalue(lhs, codeContext);

            var localVar = var as LocalVariable;
            if (localVar != null && currentMethod != null && Attributes.Contains(localVar.Attributes, "assumption"))
            {
              var rhs = s.Rhs as ExprRhs;
              var expr = (rhs != null ? rhs.Expr : null);
              var binaryExpr = expr as BinaryExpr;
              if (binaryExpr != null
                  && (binaryExpr.Op == BinaryExpr.Opcode.And)
                  && (binaryExpr.E0.Resolved is IdentifierExpr)
                  && ((IdentifierExpr)(binaryExpr.E0.Resolved)).Var == localVar
                  && !currentMethod.AssignedAssumptionVariables.Contains(localVar))
              {
                currentMethod.AssignedAssumptionVariables.Add(localVar);
              }
              else
              {
                reporter.Error(MessageSource.Resolver, stmt, string.Format("there may be at most one assignment to an assumption variable, the RHS of which must match the expression \"{0} && <boolean expression>\"", localVar.Name));
              }
            }
          }
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          if (fse.Member != null) {  // otherwise, an error was reported above
            CheckIsLvalue(fse, codeContext);
          }
        } else if (lhs is SeqSelectExpr) {
          var slhs = (SeqSelectExpr)lhs;
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            Contract.Assert(slhs.Seq.Type != null);
            CheckIsLvalue(slhs, codeContext);
          }

        } else if (lhs is MultiSelectExpr) {
          CheckIsLvalue(lhs, codeContext);

        } else {
          CheckIsLvalue(lhs, codeContext);
        }

        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, new ResolveOpts(codeContext, true));
          Contract.Assert(rr.Expr.Type != null);  // follows from postcondition of ResolveExpression
          AddAssignableConstraint(stmt.Tok, lhsType, rr.Expr.Type, "RHS (of type {1}) not assignable to LHS (of type {0})");
        } else if (s.Rhs is TypeRhs) {
          TypeRhs rr = (TypeRhs)s.Rhs;
          Type t = ResolveTypeRhs(rr, stmt, codeContext);
          AddAssignableConstraint(stmt.Tok, lhsType, t, "type {1} is not assignable to LHS (of type {0})");
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        ResolveCallStmt(s, codeContext, null);

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        ResolveBlockStatement(s, codeContext);
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        if (s.Guard != null) {
          ResolveExpression(s.Guard, new ResolveOpts(codeContext, true));
          Contract.Assert(s.Guard.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(s.Guard, "condition is expected to be of type bool, but is {0}");
        }

        scope.PushMarker();
        if (s.IsBindingGuard) {
          var exists = (ExistsExpr)s.Guard;
          foreach (var v in exists.BoundVars) {
            ScopePushAndReport(scope, v, "bound-variable");
          }
        }
        dominatingStatementLabels.PushMarker();
        ResolveBlockStatement(s.Thn, codeContext);
        dominatingStatementLabels.PopMarker();
        scope.PopMarker();

        if (s.Els != null) {
          dominatingStatementLabels.PushMarker();
          ResolveStatement(s.Els, codeContext);
          dominatingStatementLabels.PopMarker();
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        ResolveAlternatives(s.Alternatives, null, codeContext);

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        var fvs = new HashSet<IVariable>();
        if (s.Guard != null) {
          ResolveExpression(s.Guard, new ResolveOpts(codeContext, true));
          Contract.Assert(s.Guard.Type != null);  // follows from postcondition of ResolveExpression
          Translator.ComputeFreeVariables(s.Guard, fvs);
          ConstrainTypeExprBool(s.Guard, "condition is expected to be of type bool, but is {0}");
        }

        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, codeContext, fvs);

        if (s.Body != null) {
          loopStack.Add(s);  // push
          dominatingStatementLabels.PushMarker();
          ResolveStatement(s.Body, codeContext);
          dominatingStatementLabels.PopMarker();
          loopStack.RemoveAt(loopStack.Count - 1);  // pop
        } else {
          reporter.Warning(MessageSource.Resolver, s.Tok, "note, this loop has no body");
          string text = "havoc {" + Util.Comma(", ", fvs, fv => fv.Name) + "};";  // always terminate with a semi-colon
          reporter.Info(MessageSource.Resolver, s.Tok, text);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        ResolveAlternatives(s.Alternatives, s, codeContext);
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, codeContext, null);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in s.BoundVars) {
          ScopePushAndReport(scope, v, "local-variable");
          ResolveType(v.tok, v.Type, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
        ResolveExpression(s.Range, new ResolveOpts(codeContext, true));
        Contract.Assert(s.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(s.Range, "range restriction in forall statement must be of type bool (instead got {0})");
        foreach (var ens in s.Ens) {
          ResolveExpression(ens.E, new ResolveOpts(codeContext, true));
          Contract.Assert(ens.E.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(ens.E, "ensures condition is expected to be of type bool, but is {0}");
        }
        // Since the range and postconditions are more likely to infer the types of the bound variables, resolve them
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(s.Attributes, s, new ResolveOpts(codeContext, true));

        if (s.Body != null) {
          // clear the labels for the duration of checking the body, because break statements are not allowed to leave a forall statement
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(s.Body, codeContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        } else {
          reporter.Warning(MessageSource.Resolver, s.Tok, "note, this forall statement has no body");
        }
        scope.PopMarker();

        if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
          // determine the Kind and run some additional checks on the body
          if (s.Ens.Count != 0) {
            // The only supported kind with ensures clauses is Proof.
            s.Kind = ForallStmt.BodyKind.Proof;
          } else {
            // There are three special cases:
            // * Assign, which is the only kind of the forall statement that allows a heap update.
            // * Call, which is a single call statement with no side effects or output parameters.
            // * A single calc statement, which is a special case of Proof where the postcondition can be inferred.
            // The effect of Assign and the postcondition of Call will be seen outside the forall
            // statement.
            Statement s0 = s.S0;
            if (s0 is AssignStmt) {
              s.Kind = ForallStmt.BodyKind.Assign;
            } else if (s0 is CallStmt) {
              s.Kind = ForallStmt.BodyKind.Call;
              var call = (CallStmt)s.S0;
              var method = call.Method;
              // if the called method is not in the same module as the ForallCall stmt
              // don't convert it to ForallExpression since the inlined called method's
              // ensure clause might not be resolved correctly(test\dafny3\GenericSort.dfy)
              if (method.EnclosingClass.Module != codeContext.EnclosingModule) {
                s.CanConvert = false;
              }
              // Additional information (namely, the postcondition of the call) will be reported later. But it cannot be
              // done yet, because the specification of the callee may not have been resolved yet.
            } else if (s0 is CalcStmt) {
              s.Kind = ForallStmt.BodyKind.Proof;
              // add the conclusion of the calc as a free postcondition
              var result = ((CalcStmt)s0).Result;
              s.Ens.Add(new MaybeFreeExpression(result, true));
              reporter.Info(MessageSource.Resolver, s.Tok, "ensures " + Printer.ExprToString(result));
            } else {
              s.Kind = ForallStmt.BodyKind.Proof;
              if (s.Body is BlockStmt && ((BlockStmt)s.Body).Body.Count == 0) {
                // an empty statement, so don't produce any warning
              } else {
                reporter.Warning(MessageSource.Resolver, s.Tok, "the conclusion of the body of this forall statement will not be known outside the forall statement; consider using an 'ensures' clause");
              }
            }
          }
          if (s.Body != null) {
            CheckForallStatementBodyRestrictions(s.Body, s.Kind);
          }

          if (s.ForallExpressions != null) {
            foreach (Expression expr in s.ForallExpressions) {
              ResolveExpression(expr, new ResolveOpts(codeContext, true));
            }
          }
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        ResolveAttributes(s.Mod.Attributes, null, new ResolveOpts(codeContext, true));
        foreach (FrameExpression fe in s.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, codeContext);
        }
        if (s.Body != null) {
          ResolveBlockStatement(s.Body, codeContext);
        }

      } else if (stmt is CalcStmt) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        CalcStmt s = (CalcStmt)stmt;
        // figure out s.Op
        Contract.Assert(s.Op == null);  // it hasn't been set yet
        if (s.UserSuppliedOp != null) {
          s.Op = s.UserSuppliedOp;
        } else {
          // Usually, we'd use == as the default main operator.  However, if the calculation
          // begins or ends with a boolean literal, then we can do better by selecting ==>
          // or <==.  Also, if the calculation begins or ends with an empty set, then we can
          // do better by selecting <= or >=.
          if (s.Lines.Count == 0) {
            s.Op = CalcStmt.DefaultOp;
          } else {
            bool b;
            if (Expression.IsBoolLiteral(s.Lines.First(), out b)) {
              s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Imp : BinaryExpr.Opcode.Exp);
            } else if (Expression.IsBoolLiteral(s.Lines.Last(), out b)) {
              s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Exp : BinaryExpr.Opcode.Imp);
            } else if (Expression.IsEmptySetOrMultiset(s.Lines.First())) {
              s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Ge);
            } else if (Expression.IsEmptySetOrMultiset(s.Lines.Last())) {
              s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Le);
            } else {
              s.Op = CalcStmt.DefaultOp;
            }
          }
          reporter.Info(MessageSource.Resolver, s.Tok, s.Op.ToString());
        }

        if (s.Lines.Count > 0) {
          Type lineType = new InferredTypeProxy();
          var e0 = s.Lines.First();
          ResolveExpression(e0, new ResolveOpts(codeContext, true));
          Contract.Assert(e0.Type != null);  // follows from postcondition of ResolveExpression
          var err = new TypeConstraint.ErrorMsgWithToken(e0.tok, "all lines in a calculation must have the same type (got {0} after {1})", e0.Type, lineType);
          ConstrainSubtypeRelation(lineType, e0.Type, err);
          for (int i = 1; i < s.Lines.Count; i++) {
            var e1 = s.Lines[i];
            ResolveExpression(e1, new ResolveOpts(codeContext, true));
            Contract.Assert(e1.Type != null);  // follows from postcondition of ResolveExpression
            // reuse the error object if we're on the dummy line; this prevents a duplicate error message
            if (i < s.Lines.Count - 1) {
              err = new TypeConstraint.ErrorMsgWithToken(e1.tok, "all lines in a calculation must have the same type (got {0} after {1})", e1.Type, lineType);
            }
            ConstrainSubtypeRelation(lineType, e1.Type, err);
            var step = (s.StepOps[i - 1] ?? s.Op).StepExpr(e0, e1); // Use custom line operator
            ResolveExpression(step, new ResolveOpts(codeContext, true));
            s.Steps.Add(step);
            e0 = e1;
          }

          // clear the labels for the duration of checking the hints, because break statements are not allowed to leave a forall statement
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          foreach (var h in s.Hints) {
            foreach (var oneHint in h.Body) {
              dominatingStatementLabels.PushMarker();
              ResolveStatement(oneHint, codeContext);
              dominatingStatementLabels.PopMarker();
            }
          }
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;

        }
        if (prevErrorCount == reporter.Count(ErrorLevel.Error) && s.Lines.Count > 0) {
          // do not build Result from the lines if there were errors, as it might be ill-typed and produce unnecessary resolution errors
          var resultOp = s.StepOps.Aggregate(s.Op, (op0, op1) => op1 == null ? op0 : op0.ResultOp(op1));
          s.Result = resultOp.StepExpr(s.Lines.First(), s.Lines.Last());
        } else {
          s.Result = CalcStmt.DefaultOp.StepExpr(Expression.CreateIntLiteral(s.Tok, 0), Expression.CreateIntLiteral(s.Tok, 0));
        }
        ResolveExpression(s.Result, new ResolveOpts(codeContext, true));
        Contract.Assert(s.Result != null);
        Contract.Assert(prevErrorCount != reporter.Count(ErrorLevel.Error) || s.Steps.Count == s.Hints.Count);

      } else if (stmt is MatchStmt) {
        ResolveMatchStmt((MatchStmt)stmt, codeContext);
      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        reporter.Error(MessageSource.Resolver, s.Tok, "skeleton statements are allowed only in refining methods");
        // nevertheless, resolve the underlying statement; hey, why not
        if (s.S != null) {
          ResolveStatement(s.S, codeContext);
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveLoopSpecificationComponents(List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> modifies, ICodeContext codeContext, HashSet<IVariable> fvs) {
      Contract.Requires(invariants != null);
      Contract.Requires(decreases != null);
      Contract.Requires(modifies != null);
      Contract.Requires(codeContext != null);

      foreach (MaybeFreeExpression inv in invariants) {
        ResolveAttributes(inv.Attributes, null, new ResolveOpts(codeContext, true));
        ResolveExpression(inv.E, new ResolveOpts(codeContext, true));
        Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
        if (fvs != null) {
          Translator.ComputeFreeVariables(inv.E, fvs);
        }
        ConstrainTypeExprBool(inv.E, "invariant is expected to be of type bool, but is {0}");
      }

      ResolveAttributes(decreases.Attributes, null, new ResolveOpts(codeContext, true));
      foreach (Expression e in decreases.Expressions) {
        ResolveExpression(e, new ResolveOpts(codeContext, true));
        if (e is WildcardExpr) {
          if (!codeContext.AllowsNontermination && !DafnyOptions.O.Dafnycc) {
            reporter.Error(MessageSource.Resolver, e, "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating");
          }
        }
        // any type is fine
      }

      ResolveAttributes(modifies.Attributes, null, new ResolveOpts(codeContext, true));
      if (modifies.Expressions != null) {
        foreach (FrameExpression fe in modifies.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, codeContext);
          if (fvs != null) {
            Translator.ComputeFreeVariables(fe.E, fvs);
          }
        }
      }
    }

    void ResolveMatchStmt(MatchStmt s, ICodeContext codeContext) {
      Contract.Requires(s != null);
      Contract.Requires(codeContext != null);
      Contract.Requires(s.OrigUnresolved == null);

      // first, clone the original expression
      s.OrigUnresolved = (MatchStmt)new Cloner().CloneStmt(s);
      ResolveExpression(s.Source, new ResolveOpts(codeContext, true));
      Contract.Assert(s.Source.Type != null);  // follows from postcondition of ResolveExpression
      var errorCount = reporter.Count(ErrorLevel.Error);
      if (s.Source is DatatypeValue) {
        var e = (DatatypeValue)s.Source;
        if (e.Arguments.Count < 1) {
          reporter.Error(MessageSource.Resolver, s.Tok, "match source tuple needs at least 1 argument");
        }
        foreach (var arg in e.Arguments) {
          if (arg is DatatypeValue && ((DatatypeValue)arg).Arguments.Count < 1) {
            reporter.Error(MessageSource.Resolver, s.Tok, "match source tuple needs at least 1 argument");
          }
        }
      }
      if (reporter.Count(ErrorLevel.Error) != errorCount) {
        return;
      }
      var sourceType = PartiallyResolveTypeForMemberSelection(s.Source.tok, s.Source.Type).NormalizeExpand();
      var dtd = sourceType.AsDatatype;
      var subst = new Dictionary<TypeParameter, Type>();
      Dictionary<string, DatatypeCtor> ctors;
      if (dtd == null) {
        reporter.Error(MessageSource.Resolver, s.Source, "the type of the match source expression must be a datatype (instead found {0})", s.Source.Type);
        ctors = null;
      } else {
        ctors = datatypeCtors[dtd];
        Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage

        // build the type-parameter substitution map for this use of the datatype
        subst = TypeSubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs);
      }

      // convert CasePattern in MatchCaseExpr to BoundVar and flatten the MatchCaseExpr.
      List<Tuple<CasePattern<BoundVar>, BoundVar>> patternSubst = new List<Tuple<CasePattern<BoundVar>, BoundVar>>();
      if (dtd != null) {
        DesugarMatchCaseStmt(s, dtd, patternSubst, codeContext);
      }

      ISet<string> memberNamesUsed = new HashSet<string>();
      foreach (MatchCaseStmt mc in s.Cases) {
        DatatypeCtor ctor = null;
        if (ctors != null) {
          Contract.Assert(dtd != null);
          var ctorId = mc.Id;
          if (s.Source.Type.AsDatatype is TupleTypeDecl) {
            var tuple = (TupleTypeDecl)s.Source.Type.AsDatatype;
            var dims = tuple.Dims;
            ctorId = BuiltIns.TupleTypeCtorNamePrefix + dims;
          }
          if (!ctors.TryGetValue(ctorId, out ctor)) {
            reporter.Error(MessageSource.Resolver, mc.tok, "member {0} does not exist in datatype {1}", ctorId, dtd.Name);
          } else {
            Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
            mc.Ctor = ctor;
            if (ctor.Formals.Count != mc.Arguments.Count) {
              if (s.Source.Type.AsDatatype is TupleTypeDecl) {
                reporter.Error(MessageSource.Resolver, mc.tok, "case arguments count does not match source arguments count");
              } else {
                reporter.Error(MessageSource.Resolver, mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", ctorId, mc.Arguments.Count, ctor.Formals.Count);
              }
            }
            if (memberNamesUsed.Contains(ctorId)) {
              reporter.Error(MessageSource.Resolver, mc.tok, "member {0} appears in more than one case", mc.Id);
            } else {
              memberNamesUsed.Add(ctorId);  // add mc.Id to the set of names used
            }
          }
        }
        scope.PushMarker();
        int i = 0;
        if (mc.Arguments != null) {
          foreach (BoundVar v in mc.Arguments) {
            scope.Push(v.Name, v);
            ResolveType(v.tok, v.Type, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            if (ctor != null && i < ctor.Formals.Count) {
              Formal formal = ctor.Formals[i];
              Type st = SubstType(formal.Type, subst);
              ConstrainSubtypeRelation(v.Type, st, s.Tok,
                "the declared type of the formal ({0}) does not agree with the corresponding type in the constructor's signature ({1})", v.Type, st);
              v.IsGhost = formal.IsGhost;

              // update the type of the boundvars in the MatchCaseToken
              if (v.tok is MatchCaseToken) {
                MatchCaseToken mt = (MatchCaseToken)v.tok;
                foreach (Tuple<IToken, BoundVar, bool> entry in mt.varList) {
                  ConstrainSubtypeRelation(entry.Item2.Type, v.Type, entry.Item1, "incorrect type for bound match-case variable (expected {0}, got {1})", v.Type, entry.Item2.Type);
                }
              }
            }
            i++;
          }
        }
        dominatingStatementLabels.PushMarker();
        foreach (Statement ss in mc.Body) {
          ResolveStatement(ss, codeContext);
        }
        dominatingStatementLabels.PopMarker();
        // substitute body to replace the case pat with v. This needs to happen
        // after the body is resolved so we can scope the bv correctly.
        if (patternSubst.Count > 0) {
          var cloner = new MatchCaseExprSubstituteCloner(patternSubst);
          List<Statement> list = new List<Statement>();
          foreach (Statement ss in mc.Body) {
            Statement clone = cloner.CloneStmt(ss);
            // resolve it again since we just cloned it.
            ResolveStatement(clone, codeContext);
            list.Add(clone);
          }
          mc.UpdateBody(list);
        }

        scope.PopMarker();
      }
      if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
        // We could complain about the syntactic omission of constructors:
        //   reporter.Error(MessageSource.Resolver, stmt, "match statement does not cover all constructors");
        // but instead we let the verifier do a semantic check.
        // So, for now, record the missing constructors:
        foreach (var ctr in dtd.Ctors) {
          if (!memberNamesUsed.Contains(ctr.Name)) {
            s.MissingCases.Add(ctr);
          }
        }
        Contract.Assert(memberNamesUsed.Count + s.MissingCases.Count == dtd.Ctors.Count);
      }
    }

    /*
     * Convert
     *   match xs
     *     case Cons(y, Cons(z, zs)) => last(Cons(z, zs))
     *     case Cons(y, Nil) => y
     * To
     *   match xs
     *     case Cons(y, ys) => match ys
     *       case Nil => y
     *       case Cons(z, zs) => last(ys)
     */
    void DesugarMatchCaseStmt(MatchStmt s, DatatypeDecl dtd, List<Tuple<CasePattern<BoundVar>, BoundVar>> patterns, ICodeContext codeContext) {
      Contract.Assert(dtd != null);
      Dictionary<string, DatatypeCtor> ctors = datatypeCtors[dtd];
      if (ctors == null) {
        // there is no constructor, no need to desugar
        return;
      }

      var ctorsList = new List<Dictionary<string, DatatypeCtor>>();
      if (s.Source.Type.AsDatatype is TupleTypeDecl) {
        var udt = s.Source.Type.NormalizeExpand() as UserDefinedType;
        foreach (Type typeArg in udt.TypeArgs) {
          var t = PartiallyResolveTypeForMemberSelection(s.Tok, typeArg).NormalizeExpand() as UserDefinedType;
          if (t != null && t.ResolvedClass is DatatypeDecl) {
            dtd = (DatatypeDecl)t.ResolvedClass;
            ctorsList.Add(datatypeCtors[dtd]);
          } else {
            ctorsList.Add(new Dictionary<string, DatatypeCtor>());
          }
        }
      }
      bool keepOrigToken = true;
      foreach (MatchCaseStmt mc in s.Cases) {
        if (mc.Arguments != null) {
          // already desugared. This happens during the second pass resolver after cloning.
          Contract.Assert(mc.CasePatterns == null);
          return;
        }

        Contract.Assert(mc.Arguments == null);
        Contract.Assert(mc.CasePatterns != null);
        Contract.Assert(ctors != null);
        DatatypeCtor ctor = null;

        if (ctors.TryGetValue(mc.Id, out ctor) || s.Source.Type.AsDatatype is TupleTypeDecl) {
          scope.PushMarker();
          if (s.Source.Type.AsDatatype is TupleTypeDecl) {
            int i = 0;
            foreach (var pat in mc.CasePatterns) {
              FindDuplicateIdentifier(pat, ctorsList[i++], true);
            }
          } else {
            foreach (var pat in mc.CasePatterns) {
              FindDuplicateIdentifier(pat, ctors, true);
            }
          }
          List<BoundVar> arguments = new List<BoundVar>();
          List<Statement> body = mc.Body;
          for (int i = mc.CasePatterns.Count - 1; i >= 0; i--) {
            string name = "_ms#" + i;
            Type type = new InferredTypeProxy();
            BoundVar sourceVar = new BoundVar(new MatchCaseToken(mc.tok), name, type);
            var pat = mc.CasePatterns[i];
            if (pat.Var != null) {
              BoundVar v = pat.Var;
              arguments.Insert(0, v);
            } else {
              body = DesugarMatchCasePattern(mc, pat, sourceVar, body, keepOrigToken);
              patterns.Add(new Tuple<CasePattern<BoundVar>, BoundVar>(pat, sourceVar));
              arguments.Insert(0, sourceVar);
            }
          }
          keepOrigToken = false;
          mc.UpdateBody(body);
          mc.Arguments = arguments;
          mc.CasePatterns = null;
          scope.PopMarker();
        }
      }


      List<MatchCaseStmt> newCases = new List<MatchCaseStmt>();

      // need to consolidate the cases.
      // Convert
      //  match xs
      //    case Cons(y, #mc#0) => match #mc#0
      //                case Cons((z, zs) => body
      //    case Cons(y, #mc#0) => match #mc#0
      //                case Nil => y
      // into
      //  match xs
      //    case Cons(y, #mc#0) => match #mc#0
      //                case Cons((z, zs) => body
      //                case Nil => y
      bool thingsChanged = false;
      Dictionary<string, MatchCaseStmt> caseMap = new Dictionary<string, MatchCaseStmt>();
      List<MatchCaseStmt> mcWithWildCard = new List<MatchCaseStmt>();
      foreach (MatchCaseStmt mc in s.Cases) {
        // check each CasePattern to see if it has wildcard.
        if (CaseExprHasWildCard(mc)) {
          mcWithWildCard.Add(mc);
        } else {
          thingsChanged |= CombineMatchCaseStmt(mc, newCases, caseMap, codeContext);
        }
      }

      foreach (MatchCaseStmt mc in mcWithWildCard) {
        // now process with cases with wildcard
        thingsChanged |= CombineMatchCaseStmt(mc, newCases, caseMap, codeContext);
      }

      if (thingsChanged) {
        s.UpdateCases(newCases);
      }
    }

    void FindDuplicateIdentifier<VT>(CasePattern<VT> pat, Dictionary<string, DatatypeCtor> ctors, bool topLevel) where VT: IVariable {
      Contract.Assert(ctors != null);
      DatatypeCtor ctor = null;
      // Find the constructor in the given datatype
      // If what was parsed was just an identifier, we will interpret it as a datatype constructor, if possible
      if (pat.Var == null || (pat.Var != null && pat.Var.Type is TypeProxy)) {
        if (ctors.TryGetValue(pat.Id, out ctor)) {
          pat.Ctor = ctor;
          pat.Var = default(VT);
        }
      }
      if (pat.Var != null) {
        IVariable v = pat.Var;
        if (topLevel) {
          ScopePushAndReport(scope, v, "parameter");
        } else {
          // For cons(a, const(b, c)):
          // this handles check to see if 'b' or 'c' is duplicate with 'a',
          // the duplication check between 'b' and 'c' is handled in the desugared
          // form (to avoid reporting the same error twice), that is why we don't
          // push 'b' and 'c' onto the scope, only find.
          if (scope.FindInCurrentScope(v.Name) != null) {
            reporter.Error(MessageSource.Resolver, v, "Duplicate parameter name: {0}", v.Name);
          }
        }
      } else {
        if (pat.Arguments != null) {
          foreach (CasePattern<VT> cp in pat.Arguments) {
            FindDuplicateIdentifier(cp, ctors, false);
          }
        }
      }
    }

    List<Statement> DesugarMatchCasePattern(MatchCaseStmt mc, CasePattern<BoundVar> pat, BoundVar v, List<Statement> body, bool keepToken) {
      // convert
      //    case Cons(y, Cons(z, zs)) => body
      // to
      //    case Cons(y, #mc#) => match #mc#
      //            case Cons(z, zs) => body

      Expression source = new NameSegment(new AutoGeneratedToken(pat.tok), v.Name, null);
      List<MatchCaseStmt> cases = new List<MatchCaseStmt>();
      cases.Add(new MatchCaseStmt(pat.tok, pat.Id, pat.Arguments == null ? new List<CasePattern<BoundVar>>() : pat.Arguments, body));
      List<Statement> list = new List<Statement>();
      if (!keepToken) {
        AutoGeneratedTokenCloner cloner = new AutoGeneratedTokenCloner();
        source = cloner.CloneExpr(source);
      }
      list.Add(new MatchStmt(pat.tok, pat.tok, source, cases, false));
      return list;
    }

    bool CombineMatchCaseStmt(MatchCaseStmt mc, List<MatchCaseStmt> newCases, Dictionary<string, MatchCaseStmt> caseMap, ICodeContext codeContext) {
      bool thingsChanged = false;
      MatchCaseStmt old_mc;
      if (caseMap.TryGetValue(mc.Id, out old_mc)) {
        // already has a case with the same ctor, try to consolidate the body.
        List<Statement> oldBody = old_mc.Body;
        List<Statement> body = mc.Body;
        if ((oldBody.Count == 1) && (oldBody[0] is MatchStmt)
            && (body.Count == 1) && (body[0] is MatchStmt)) {
          // both only have on statement and the statement is MatchStmt
          if (SameMatchCaseStmt(old_mc, mc, codeContext)) {
            MatchStmt old = (MatchStmt)old_mc.Body[0];
            MatchStmt current = (MatchStmt)mc.Body[0];
            foreach (MatchCaseStmt c in current.Cases) {
              old.Cases.Add(c);
            }
            // add the token from mc to old_mc so the identifiers will show correctly in the IDE
            List<BoundVar> arguments = new List<BoundVar>();
            Contract.Assert(old_mc.Arguments.Count == mc.Arguments.Count);
            for (int i = 0; i < old_mc.Arguments.Count; i++) {
              var bv = old_mc.Arguments[i];
              MatchCaseToken mcToken;
              if (!(bv.tok is MatchCaseToken)) {
                // create a MatchCaseToken
                mcToken = new MatchCaseToken(bv.tok);
                // clone the bv but with the MatchCaseToken
                var bvNew = new BoundVar(mcToken, bv.Name, bv.Type);
                bvNew.IsGhost = bv.IsGhost;
                arguments.Add(bvNew);
              } else {
                mcToken = (MatchCaseToken)bv.tok;
                arguments.Add(bv);
              }
              mcToken.AddVar(bv.tok, bv, true);
              mcToken.AddVar(mc.Arguments[i].tok, mc.Arguments[i], true);
            }
            old_mc.Arguments = arguments;
            thingsChanged = true;
          }
        } else {
          // duplicate cases, do nothing for now. The error will be reported during resolving
        }
      } else {
        // it is a new case.
        newCases.Add(mc);
        caseMap.Add(mc.Id, mc);
      }
      return thingsChanged;
    }

    bool SameMatchCaseStmt(MatchCaseStmt one, MatchCaseStmt other, ICodeContext codeContext) {
      // this method is called after all the CasePattern in the match cases are converted
      // into BoundVars.
      Contract.Assert(one.CasePatterns == null && one.Arguments != null);
      Contract.Assert(other.CasePatterns == null && other.Arguments != null);
      // In order to combine the two match cases, the bodies need to be a MatchExpr and
      // the arguments and the source of the body are the same.
      // We do string equals since they should be in the same scope.
      if (one.Arguments.Count != other.Arguments.Count) {
        return false;
      }
      List<Statement> body1 = one.Body;
      List<Statement> body2 = other.Body;
      if ((body1.Count != 1) || (body2.Count != 1)) {
        return false;
      }
      if (!(body1[0] is MatchStmt) || !(body2[0] is MatchStmt)) {
       return false;
      }
      var source1 = ((MatchStmt)body1[0]).Source;
      var source2 = ((MatchStmt)body2[0]).Source;
      if (!(source1 is NameSegment) || !(source2 is NameSegment)) {
        return false;
      }
      if (!((NameSegment)source1).Name.Equals(((NameSegment)source2).Name)) {
        return false;
      }
      for (int i = 0; i < one.Arguments.Count; i++) {
        BoundVar bv1 = one.Arguments[i];
        BoundVar bv2 = other.Arguments[i];
        if (!LocalVariable.HasWildcardName(bv1) && !LocalVariable.HasWildcardName(bv2)) {
          if (!bv1.Name.Equals(bv2.Name)) {
            // need to substitute bv2 with bv1 in the matchstmt body
            // what if match body already has the bv?? need to make a new bv
            Type type = new InferredTypeProxy();
            string name = FreshTempVarName("_mc#", codeContext);
            BoundVar bv = new BoundVar(new MatchCaseToken(one.tok), name, type);
            ((MatchCaseToken)bv.tok).AddVar(bv1.tok, bv1, true);
            ((MatchCaseToken)bv.tok).AddVar(bv2.tok, bv2, true);
            SubstituteMatchCaseBoundVar(one, bv1, bv);
            SubstituteMatchCaseBoundVar(other, bv2, bv);
          }
        }
      }
      return true;
    }

    void SubstituteMatchCaseBoundVar(MatchCaseStmt mc, BoundVar oldBv, BoundVar newBv) {
      List<BoundVar> arguments = new List<BoundVar>();
      for (int i = 0; i < mc.Arguments.Count; i++) {
        BoundVar bv = mc.Arguments[i];
        if (bv == oldBv) {
          arguments.Add(newBv);
        } else {
          arguments.Add(bv);
        }
      }
      mc.Arguments = arguments;

      // substitue the oldBv with newBv in the body
      MatchCaseExprSubstituteCloner cloner = new MatchCaseExprSubstituteCloner(oldBv, newBv);
      List<Statement> list = new List<Statement>();
      foreach (Statement ss in mc.Body) {
        Statement clone = cloner.CloneStmt(ss);
        list.Add(clone);
      }
      mc.UpdateBody(list);
    }

    void FillInDefaultLoopDecreases(LoopStmt loopStmt, Expression guard, List<Expression> theDecreases, ICallable enclosingMethod) {
      Contract.Requires(loopStmt != null);
      Contract.Requires(theDecreases != null);

      if (theDecreases.Count == 0 && guard != null) {
        loopStmt.InferredDecreases = true;
        Expression prefix = null;
        foreach (Expression guardConjunct in Expression.Conjuncts(guard)) {
          Expression guess = null;
          BinaryExpr bin = guardConjunct as BinaryExpr;
          if (bin != null) {
            switch (bin.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.Lt:
              case BinaryExpr.ResolvedOpcode.Le:
                // for A < B and A <= B, use the decreases B - A
                guess = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
              case BinaryExpr.ResolvedOpcode.Gt:
                // for A >= B and A > B, use the decreases A - B
                guess = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
                break;
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                if (bin.E0.Type.IsNumericBased()) {
                  // for A != B where A and B are numeric, use the absolute difference between A and B (that is: if A <= B then B-A else A-B)
                  var AminusB = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
                  var BminusA = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
                  var test = Expression.CreateAtMost(bin.E0, bin.E1);
                  guess = Expression.CreateITE(test, BminusA, AminusB);
                }
                break;
              default:
                break;
            }
          }
          if (guess != null) {
            if (prefix != null) {
              // Make the following guess:  if prefix then guess else -1
              guess = Expression.CreateITE(prefix, guess, Expression.CreateIntLiteral(prefix.tok, -1));
            }
            theDecreases.Add(AutoGeneratedExpression.Create(guess));
            break;  // ignore any further conjuncts
          }
          if (prefix == null) {
            prefix = guardConjunct;
          } else {
            prefix = Expression.CreateAnd(prefix, guardConjunct);
          }
        }
      }
      if (enclosingMethod is IteratorDecl) {
        var iter = (IteratorDecl)enclosingMethod;
        var ie = new IdentifierExpr(loopStmt.Tok, iter.YieldCountVariable.Name);
        ie.Var = iter.YieldCountVariable;  // resolve here
        ie.Type = iter.YieldCountVariable.Type;  // resolve here
        theDecreases.Insert(0, AutoGeneratedExpression.Create(ie));
        loopStmt.InferredDecreases = true;
      }
      if (loopStmt.InferredDecreases) {
        string s = "decreases " + Util.Comma(", ", theDecreases, Printer.ExprToString);
        reporter.Info(MessageSource.Resolver, loopStmt.Tok, s);
      }
    }
    private void ResolveConcreteUpdateStmt(ConcreteUpdateStatement s, ICodeContext codeContext) {
      Contract.Requires(codeContext != null);

      // First, resolve all LHS's and expression-looking RHS's.
      int errorCountBeforeCheckingLhs = reporter.Count(ErrorLevel.Error);

      var lhsNameSet = new HashSet<string>();  // used to check for duplicate identifiers on the left (full duplication checking for references and the like is done during verification)
      foreach (var lhs in s.Lhss) {
        var ec = reporter.Count(ErrorLevel.Error);
        ResolveExpression(lhs, new ResolveOpts(codeContext, true));
        if (ec == reporter.Count(ErrorLevel.Error)) {
          if (lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne) {
            reporter.Error(MessageSource.Resolver, lhs, "cannot assign to a range of array elements (try the 'forall' statement)");
          }
        }
      }

      // Resolve RHSs
      if (s is AssignSuchThatStmt) {
        ResolveAssignSuchThatStmt((AssignSuchThatStmt)s, codeContext);
      } else if (s is UpdateStmt) {
        ResolveUpdateStmt((UpdateStmt)s, codeContext, errorCountBeforeCheckingLhs);
      } else if (s is AssignOrReturnStmt) {
        ResolveAssignOrReturnStmt((AssignOrReturnStmt)s, codeContext);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
      ResolveAttributes(s.Attributes, s, new ResolveOpts(codeContext, true));
    }
    /// <summary>
    /// Resolve the RHSs and entire UpdateStmt (LHSs should already have been checked by the caller).
    /// errorCountBeforeCheckingLhs is passed in so that this method can determined if any resolution errors were found during
    /// LHS or RHS checking, because only if no errors were found is update.ResolvedStmt changed.
    /// </summary>
    private void ResolveUpdateStmt(UpdateStmt update, ICodeContext codeContext, int errorCountBeforeCheckingLhs) {
      Contract.Requires(update != null);
      Contract.Requires(codeContext != null);
      IToken firstEffectfulRhs = null;
      MethodCallInformation methodCallInfo = null;
      var j = 0;
      foreach (var rhs in update.Rhss) {
        bool isEffectful;
        if (rhs is TypeRhs) {
          var tr = (TypeRhs)rhs;
          ResolveTypeRhs(tr, update, codeContext);
          isEffectful = tr.InitCall != null;
        } else if (rhs is HavocRhs) {
          isEffectful = false;
        } else {
          var er = (ExprRhs)rhs;
          if (er.Expr is ApplySuffix) {
            var a = (ApplySuffix)er.Expr;
            var cRhs = ResolveApplySuffix(a, new ResolveOpts(codeContext, true), true);
            isEffectful = cRhs != null;
            methodCallInfo = methodCallInfo ?? cRhs;
          } else if (er.Expr is RevealExpr) {
            var r = (RevealExpr)er.Expr;
            var cRhs = ResolveRevealExpr(r, new ResolveOpts(codeContext, true), true);
            isEffectful = cRhs != null;
            methodCallInfo = methodCallInfo ?? cRhs;
          } else {
            ResolveExpression(er.Expr, new ResolveOpts(codeContext, true));
            isEffectful = false;
          }
        }
        if (isEffectful && firstEffectfulRhs == null) {
          firstEffectfulRhs = rhs.Tok;
        }
        j++;
      }

      // figure out what kind of UpdateStmt this is
      if (firstEffectfulRhs == null) {
        if (update.Lhss.Count == 0) {
          Contract.Assert(update.Rhss.Count == 1);  // guaranteed by the parser
          reporter.Error(MessageSource.Resolver, update, "expected method call, found expression");
        } else if (update.Lhss.Count != update.Rhss.Count) {
          reporter.Error(MessageSource.Resolver, update, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", update.Lhss.Count, update.Rhss.Count);
        } else if (reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
          // add the statements here in a sequence, but don't use that sequence later for translation (instead, should translate properly as multi-assignment)
          for (int i = 0; i < update.Lhss.Count; i++) {
            var a = new AssignStmt(update.Tok, update.EndTok, update.Lhss[i].Resolved, update.Rhss[i]);
            update.ResolvedStatements.Add(a);
          }
        }

      } else if (update.CanMutateKnownState) {
        if (1 < update.Rhss.Count) {
          reporter.Error(MessageSource.Resolver, firstEffectfulRhs, "cannot have effectful parameter in multi-return statement.");
        } else { // it might be ok, if it is a TypeRhs
          Contract.Assert(update.Rhss.Count == 1);
          if (methodCallInfo != null) {
            reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "cannot have method call in return statement.");
          } else {
            // we have a TypeRhs
            Contract.Assert(update.Rhss[0] is TypeRhs);
            var tr = (TypeRhs)update.Rhss[0];
            Contract.Assert(tr.InitCall != null); // there were effects, so this must have been a call.
            if (tr.CanAffectPreviouslyKnownExpressions) {
              reporter.Error(MessageSource.Resolver, tr.Tok, "can only have initialization methods which modify at most 'this'.");
            } else if (reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
              var a = new AssignStmt(update.Tok, update.EndTok, update.Lhss[0].Resolved, tr);
              update.ResolvedStatements.Add(a);
            }
          }
        }

      } else {
        // if there was an effectful RHS, that must be the only RHS
        if (update.Rhss.Count != 1) {
          reporter.Error(MessageSource.Resolver, firstEffectfulRhs, "an update statement is allowed an effectful RHS only if there is just one RHS");
        } else if (methodCallInfo == null) {
          // must be a single TypeRhs
          if (update.Lhss.Count != 1) {
            Contract.Assert(2 <= update.Lhss.Count);  // the parser allows 0 Lhss only if the whole statement looks like an expression (not a TypeRhs)
            reporter.Error(MessageSource.Resolver, update.Lhss[1].tok, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", update.Lhss.Count, update.Rhss.Count);
          } else if (reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
            var a = new AssignStmt(update.Tok, update.EndTok, update.Lhss[0].Resolved, update.Rhss[0]);
            update.ResolvedStatements.Add(a);
          }
        } else if (reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
          // a call statement
          var resolvedLhss = new List<Expression>();
          foreach (var ll in update.Lhss) {
            resolvedLhss.Add(ll.Resolved);
          }
          var a = new CallStmt(methodCallInfo.Tok, update.EndTok, resolvedLhss, methodCallInfo.Callee, methodCallInfo.Args);
          update.ResolvedStatements.Add(a);
        }
      }

      foreach (var a in update.ResolvedStatements) {
        ResolveStatement(a, codeContext);
      }
    }

    private void ResolveAssignSuchThatStmt(AssignSuchThatStmt s, ICodeContext codeContext) {
      Contract.Requires(s != null);
      Contract.Requires(codeContext != null);

      if (s.AssumeToken == null) {
        // to ease in the verification of the existence check, only allow local variables as LHSs
        foreach (var lhs in s.Lhss) {
          var ide = lhs.Resolved as IdentifierExpr;
          if (ide == null) {
            reporter.Error(MessageSource.Resolver, lhs, "an assign-such-that statement (without an 'assume' clause) currently only supports local-variable LHSs");
          }
        }
      }

      ResolveExpression(s.Expr, new ResolveOpts(codeContext, true));
      ConstrainTypeExprBool(s.Expr, "type of RHS of assign-such-that statement must be boolean (got {0})");
    }

    private Expression VarDotMethod(IToken tok, string varname, string methodname) {
      return new ApplySuffix(tok, new ExprDotName(tok, new IdentifierExpr(tok, varname), methodname, null), new List<Expression>() { });
    }

    /// <summary>
    /// Desugars "y :- MethodOrExpression" into 
    /// "var temp := MethodOrExpression; if temp.IsFailure() { return temp.PropagateFailure(); } y := temp.Extract();"
    /// and saves the result into s.ResolvedStatements.
    /// </summary>
    private void ResolveAssignOrReturnStmt(AssignOrReturnStmt s, ICodeContext codeContext) {
      // TODO Do I have any responsibilities regarding the use of codeContext? Is it mutable?

      var temp = FreshTempVarName("valueOrError", codeContext);
      var tempType = new InferredTypeProxy();
      s.ResolvedStatements.Add(
        // "var temp := MethodOrExpression;"
        new VarDeclStmt(s.Tok, s.Tok, new List<LocalVariable>() { new LocalVariable(s.Tok, s.Tok, temp, tempType, false) },
          new UpdateStmt(s.Tok, s.Tok, new List<Expression>() { new IdentifierExpr(s.Tok, temp) }, new List<AssignmentRhs>() { new ExprRhs(s.Rhs) })));
      s.ResolvedStatements.Add(
        // "if temp.IsFailure()"
        new IfStmt(s.Tok, s.Tok, false, VarDotMethod(s.Tok, temp, "IsFailure"),
          // THEN: { return temp.PropagateFailure(); }
          new BlockStmt(s.Tok, s.Tok, new List<Statement>() {
            new ReturnStmt(s.Tok, s.Tok, new List<AssignmentRhs>() { new ExprRhs(VarDotMethod(s.Tok, temp, "PropagateFailure"))}),
          }),
          // ELSE: no else block
          null
        ));

      Contract.Assert(s.Lhss.Count <= 1);
      if (s.Lhss.Count == 1)
      {
        // "y := temp.Extract();"
        s.ResolvedStatements.Add(
          new UpdateStmt(s.Tok, s.Tok, s.Lhss, new List<AssignmentRhs>() {
            new ExprRhs(VarDotMethod(s.Tok, temp, "Extract"))}));
      }

      foreach (var a in s.ResolvedStatements) {
        ResolveStatement(a, codeContext);
      }
      bool expectExtract = s.Lhss.Count != 0;
      EnsureSupportsErrorHandling(s.Tok, PartiallyResolveTypeForMemberSelection(s.Tok, tempType), expectExtract);
    }

    private void EnsureSupportsErrorHandling(IToken tok, Type tp, bool expectExtract) {
      // The "method not found" errors which will be generated here were already reported while
      // resolving the statement, so we don't want them to reappear and redirect them into a sink.
      var origReporter = this.reporter;
      this.reporter = new ErrorReporterSink();

      NonProxyType ignoredNptype = null;
      if (ResolveMember(tok, tp, "IsFailure", out ignoredNptype) == null ||
          ResolveMember(tok, tp, "PropagateFailure", out ignoredNptype) == null ||
          (ResolveMember(tok, tp, "Extract", out ignoredNptype) != null) != expectExtract
      ) {
        // more details regarding which methods are missing have already been reported by regular resolution
        origReporter.Error(MessageSource.Resolver, tok,
          "The right-hand side of ':-', which is of type '{0}', must have members 'IsFailure()', 'PropagateFailure()', {1} 'Extract()'", 
          tp, expectExtract ? "and" : "but not");
      }

      this.reporter = origReporter;
    }

    void ResolveAlternatives(List<GuardedAlternative> alternatives, AlternativeLoopStmt loopToCatchBreaks, ICodeContext codeContext) {
      Contract.Requires(alternatives != null);
      Contract.Requires(codeContext != null);

      // first, resolve the guards
      foreach (var alternative in alternatives) {
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(alternative.Guard, new ResolveOpts(codeContext, true));
        Contract.Assert(alternative.Guard.Type != null);  // follows from postcondition of ResolveExpression
        bool successfullyResolved = reporter.Count(ErrorLevel.Error) == prevErrorCount;
        ConstrainTypeExprBool(alternative.Guard, "condition is expected to be of type bool, but is {0}");
      }

      if (loopToCatchBreaks != null) {
        loopStack.Add(loopToCatchBreaks);  // push
      }
      foreach (var alternative in alternatives) {
        scope.PushMarker();
        dominatingStatementLabels.PushMarker();
        if (alternative.IsBindingGuard) {
          var exists = (ExistsExpr)alternative.Guard;
          foreach (var v in exists.BoundVars) {
            ScopePushAndReport(scope, v, "bound-variable");
          }
        }
        foreach (Statement ss in alternative.Body) {
          ResolveStatement(ss, codeContext);
        }
        dominatingStatementLabels.PopMarker();
        scope.PopMarker();
      }
      if (loopToCatchBreaks != null) {
        loopStack.RemoveAt(loopStack.Count - 1);  // pop
      }
    }

    /// <summary>
    /// Resolves the given call statement.
    /// Assumes all LHSs have already been resolved (and checked for mutability).
    /// </summary>
    void ResolveCallStmt(CallStmt s, ICodeContext codeContext, Type receiverType) {
      Contract.Requires(s != null);
      Contract.Requires(codeContext != null);
      bool isInitCall = receiverType != null;

      var callee = s.Method;
      Contract.Assert(callee != null);  // follows from the invariant of CallStmt
      if (!isInitCall && callee is Constructor) {
        reporter.Error(MessageSource.Resolver, s, "a constructor is allowed to be called only when an object is being allocated");
      }

      // resolve left-hand sides
      foreach (var lhs in s.Lhs) {
        Contract.Assume(lhs.Type != null);  // a sanity check that LHSs have already been resolved
      }
      // resolve arguments
      int j = 0;
      foreach (Expression e in s.Args) {
        ResolveExpression(e, new ResolveOpts(codeContext, true));
        j++;
      }

      if (callee.Ins.Count != s.Args.Count) {
        reporter.Error(MessageSource.Resolver, s, "wrong number of method arguments (got {0}, expected {1})", s.Args.Count, callee.Ins.Count);
      } else if (callee.Outs.Count != s.Lhs.Count) {
        if (isInitCall) {
          reporter.Error(MessageSource.Resolver, s, "a method called as an initialization method must not have any result arguments");
        } else {
          reporter.Error(MessageSource.Resolver, s, "wrong number of method result arguments (got {0}, expected {1})", s.Lhs.Count, callee.Outs.Count);
        }
      } else {
        if (isInitCall) {
          if (callee.IsStatic) {
            reporter.Error(MessageSource.Resolver, s.Tok, "a method called as an initialization method must not be 'static'");
          }
        } else if (!callee.IsStatic) {
          if (!scope.AllowInstance && s.Receiver is ThisExpr) {
            // The call really needs an instance, but that instance is given as 'this', which is not
            // available in this context.  For more details, see comment in the resolution of a
            // FunctionCallExpr.
            reporter.Error(MessageSource.Resolver, s.Receiver, "'this' is not allowed in a 'static' context");
          } else if (s.Receiver is StaticReceiverExpr) {
            reporter.Error(MessageSource.Resolver, s.Receiver, "call to instance method requires an instance");
          }
        }
        // type check the arguments
        var subst = s.MethodSelect.TypeArgumentSubstitutions();
        for (int i = 0; i < callee.Ins.Count; i++) {
          var it = callee.Ins[i].Type;
          Type st = SubstType(it, subst);
          AddAssignableConstraint(s.Tok, st, s.Args[i].Type, "incorrect type of method in-parameter" + (callee.Ins.Count == 1 ? "" : " " + i) + " (expected {0}, got {1})");
        }
        for (int i = 0; i < callee.Outs.Count; i++) {
          var it = callee.Outs[i].Type;
          Type st = SubstType(it, subst);
          var lhs = s.Lhs[i];
          AddAssignableConstraint(s.Tok, lhs.Type, st, "incorrect type of method out-parameter" + (callee.Outs.Count == 1 ? "" : " " + i) + " (expected {1}, got {0})");
          // LHS must denote a mutable field.
          CheckIsLvalue(lhs.Resolved, codeContext);
        }

        // Resolution termination check
        ModuleDefinition callerModule = codeContext.EnclosingModule;
        ModuleDefinition calleeModule = ((ICodeContext)callee).EnclosingModule;
        if (callerModule == calleeModule) {
          // intra-module call; add edge in module's call graph
          var caller = codeContext as ICallable;
          if (caller == null) {
            // don't add anything to the call graph after all
          } else if (caller is IteratorDecl) {
            callerModule.CallGraph.AddEdge(((IteratorDecl)caller).Member_MoveNext, callee);
          } else {
            callerModule.CallGraph.AddEdge(caller, callee);
            if (caller == callee) {
              callee.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
            }
          }
        }
      }
      if (Contract.Exists(callee.Decreases.Expressions, e => e is WildcardExpr) && !codeContext.AllowsNontermination) {
        reporter.Error(MessageSource.Resolver, s.Tok, "a call to a possibly non-terminating method is allowed only if the calling method is also declared (with 'decreases *') to be possibly non-terminating");
      }
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    void CheckIsLvalue(Expression lhs, ICodeContext codeContext) {
      Contract.Requires(lhs != null);
      Contract.Requires(codeContext != null);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        if (!ll.Var.IsMutable) {
          reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable variable");
        }
      } else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        var field = ll.Member as Field;
        if (field == null || !field.IsUserMutable) {
          var cf = field as ConstantField;
          if (inBodyInitContext && cf != null && !cf.IsStatic && cf.Rhs == null) {
            if (Expression.AsThis(ll.Obj) != null) {
              // it's cool; this field can be assigned to here
            } else {
              reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable field of 'this'");
            }
          } else {
            reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable field");
          }
        }
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        ConstrainSubtypeRelation(ResolvedArrayType(ll.Seq.tok, 1, new InferredTypeProxy(), codeContext, true), ll.Seq.Type, ll.Seq,
          "LHS of array assignment must denote an array element (found {0})", ll.Seq.Type);
        if (!ll.SelectOne) {
          reporter.Error(MessageSource.Resolver, ll.Seq, "cannot assign to a range of array elements (try the 'forall' statement)");
        }
      } else if (lhs is MultiSelectExpr) {
        // nothing to check; this can only denote an array element
      } else {
        reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable variable or field");
      }
    }

    void ResolveBlockStatement(BlockStmt blockStmt, ICodeContext codeContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(codeContext != null);

      if (blockStmt is DividedBlockStmt) {
        var div = (DividedBlockStmt)blockStmt;
        Contract.Assert(currentMethod is Constructor);  // divided bodies occur only in class constructors
        Contract.Assert(!inBodyInitContext);  // divided bodies are never nested
        inBodyInitContext = true;
        foreach (Statement ss in div.BodyInit) {
          ResolveStatementWithLabels(ss, codeContext);
        }
        Contract.Assert(inBodyInitContext);
        inBodyInitContext = false;
        foreach (Statement ss in div.BodyProper) {
          ResolveStatementWithLabels(ss, codeContext);
        }
      } else {
        foreach (Statement ss in blockStmt.Body) {
          ResolveStatementWithLabels(ss, codeContext);
        }
      }
    }

    void ResolveStatementWithLabels(Statement stmt, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);

      enclosingStatementLabels.PushMarker();
      // push labels
      for (var l = stmt.Labels; l != null; l = l.Next) {
        var lnode = l.Data;
        Contract.Assert(lnode.Name != null);  // LabelNode's with .Label==null are added only during resolution of the break statements with 'stmt' as their target, which hasn't happened yet
        var prev = enclosingStatementLabels.Find(lnode.Name);
        if (prev == stmt) {
          reporter.Error(MessageSource.Resolver, lnode.Tok, "duplicate label");
        } else if (prev != null) {
          reporter.Error(MessageSource.Resolver, lnode.Tok, "label shadows an enclosing label");
        } else {
          var r = enclosingStatementLabels.Push(lnode.Name, stmt);
          Contract.Assert(r == Scope<Statement>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          if (dominatingStatementLabels.Find(lnode.Name) != null) {
            reporter.Error(MessageSource.Resolver, lnode.Tok, "label shadows a dominating label");
          } else {
            var rr = dominatingStatementLabels.Push(lnode.Name, lnode);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
      }
      ResolveStatement(stmt, codeContext);
      enclosingStatementLabels.PopMarker();
    }

    /// <summary>
    /// This method performs some additional checks on the body "stmt" of a forall statement of kind "kind".
    /// </summary>
    public void CheckForallStatementBodyRestrictions(Statement stmt, ForallStmt.BodyKind kind) {
      Contract.Requires(stmt != null);
      if (stmt is PredicateStmt) {
        // cool
      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        foreach (var ss in s.ResolvedStatements) {
          CheckForallStatementBodyRestrictions(ss, kind);
        }
      } else if (stmt is PrintStmt) {
        reporter.Error(MessageSource.Resolver, stmt, "print statement is not allowed inside a forall statement");
      } else if (stmt is BreakStmt) {
        // this case is checked already in the first pass through the forall-statement body, by doing so from an empty set of labeled statements and resetting the loop-stack
      } else if (stmt is ReturnStmt) {
        reporter.Error(MessageSource.Resolver, stmt, "return statement is not allowed inside a forall statement");
      } else if (stmt is YieldStmt) {
        reporter.Error(MessageSource.Resolver, stmt, "yield statement is not allowed inside a forall statement");
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          CheckForallStatementBodyLhs(s.Tok, lhs.Resolved, kind);
        }
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        foreach (var ss in s.ResolvedStatements) {
          CheckForallStatementBodyRestrictions(ss, kind);
        }
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Update != null) {
          CheckForallStatementBodyRestrictions(s.Update, kind);
        }
      } else if (stmt is LetStmt) {
        // Are we fine?
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        CheckForallStatementBodyLhs(s.Tok, s.Lhs.Resolved, kind);
        var rhs = s.Rhs;  // ExprRhs and HavocRhs are fine, but TypeRhs is not
        if (rhs is TypeRhs) {
          if (kind == ForallStmt.BodyKind.Assign) {
            reporter.Error(MessageSource.Resolver, rhs.Tok, "new allocation not supported in forall statements");
          } else {
            reporter.Error(MessageSource.Resolver, rhs.Tok, "new allocation not allowed in ghost context");
          }
        }
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        foreach (var lhs in s.Lhs) {
          var idExpr = lhs as IdentifierExpr;
          if (idExpr != null) {
            if (scope.ContainsDecl(idExpr.Var)) {
              reporter.Error(MessageSource.Resolver, stmt, "body of forall statement is attempting to update a variable declared outside the forall statement");
            }
          } else {
            reporter.Error(MessageSource.Resolver, stmt, "the body of the enclosing forall statement is not allowed to update heap locations");
          }
        }
        if (s.Method.Mod.Expressions.Count != 0) {
          reporter.Error(MessageSource.Resolver, stmt, "the body of the enclosing forall statement is not allowed to update heap locations, so any call must be to a method with an empty modifies clause");
        }
        if (!s.Method.IsGhost) {
          // The reason for this restriction is that the compiler is going to omit the forall statement altogether--it has
          // no effect.  However, print effects are not documented, so to make sure that the compiler does not omit a call to
          // a method that prints something, all calls to non-ghost methods are disallowed.  (Note, if this restriction
          // is somehow lifted in the future, then it is still necessary to enforce s.Method.Mod.Expressions.Count != 0 for
          // calls to non-ghost methods.)
          reporter.Error(MessageSource.Resolver, s, "the body of the enclosing forall statement is not allowed to call non-ghost methods");
        }

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        foreach (var ss in s.Body) {
          CheckForallStatementBodyRestrictions(ss, kind);
        }
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        CheckForallStatementBodyRestrictions(s.Thn, kind);
        if (s.Els != null) {
          CheckForallStatementBodyRestrictions(s.Els, kind);
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckForallStatementBodyRestrictions(ss, kind);
          }
        }

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        if (s.Body != null) {
          CheckForallStatementBodyRestrictions(s.Body, kind);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckForallStatementBodyRestrictions(ss, kind);
          }
        }

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        switch (s.Kind) {
          case ForallStmt.BodyKind.Assign:
            reporter.Error(MessageSource.Resolver, stmt, "a forall statement with heap updates is not allowed inside the body of another forall statement");
            break;
          case ForallStmt.BodyKind.Call:
          case ForallStmt.BodyKind.Proof:
            // these are fine, since they don't update any non-local state
            break;
          default:
            Contract.Assert(false);  // unexpected kind
            break;
        }

      } else if (stmt is CalcStmt) {
          // cool

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        foreach (var kase in s.Cases) {
          foreach (var ss in kase.Body) {
            CheckForallStatementBodyRestrictions(ss, kind);
          }
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    void CheckForallStatementBodyLhs(IToken tok, Expression lhs, ForallStmt.BodyKind kind) {
      var idExpr = lhs as IdentifierExpr;
      if (idExpr != null) {
        if (scope.ContainsDecl(idExpr.Var)) {
          reporter.Error(MessageSource.Resolver, tok, "body of forall statement is attempting to update a variable declared outside the forall statement");
        }
      } else if (kind != ForallStmt.BodyKind.Assign) {
        reporter.Error(MessageSource.Resolver, tok, "the body of the enclosing forall statement is not allowed to update heap locations");
      }
    }

    /// <summary>
    /// Check that a statment is a valid hint for a calculation.
    /// ToDo: generalize the part for compound statements to take a delegate?
    /// </summary>
    public void CheckHintRestrictions(Statement stmt, ISet<LocalVariable> localsAllowedInUpdates) {
      Contract.Requires(stmt != null);
      Contract.Requires(localsAllowedInUpdates != null);
      if (stmt is PredicateStmt) {
        // cool
      } else if (stmt is PrintStmt) {
        // not allowed in ghost context
      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        foreach (var ss in s.ResolvedStatements) {
          CheckHintRestrictions(ss, localsAllowedInUpdates);
        }
      } else if (stmt is BreakStmt) {
        // already checked while resolving hints
      } else if (stmt is ReturnStmt) {
        reporter.Error(MessageSource.Resolver, stmt, "return statement is not allowed inside a hint");
      } else if (stmt is YieldStmt) {
        reporter.Error(MessageSource.Resolver, stmt, "yield statement is not allowed inside a hint");
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          CheckHintLhs(s.Tok, lhs.Resolved, localsAllowedInUpdates);
        }
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        CheckHintLhs(s.Tok, s.Lhs.Resolved, localsAllowedInUpdates);
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        if (s.Method.Mod.Expressions.Count != 0) {
          reporter.Error(MessageSource.Resolver, stmt, "calls to methods with side-effects are not allowed inside a hint");
        }
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        foreach (var ss in s.ResolvedStatements) {
          CheckHintRestrictions(ss, localsAllowedInUpdates);
        }
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        s.Locals.Iter(local => localsAllowedInUpdates.Add(local));
        if (s.Update != null) {
          CheckHintRestrictions(s.Update, localsAllowedInUpdates);
        }
      } else if (stmt is LetStmt) {
        // Are we fine?
      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        var newScopeForLocals = new HashSet<LocalVariable>(localsAllowedInUpdates);
        foreach (var ss in s.Body) {
          CheckHintRestrictions(ss, newScopeForLocals);
        }

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        CheckHintRestrictions(s.Thn, localsAllowedInUpdates);
        if (s.Els != null) {
          CheckHintRestrictions(s.Els, localsAllowedInUpdates);
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckHintRestrictions(ss, localsAllowedInUpdates);
          }
        }

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        if (s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
          reporter.Error(MessageSource.Resolver, s.Mod.Expressions[0].tok, "a while statement used inside a hint is not allowed to have a modifies clause");
        }
        if (s.Body != null) {
          CheckHintRestrictions(s.Body, localsAllowedInUpdates);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        foreach (var alt in s.Alternatives) {
          foreach (var ss in alt.Body) {
            CheckHintRestrictions(ss, localsAllowedInUpdates);
          }
        }

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        switch (s.Kind) {
          case ForallStmt.BodyKind.Assign:
            reporter.Error(MessageSource.Resolver, stmt, "a forall statement with heap updates is not allowed inside a hint");
            break;
          case ForallStmt.BodyKind.Call:
          case ForallStmt.BodyKind.Proof:
            // these are fine, since they don't update any non-local state
            break;
          default:
            Contract.Assert(false);  // unexpected kind
            break;
        }

      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        foreach (var h in s.Hints) {
          CheckHintRestrictions(h, new HashSet<LocalVariable>());
        }

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        foreach (var kase in s.Cases) {
          foreach (var ss in kase.Body) {
            CheckHintRestrictions(ss, localsAllowedInUpdates);
          }
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    void CheckHintLhs(IToken tok, Expression lhs, ISet<LocalVariable> localsAllowedInUpdates) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(localsAllowedInUpdates != null);
      var idExpr = lhs as IdentifierExpr;
      if (idExpr == null) {
        reporter.Error(MessageSource.Resolver, tok, "a hint is not allowed to update heap locations");
      } else if (!localsAllowedInUpdates.Contains(idExpr.Var)) {
        reporter.Error(MessageSource.Resolver, tok, "a hint is not allowed to update a variable declared outside the hint");
      }
    }

    Type ResolveTypeRhs(TypeRhs rr, Statement stmt, ICodeContext codeContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (rr.Type == null) {
        if (rr.ArrayDimensions != null) {
          // ---------- new T[EE]    OR    new T[EE] (elementInit)
          Contract.Assert(rr.Arguments == null && rr.Path == null && rr.InitCall == null);
          ResolveType(stmt.Tok, rr.EType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          int i = 0;
          foreach (Expression dim in rr.ArrayDimensions) {
            Contract.Assert(dim != null);
            ResolveExpression(dim, new ResolveOpts(codeContext, false));
            ConstrainToIntegerType(dim, string.Format("new must use an integer-based expression for the array size (got {{0}}{0})", rr.ArrayDimensions.Count == 1 ? "" : " for index " + i));
            i++;
          }
          rr.Type = ResolvedArrayType(stmt.Tok, rr.ArrayDimensions.Count, rr.EType, codeContext, false);
          if (rr.ElementInit != null) {
            ResolveExpression(rr.ElementInit, new ResolveOpts(codeContext, false));
            // Check
            //     int^N -> rr.EType  :>  rr.ElementInit.Type
            builtIns.CreateArrowTypeDecl(rr.ArrayDimensions.Count);  // TODO: should this be done already in the parser?
            var args = new List<Type>();
            for (int ii = 0; ii < rr.ArrayDimensions.Count; ii++) {
              args.Add(Type.Int);
            }
            var arrowType = new ArrowType(rr.ElementInit.tok, builtIns.ArrowTypeDecls[rr.ArrayDimensions.Count], args, rr.EType);
            string underscores;
            if (rr.ArrayDimensions.Count == 1) {
              underscores = "_";
            } else {
              underscores = "(" + Util.Comma(rr.ArrayDimensions.Count, x => "_") + ")";
            }
            var hintString = string.Format(" (perhaps write '{0} =>' in front of the expression you gave in order to make it an arrow type)", underscores);
            ConstrainSubtypeRelation(arrowType, rr.ElementInit.Type, rr.ElementInit, "array-allocation initialization expression expected to have type '{0}' (instead got '{1}'){2}",
              arrowType, rr.ElementInit.Type, new LazyString_OnTypeEquals(rr.EType, rr.ElementInit.Type, hintString));
          } else if (rr.InitDisplay != null) {
            foreach (var v in rr.InitDisplay) {
              ResolveExpression(v, new ResolveOpts(codeContext, false));
              AddAssignableConstraint(v.tok, rr.EType, v.Type, "initial value must be assignable to array's elements (expected '{0}', got '{1}')");
            }
          }
        } else {
          bool callsConstructor = false;
          if (rr.Arguments == null) {
            ResolveType_ClassName(stmt.Tok, rr.EType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            var udt = rr.EType as UserDefinedType;
            var cl = udt == null ? null : udt.ResolvedClass as NonNullTypeDecl;
            if (cl != null && !(rr.EType.IsTraitType && !rr.EType.NormalizeExpand().IsObjectQ)) {
              // life is good
            } else {
              reporter.Error(MessageSource.Resolver, stmt, "new can be applied only to class types (got {0})", rr.EType);
            }
          } else {
            string initCallName = null;
            IToken initCallTok = null;
            // Resolve rr.Path and do one of three things:
            // * If rr.Path denotes a type, then set EType,initCallName to rr.Path,"_ctor", which sets up a call to the anonymous constructor.
            // * If the all-but-last components of rr.Path denote a type, then do EType,initCallName := allButLast(EType),last(EType)
            // * Otherwise, report an error
            var ret = ResolveTypeLenient(rr.Tok, rr.Path, codeContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null, true);
            if (ret != null) {
              // The all-but-last components of rr.Path denote a type (namely, ret.ReplacementType).
              rr.EType = ret.ReplacementType;
              initCallName = ret.LastComponent.SuffixName;
              initCallTok = ret.LastComponent.tok;
            } else {
              // Either rr.Path resolved correctly as a type or there was no way to drop a last component to make it into something that looked
              // like a type.  In either case, set EType,initCallName to Path,"_ctor" and continue.
              rr.EType = rr.Path;
              initCallName = "_ctor";
              initCallTok = rr.Tok;
            }
            if (!rr.EType.IsRefType) {
              reporter.Error(MessageSource.Resolver, stmt, "new can be applied only to reference types (got {0})", rr.EType);
            } else {
              // ---------- new C.Init(EE)
              Contract.Assert(initCallName != null);
              var prevErrorCount = reporter.Count(ErrorLevel.Error);

              // We want to create a MemberSelectExpr for the initializing method.  To do that, we create a throw-away receiver of the appropriate
              // type, create an dot-suffix expression around this receiver, and then resolve it in the usual way for dot-suffix expressions.
              var lhs = new ImplicitThisExpr_ConstructorCall(initCallTok) { Type = rr.EType };
              var callLhs = new ExprDotName(initCallTok, lhs, initCallName, ret == null ? null : ret.LastComponent.OptTypeArguments);
              ResolveDotSuffix(callLhs, true, rr.Arguments, new ResolveOpts(codeContext, true), true);
              if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
                Contract.Assert(callLhs.ResolvedExpression is MemberSelectExpr);  // since ResolveApplySuffix succeeded and call.Lhs denotes an expression (not a module or a type)
                var methodSel = (MemberSelectExpr)callLhs.ResolvedExpression;
                if (methodSel.Member is Method) {
                  rr.InitCall = new CallStmt(initCallTok, stmt.EndTok, new List<Expression>(), methodSel, rr.Arguments);
                  ResolveCallStmt(rr.InitCall, codeContext, rr.EType);
                  if (rr.InitCall.Method is Constructor) {
                    callsConstructor = true;
                  }
                } else {
                  reporter.Error(MessageSource.Resolver, initCallTok, "object initialization must denote an initializing method or constructor ({0})", initCallName);
                }
              }
            }
          }
          if (rr.EType.IsRefType) {
            var udt = rr.EType.NormalizeExpand() as UserDefinedType;
            if (udt != null) {
              var cl = (ClassDecl)udt.ResolvedClass;  // cast is guaranteed by the call to rr.EType.IsRefType above, together with the "rr.EType is UserDefinedType" test
              if (!callsConstructor && cl.HasConstructor) {
                reporter.Error(MessageSource.Resolver, stmt, "when allocating an object of type '{0}', one of its constructor methods must be called", cl.Name);
              }
            }
          }
          rr.Type = rr.EType;
        }
      }
      return rr.Type;
    }

    class LazyString_OnTypeEquals
    {
      Type t0;
      Type t1;
      string s;
      public LazyString_OnTypeEquals(Type t0, Type t1, string s) {
        Contract.Requires(t0 != null);
        Contract.Requires(t1 != null);
        Contract.Requires(s != null);
        this.t0 = t0;
        this.t1 = t1;
        this.s = s;
      }
      public override string ToString() {
        return t0.Equals(t1) ? s : "";
      }
    }

    MemberDecl ResolveMember(IToken tok, Type receiverType, string memberName, out NonProxyType nptype) {
      Contract.Requires(tok != null);
      Contract.Requires(receiverType != null);
      Contract.Requires(memberName != null);
      Contract.Ensures(Contract.Result<MemberDecl>() == null || Contract.ValueAtReturn(out nptype) != null);

      receiverType = PartiallyResolveTypeForMemberSelection(tok, receiverType, memberName);

      if (receiverType is TypeProxy) {
        reporter.Error(MessageSource.Resolver, tok, "type of the receiver is not fully determined at this program point", receiverType);
        nptype = null;
        return null;
      }
      Contract.Assert(receiverType is NonProxyType);  // there are only two kinds of types: proxies and non-proxies

      UserDefinedType ctype = UserDefinedType.DenotesClass(receiverType);
      if (ctype != null) {
        var cd = (ClassDecl)ctype.ResolvedClass;  // correctness of cast follows from postcondition of DenotesClass
        Contract.Assert(ctype.TypeArgs.Count == cd.TypeArgs.Count);  // follows from the fact that ctype was resolved
        MemberDecl member;
        if (!classMembers[cd].TryGetValue(memberName, out member)) {
          if (memberName == "_ctor") {
            reporter.Error(MessageSource.Resolver, tok, "{0} {1} does not have an anonymous constructor", cd.WhatKind, cd.Name);
          } else {
            reporter.Error(MessageSource.Resolver, tok, "member {0} does not exist in {2} {1}", memberName, cd.Name, cd.WhatKind);
          }
          nptype = null;
          return null;
        } else if (!VisibleInScope(member)) {
          reporter.Error(MessageSource.Resolver, tok, "member '{0}' has not been imported in this scope and cannot be accessed here", memberName);
        } else {
          nptype = ctype;
          return member;
        }
      }

      ValuetypeDecl valuet = null;
      foreach (var vtd in valuetypeDecls) {
        if (vtd.IsThisType(receiverType)) {
          valuet = vtd;
          break;
        }
      }
      if (valuet != null) {
        MemberDecl member;
        if (valuet.Members.TryGetValue(memberName, out member)) {
          nptype = (NonProxyType)receiverType;
          SelfType resultType = null;
          if (member is SpecialFunction) {
            resultType = ((SpecialFunction)member).ResultType as SelfType;
          } else if (member is SpecialField) {
            resultType = ((SpecialField)member).Type as SelfType;
          }
          if (resultType != null) {
            SelfTypeSubstitution = new Dictionary<TypeParameter, Type>();
            SelfTypeSubstitution.Add(resultType.TypeArg, receiverType);
            resultType.ResolvedType = receiverType;
          }
          return member;
        }
      }

      TopLevelDeclWithMembers tltwm = receiverType.AsTopLevelTypeWithMembers;
      if (tltwm != null) {
        MemberDecl member;
        if (!classMembers[tltwm].TryGetValue(memberName, out member)) {
          reporter.Error(MessageSource.Resolver, tok, "member {0} does not exist in {2} {1}", memberName, tltwm.Name, tltwm.WhatKind);
          nptype = null;
          return null;
        } else {
          nptype = (UserDefinedType)receiverType;
          return member;
        }
      }

      reporter.Error(MessageSource.Resolver, tok, "type {0} does not have a member {1}", receiverType, memberName);
      nptype = null;
      return null;
    }

    /// <summary>
    /// Roughly speaking, tries to figure out the head of the type of "t", making as few inference decisions as possible.
    /// More precisely, returns a type that contains all the members of "t"; or if "memberName" is non-null, a type
    /// that at least contains the member "memberName" of "t".  Typically, this type is the head type of "t",
    /// but it may also be a type in a super- or subtype relation to "t".
    /// In some cases, it is necessary to make some inference decisions in order to figure out the type to return.
    /// </summary>
    Type PartiallyResolveTypeForMemberSelection(IToken tok, Type t, string memberName = null, int strength = 0) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);
      t = t.NormalizeExpand();
      if (!(t is TypeProxy)) {
        return t;  // we're good
      }

      // simplify constraints
      PrintTypeConstraintState(10);
      if (strength > 0) {
        var proxySpecializations = new HashSet<TypeProxy>();
        GetRelatedTypeProxies(t, proxySpecializations);
        var anyNewConstraintsAssignable = ConvertAssignableToSubtypeConstraints(proxySpecializations);
        var anyNewConstraintsEquatable = TightenUpEquatable(proxySpecializations);
        if ((strength > 1 && !anyNewConstraintsAssignable && !anyNewConstraintsEquatable) || strength == 10) {
          if (t is TypeProxy) {
            // One more try
            var r = GetBaseTypeFromProxy((TypeProxy)t, new Dictionary<TypeProxy, Type>());
            if (r != null) {
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("  ----> found improvement through GetBaseTypeFromProxy: {0}", r);
              }
              return r;
            }
          }
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> found no improvement, giving up");
          }
          return t;
        }
      }
      PartiallySolveTypeConstraints(false);
      PrintTypeConstraintState(11);
      t = t.NormalizeExpandKeepConstraints();
      var proxy = t as TypeProxy;
      if (proxy == null) {
        return t;  // simplification did the trick
      }
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.Write("DEBUG: Member selection{3}:  {1} :> {0} :> {2}", t,
        Util.Comma(proxy.SupertypesKeepConstraints, su => su.ToString()),
        Util.Comma(proxy.SubtypesKeepConstraints, su => su.ToString()),
        memberName == null ? "" : " (" + memberName + ")");
      }

      var artificialSuper = proxy.InClusterOfArtificial(AllXConstraints);
      if (artificialSuper != null) {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("  ----> use artificial supertype: {0}", artificialSuper);
        }
        return artificialSuper;
      }

      // Look for a meet of head symbols among the proxy's subtypes
      Type meet = null;
      if (MeetOfAllSubtypes(proxy, ref meet, new HashSet<TypeProxy>()) && meet != null) {
        bool isRoot, isLeaf, headIsRoot, headIsLeaf;
        CheckEnds(meet, out isRoot, out isLeaf, out headIsRoot, out headIsLeaf);
        if (meet.IsDatatype) {
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> meet is a datatype: {0}", meet);
          }
          ConstrainSubtypeRelation(t, meet, tok, "Member selection requires a supertype of {0} (got something more like {1})", t, meet);
          return meet;
        } else if (headIsRoot) {
          // we're good to go -- by picking "meet" (whose type parameters have been replaced by fresh proxies), we're not losing any generality
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> improved to {0} through meet", meet);
          }
          AssignProxyAndHandleItsConstraints(proxy, meet, true);
          return proxy.NormalizeExpand();  // we return proxy.T instead of meet, in case the assignment gets hijacked
        } else if (memberName == "_#apply" || memberName == "requires" || memberName == "reads") {
          var generalArrowType = meet.AsArrowType;  // go all the way to the base type, to get to the general arrow type, if any0
          if (generalArrowType != null) {
            // pick the supertype "generalArrowType" of "meet"
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> improved to {0} through meet and function application", generalArrowType);
            }
            ConstrainSubtypeRelation(generalArrowType, t, tok, "Function application requires a subtype of {0} (got something more like {1})", generalArrowType, t);
            return generalArrowType;
          }
        } else if (memberName != null) {
          // If "meet" has a member called "memberName" and no supertype of "meet" does, then we'll pick this meet
          if (meet.IsRefType) {
            var meetExpanded = meet.NormalizeExpand();  // go all the way to the base type, to get to the class
            if (!meetExpanded.IsObjectQ) {
              var cl = ((UserDefinedType)meetExpanded).ResolvedClass as ClassDecl;
              if (cl != null) {
                // TODO: the following could be improved by also supplying an upper bound of the search (computed as a join of the supertypes)
                var plausibleMembers = new HashSet<MemberDecl>();
                FindAllMembers(cl, memberName, plausibleMembers);
                if (plausibleMembers.Count == 1) {
                  var mbr = plausibleMembers.First();
                  if (mbr.EnclosingClass == cl) {
                    if (DafnyOptions.O.TypeInferenceDebug) {
                      Console.WriteLine("  ----> improved to {0} through member-selection meet", meet);
                    }
                    var meetRoot = meet.NormalizeExpand();  // blow passed any constraints
                    ConstrainSubtypeRelation(meetRoot, t, tok, "Member selection requires a subtype of {0} (got something more like {1})", meetRoot, t);
                    return meet;
                  } else {
                    // pick the supertype "mbr.EnclosingClass" of "cl"
                    Contract.Assert(mbr.EnclosingClass is TraitDecl);  // a proper supertype of a ClassDecl must be a TraitDecl
                    var pickItFromHere = new UserDefinedType(tok, mbr.EnclosingClass.Name, mbr.EnclosingClass, new List<Type>());
                    if (DafnyOptions.O.TypeInferenceDebug) {
                      Console.WriteLine("  ----> improved to {0} through meet and member lookup", pickItFromHere);
                    }
                    ConstrainSubtypeRelation(pickItFromHere, meet, tok, "Member selection requires a subtype of {0} (got something more like {1})", pickItFromHere, meet);
                    return pickItFromHere;
                  }
                }
              }
            }
          }
        }
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("  ----> found no improvement, because meet does not determine type enough");
          return t;
        }
      }

      // Compute the join of the proxy's supertypes
      Type join = null;
      if (JoinOfAllSupertypes(proxy, ref join, new HashSet<TypeProxy>(), false) && join != null) {
        // If the join does have the member, then this looks promising. It could be that the
        // type would get further constrained later to pick some subtype (in particular, a
        // subclass that overrides the member) of this join. But this is the best we can do
        // now.
        if (join is TypeProxy) {
          if (proxy == join.Normalize()) {
            // can this really ever happen?
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> found no improvement (other than the proxy itself)");
            }
            return t;
          } else {
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> (merging, then trying to improve further) assigning proxy {0}.T := {1}", proxy, join);
            }
            Contract.Assert(proxy != join);
            proxy.T = join;
            Contract.Assert(t.NormalizeExpand() == join);
            return PartiallyResolveTypeForMemberSelection(tok, t, memberName, strength + 1);
          }
        }
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("  ----> improved to {0} through join", join);
        }
        if (memberName != null) {
          AssignProxyAndHandleItsConstraints(proxy, join, true);
          return proxy.NormalizeExpand();  // we return proxy.T instead of join, in case the assignment gets hijacked
        } else {
          return join;
        }
      }

      // we weren't able to do it
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("  ----> found no improvement using simple things, trying harder once more");
      }
      return PartiallyResolveTypeForMemberSelection(tok, t, memberName, strength + 1);
    }

    private Type/*?*/ GetBaseTypeFromProxy(TypeProxy proxy, Dictionary<TypeProxy,Type/*?*/> determinedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(determinedProxies != null);
      Type t;
      if (determinedProxies.TryGetValue(proxy, out t)) {
        // "t" may be null (meaning search for "proxy" is underway or was unsuccessful) or non-null (search for
        // "proxy" has completed successfully), but we return it in either case
        return t;
      }
      determinedProxies.Add(proxy, null);  // record that search for "proxy" is underway
      // First, go through subtype constraints, treating each as if it were an equality
      foreach (var c in AllTypeConstraints) {
        t = GetBaseTypeFromProxy_Eq(proxy, c.Super, c.Sub, determinedProxies);
        if (t != null) {
          determinedProxies[proxy] = t;
          return t;
        }
      }
      // Next, check XConstraints that can be seen as equality constraints
      foreach (var xc in AllXConstraints) {
        switch (xc.ConstraintName) {
          case "Assignable":
          case "Equatable":
          case "EquatableArg":
            t = GetBaseTypeFromProxy_Eq(proxy, xc.Types[0], xc.Types[1], determinedProxies);
            if (t != null) {
              determinedProxies[proxy] = t;
              return t;
            }
            break;
          case "InSet":
            // etc. TODO
            break;
          default:
            break;
        }
      }
      return null;
    }
    /// <summary>
    /// Tries to find a non-proxy type corresponding to "proxy", under the assumption that "t" equals "u" and
    /// "determinedProxies" assumptions.  In the process, may add to "determinedProxies".
    /// </summary>
    private Type/*?*/ GetBaseTypeFromProxy_Eq(TypeProxy proxy, Type t, Type u, Dictionary<TypeProxy, Type/*?*/> determinedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(determinedProxies != null);
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      t = t.NormalizeExpand();
      u = u.NormalizeExpand();
      return GetBaseTypeFromProxy_EqAux(proxy, t, u, determinedProxies) ?? GetBaseTypeFromProxy_EqAux(proxy, u, t, determinedProxies);
    }
    private Type/*?*/ GetBaseTypeFromProxy_EqAux(TypeProxy proxy, Type t, Type u, Dictionary<TypeProxy, Type/*?*/> determinedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(determinedProxies != null);
      Contract.Requires(t != null && (!(t is TypeProxy) || ((TypeProxy)t).T == null));
      Contract.Requires(u != null && (!(u is TypeProxy) || ((TypeProxy)u).T == null));
      if (t == proxy) {
        if (u is TypeProxy) {
          return GetBaseTypeFromProxy((TypeProxy)u, determinedProxies);
        } else {
          return u;
        }
      } else if (t.ContainsProxy(proxy)) {
        if (u is TypeProxy) {
          u = GetBaseTypeFromProxy((TypeProxy)u, determinedProxies);
          if (u == null) {
            return null;
          }
        }
        if (Type.SameHead(t, u)) {
          Contract.Assert(t.TypeArgs.Count == u.TypeArgs.Count);
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            var r = GetBaseTypeFromProxy_Eq(proxy, t.TypeArgs[i], u.TypeArgs[i], determinedProxies);
            if (r != null) {
              return r;
            }
          }
        }
      }
      return null;
    }

    private void GetRelatedTypeProxies(Type t, ISet<TypeProxy> proxies) {
      Contract.Requires(t != null);
      Contract.Requires(proxies != null);
      var proxy = t.Normalize() as TypeProxy;
      if (proxy == null || proxies.Contains(proxy)) {
        return;
      }
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: GetRelatedTypeProxies: finding {0} interesting", proxy);
      }
      proxies.Add(proxy);
      // close over interesting constraints
      foreach (var c in AllTypeConstraints) {
        var super = c.Super.Normalize();
        if (super.TypeArgs.Exists(ta => ta.Normalize() == proxy)) {
          GetRelatedTypeProxies(c.Sub, proxies);
        }
      }
      foreach (var xc in AllXConstraints) {
        var xc0 = xc.Types[0].Normalize();
        if (xc.ConstraintName == "Assignable" && (xc0 == proxy || xc0.TypeArgs.Exists(ta => ta.Normalize() == proxy))) {
          GetRelatedTypeProxies(xc.Types[1], proxies);
        } else if (xc.ConstraintName == "Innable" && xc.Types[1].Normalize() == proxy) {
          GetRelatedTypeProxies(xc.Types[0], proxies);
        } else if ((xc.ConstraintName == "ModifiesFrame" || xc.ConstraintName == "ReadsFrame") && xc.Types[1].Normalize() == proxy) {
          GetRelatedTypeProxies(xc.Types[0], proxies);
        }
      }
    }

    void FindAllMembers(ClassDecl cl, string memberName, ISet<MemberDecl> foundSoFar) {
      Contract.Requires(cl != null);
      Contract.Requires(memberName != null);
      Contract.Requires(foundSoFar != null);
      MemberDecl member;
      if (classMembers[cl].TryGetValue(memberName, out member)) {
        foundSoFar.Add(member);
      }
      cl.TraitsObj.ForEach(trait => FindAllMembers(trait, memberName, foundSoFar));
    }

    /// <summary>
    /// Attempts to compute the meet of "meet", "t", and all of "t"'s known subtype( constraint)s.  The meet
    /// ignores type parameters.  It is assumed that "meet" on entry already includes the meet of all proxies
    /// in "visited".  The empty meet is represented by "null".
    /// The return is "true" if the meet exists.
    /// </summary>
    bool MeetOfAllSubtypes(Type t, ref Type meet, ISet<TypeProxy> visited) {
      Contract.Requires(t != null);
      Contract.Requires(visited != null);

      t = t.NormalizeExpandKeepConstraints();

      var proxy = t as TypeProxy;
      if (proxy != null) {
        if (visited.Contains(proxy)) {
          return true;
        }
        visited.Add(proxy);

        foreach (var c in proxy.SubtypeConstraints) {
          var s = c.Sub.NormalizeExpandKeepConstraints();
          if (!MeetOfAllSubtypes(s, ref meet, visited)) {
            return false;
          }
        }
        if (meet == null) {
          // also consider "Assignable" constraints
          foreach (var c in AllXConstraints) {
            if (c.ConstraintName == "Assignable" && c.Types[0].Normalize() == proxy) {
              var s = c.Types[1].NormalizeExpandKeepConstraints();
              if (!MeetOfAllSubtypes(s, ref meet, visited)) {
                return false;
              }
            }
          }
        }
        return true;
      }

      if (meet == null) {
        meet = Type.HeadWithProxyArgs(t);
        return true;
      } else if (Type.IsHeadSupertypeOf(meet, t)) {
        // stick with what we've got
        return true;
      } else if (Type.IsHeadSupertypeOf(t, meet)) {
        meet = Type.HeadWithProxyArgs(t);
        return true;
      } else {
        meet = Type.Meet(meet, Type.HeadWithProxyArgs(t), builtIns);  // the only way this can succeed is if we obtain a trait
        Contract.Assert(meet == null || meet.IsObjectQ || (meet is UserDefinedType && ((UserDefinedType)meet).ResolvedClass is TraitDecl));
        return meet != null;
      }
    }

    /// <summary>
    /// Attempts to compute the join of "join", all of "t"'s known supertype( constraint)s, and, if "includeT"
    /// and "t" has no supertype( constraint)s, "t".
    /// The join ignores type parameters. (Really?? --KRML)
    /// It is assumed that "join" on entry already includes the join of all proxies
    /// in "visited".  The empty join is represented by "null".
    /// The return is "true" if the join exists.
    /// </summary>
    bool JoinOfAllSupertypes(Type t, ref Type join, ISet<TypeProxy> visited, bool includeT) {
      Contract.Requires(t != null);
      Contract.Requires(visited != null);

      t = t.NormalizeExpandKeepConstraints();
      var proxy = t as TypeProxy;
      if (proxy != null) {
        if (visited.Contains(proxy)) {
          return true;
        }
        visited.Add(proxy);

        var delegatedToOthers = false;
        foreach (var c in proxy.SupertypeConstraints) {
          var s = c.Super.NormalizeExpandKeepConstraints();
          delegatedToOthers = true;
          if (!JoinOfAllSupertypes(s, ref join, visited, true)) {
            return false;
          }
        }
        if (!delegatedToOthers) {
          // also consider "Assignable" constraints
          foreach (var c in AllXConstraints) {
            if (c.ConstraintName == "Assignable" && c.Types[1].Normalize() == proxy) {
              var s = c.Types[0].NormalizeExpandKeepConstraints();
              delegatedToOthers = true;
              if (!JoinOfAllSupertypes(s, ref join, visited, true)) {
                return false;
              }
            }
          }
        }
        if (delegatedToOthers) {
          return true;
        } else if (!includeT) {
          return true;
        } else if (join == null || join.Normalize() == proxy) {
          join = proxy;
          return true;
        } else {
          return false;
        }
      }

      if (join == null) {
        join = Type.HeadWithProxyArgs(t);
        return true;
      } else if (Type.IsHeadSupertypeOf(t, join)) {
        // stick with what we've got
        return true;
      } else if (Type.IsHeadSupertypeOf(join, t)) {
        join = Type.HeadWithProxyArgs(t);
        return true;
      } else {
        join = Type.Join(join, Type.HeadWithProxyArgs(t), builtIns);
        return join != null;
      }
    }

    public static Dictionary<TypeParameter, Type> TypeSubstitutionMap(List<TypeParameter> formals, List<Type> actuals) {
      Contract.Requires(formals != null);
      Contract.Requires(actuals != null);
      Contract.Requires(formals.Count == actuals.Count);
      var subst = new Dictionary<TypeParameter, Type>();
      for (int i = 0; i < formals.Count; i++) {
        subst.Add(formals[i], actuals[i]);
      }
      return subst;
    }

    /// <summary>
    /// If the substitution has no effect, the return value is pointer-equal to 'type'
    /// </summary>
    public static Type SubstType(Type type, Dictionary<TypeParameter, Type> subst) {
      Contract.Requires(type != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(subst));
      Contract.Ensures(Contract.Result<Type>() != null);

      if (type is BasicType) {
        return type;
      } else if (type is SelfType) {
        Type t;
        if (subst.TryGetValue(((SelfType)type).TypeArg, out t)) {
          return cce.NonNull(t);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unresolved SelfType
        }
      } else if (type is MapType) {
        var t = (MapType)type;
        var dom = SubstType(t.Domain, subst);
        if (dom is InferredTypeProxy) {
          ((InferredTypeProxy)dom).KeepConstraints = true;
        }
        var ran = SubstType(t.Range, subst);
        if (ran is InferredTypeProxy) {
          ((InferredTypeProxy)ran).KeepConstraints = true;
        }
        if (dom == t.Domain && ran == t.Range) {
          return type;
        } else {
          return new MapType(t.Finite, dom, ran);
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        var arg = SubstType(t.Arg, subst);
        if (arg is InferredTypeProxy) {
          ((InferredTypeProxy)arg).KeepConstraints = true;
        }
        if (arg == t.Arg) {
          return type;
        } else if (type is SetType) {
          var st = (SetType)type;
          return new SetType(st.Finite, arg);
        } else if (type is MultiSetType) {
          return new MultiSetType(arg);
        } else if (type is SeqType) {
          return new SeqType(arg);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected collection type
        }
      } else if (type is ArrowType) {
        var t = (ArrowType)type;
        var at = new ArrowType(t.tok, t.Args.ConvertAll(u => SubstType(u, subst)), SubstType(t.Result, subst));
        at.ResolvedClass = t.ResolvedClass;
        return at;
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedParam != null) {
          Type s;
          if (subst.TryGetValue(t.ResolvedParam, out s)) {
            Contract.Assert(t.TypeArgs.Count == 0); // what to do?
            return cce.NonNull(s);
          } else {
            if (t.TypeArgs.Count == 0) {
              return type;
            } else {
              // a type parameter with type arguments--must be an opaque type
              var otp = (OpaqueType_AsParameter)t.ResolvedParam;
              var ocl = (OpaqueTypeDecl)t.ResolvedClass;
              return new UserDefinedType(otp, ocl, t.TypeArgs.ConvertAll(u => SubstType(u, subst)));
            }
          }
        } else if (t.ResolvedClass != null) {
          List<Type> newArgs = null;  // allocate it lazily
          var resolvedClass = t.ResolvedClass;
          var isArrowType = ArrowType.IsPartialArrowTypeName(resolvedClass.Name) || ArrowType.IsTotalArrowTypeName(resolvedClass.Name);
#if TEST_TYPE_SYNONYM_TRANSPARENCY
          if (resolvedClass is TypeSynonymDecl && resolvedClass.Name == "type#synonym#transparency#test") {
            // Usually, all type parameters mentioned in the definition of a type synonym are also type parameters
            // to the type synonym itself, but in this instrumented testing, that is not so, so we also do a substitution
            // in the .Rhs of the synonym.
            var syn = (TypeSynonymDecl)resolvedClass;
            var r = SubstType(syn.Rhs, subst);
            if (r != syn.Rhs) {
              resolvedClass = new TypeSynonymDecl(syn.tok, syn.Name, syn.TypeArgs, syn.Module, r, null);
              newArgs = new List<Type>();
            }
          }
#endif
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            Type p = t.TypeArgs[i];
            Type s = SubstType(p, subst);
            if (s is InferredTypeProxy && !isArrowType) {
              ((InferredTypeProxy)s).KeepConstraints = true;
            }
            if (s != p && newArgs == null) {
              // lazily construct newArgs
              newArgs = new List<Type>();
              for (int j = 0; j < i; j++) {
                newArgs.Add(t.TypeArgs[j]);
              }
            }
            if (newArgs != null) {
              newArgs.Add(s);
            }
          }
          if (newArgs == null) {
            // there were no substitutions
            return type;
          } else {
            // Note, even if t.NamePath is non-null, we don't care to keep that syntactic part of the expression in what we return here
            return new UserDefinedType(t.tok, t.Name, resolvedClass, newArgs);
          }
        } else {
          // there's neither a resolved param nor a resolved class, which means the UserDefinedType wasn't
          // properly resolved; just return it
          return type;
        }
      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T == null) {
          return type;
        }
        var s = SubstType(t.T, subst);
        return s == t.T ? type : s;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    /// <summary>
    /// Check that the type uses formal type parameters in a way that is agreeable with their variance specifications.
    /// "context == Co" says that "type" is allowed to vary in the positive direction.
    /// "context == Contra" says that "type" is allowed to vary in the negative direction.
    /// "context == Inv" says that "type" must not vary at all.
    /// * "leftOfArrow" says that the context is to the left of some arrow
    /// </summary>
    public void CheckVariance(Type type, ICallable enclosingTypeDefinition, TypeParameter.TPVariance context, bool leftOfArrow) {
      Contract.Requires(type != null);
      Contract.Requires(enclosingTypeDefinition != null);

      type = type.Normalize();  // we keep constraints, since subset types have their own type-parameter variance specifications; we also keep synonys, since that gives rise to better error messages
      if (type is BasicType) {
        // fine
      } else if (type is MapType) {
        var t = (MapType)type;
        CheckVariance(t.Domain, enclosingTypeDefinition, context, leftOfArrow);
        CheckVariance(t.Range, enclosingTypeDefinition, context, leftOfArrow);
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        CheckVariance(t.Arg, enclosingTypeDefinition, context, leftOfArrow);
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedParam != null) {
          if (t.ResolvedParam.Variance != TypeParameter.TPVariance.Non && t.ResolvedParam.Variance != context) {
            reporter.Error(MessageSource.Resolver, t.tok, "formal type parameter '{0}' is not used according to its variance specification", t.ResolvedParam.Name);
          } else if (t.ResolvedParam.StrictVariance && leftOfArrow) {
            string hint;
            if (t.ResolvedParam.VarianceSyntax == TypeParameter.TPVarianceSyntax.NonVariant_Strict) {
              hint = string.Format(" (perhaps try declaring '{0}' as '!{0}')", t.ResolvedParam.Name);
            } else {
              Contract.Assert(t.ResolvedParam.VarianceSyntax == TypeParameter.TPVarianceSyntax.Covariant_Strict);
              hint = string.Format(" (perhaps try changing the declaration from '+{0}' to '*{0}')", t.ResolvedParam.Name);
            }
            reporter.Error(MessageSource.Resolver, t.tok, "formal type parameter '{0}' is not used according to its variance specification (it is used left of an arrow){1}", t.ResolvedParam.Name, hint);
          }
        } else {
          var resolvedClass = t.ResolvedClass;
          Contract.Assert(resolvedClass != null);  // follows from that the given type was successfully resolved
          Contract.Assert(resolvedClass.TypeArgs.Count == t.TypeArgs.Count);
          if (leftOfArrow) {
            // we have to be careful about uses of the type being defined
            var cg = enclosingTypeDefinition.EnclosingModule.CallGraph;
            var t0 = resolvedClass as ICallable;
            if (t0 != null && cg.GetSCCRepresentative(t0) == cg.GetSCCRepresentative(enclosingTypeDefinition)) {
              reporter.Error(MessageSource.Resolver, t.tok, "using the type being defined ('{0}') here violates strict positivity, that is, it would cause a logical inconsistency by defining a type whose cardinality exceeds itself (like the Continuum Transfunctioner, you might say its power would then be exceeded only by its mystery)", resolvedClass.Name);
            }
          }
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            Type p = t.TypeArgs[i];
            var tpFormal = resolvedClass.TypeArgs[i];
            CheckVariance(p, enclosingTypeDefinition,
              context == TypeParameter.TPVariance.Non ? context :
              context == TypeParameter.TPVariance.Co ? tpFormal.Variance :
              TypeParameter.Negate(tpFormal.Variance),
              leftOfArrow || !tpFormal.StrictVariance);
          }
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    public static UserDefinedType GetThisType(IToken tok, TopLevelDeclWithMembers cl) {
      Contract.Requires(tok != null);
      Contract.Requires(cl != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      if (cl is ClassDecl cls) {
        return UserDefinedType.FromTopLevelDecl(tok, cls.NonNullTypeDecl, cls.TypeArgs);
      } else {
        return UserDefinedType.FromTopLevelDecl(tok, cl, cl.TypeArgs);
      }
    }

    public static UserDefinedType GetReceiverType(IToken tok, MemberDecl member) {
      Contract.Requires(tok != null);
      Contract.Requires(member != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      return GetThisType(tok, (TopLevelDeclWithMembers)member.EnclosingClass);
    }

    public class ResolveOpts
    {
      public readonly ICodeContext codeContext;
      public readonly bool twoState;
      public readonly bool isReveal;
      public readonly bool isPostCondition;
      public readonly bool InsideOld;

      public ResolveOpts(ICodeContext codeContext, bool twoState) {
        Contract.Requires(codeContext != null);
        this.codeContext = codeContext;
        this.twoState = twoState;
        this.isReveal = false;
        this.isPostCondition = false;
      }

      public ResolveOpts(ICodeContext codeContext, bool twoState, bool isReveal, bool isPostCondition, bool insideOld) {
        Contract.Requires(codeContext != null);
        this.codeContext = codeContext;
        this.twoState = twoState;
        this.isReveal = isReveal;
        this.isPostCondition = isPostCondition;
        this.InsideOld = insideOld;
      }
    }

    /// <summary>
    /// "twoState" implies that "old" and "fresh" expressions are allowed.
    /// </summary>
    public void ResolveExpression(Expression expr, ResolveOpts opts) {
#if TEST_TYPE_SYNONYM_TRANSPARENCY
      ResolveExpressionX(expr, opts);
      // For testing purposes, change the type of "expr" to a type synonym (mwo-ha-ha-ha!)
      var t = expr.Type;
      Contract.Assert(t != null);
      var sd = new TypeSynonymDecl(expr.tok, "type#synonym#transparency#test", new List<TypeParameter>(), codeContext.EnclosingModule, t, null);
      var ts = new UserDefinedType(expr.tok, "type#synonym#transparency#test", sd, new List<Type>(), null);
      expr.DebugTest_ChangeType(ts);
    }
    public void ResolveExpressionX(Expression expr, ResolveOpts opts) {
#endif
      Contract.Requires(expr != null);
      Contract.Requires(opts != null);
      Contract.Ensures(expr.Type != null);
      if (expr.Type != null) {
        // expression has already been resovled
        return;
      }

      // The following cases will resolve the subexpressions and will attempt to assign a type of expr.  However, if errors occur
      // and it cannot be determined what the type of expr is, then it is fine to leave expr.Type as null.  In that case, the end
      // of this method will assign proxy type to the expression, which reduces the number of error messages that are produced
      // while type checking the rest of the program.

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        ResolveExpression(e.E, opts);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ResolveExpression(e.E, opts);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        var errorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(e.E, opts);
        e.Type = e.E.Type;
        AddXConstraint(e.E.tok, "NumericOrBitvector", e.E.Type, "type of unary - must be of a numeric or bitvector type (instead got {0})");
        // Note, e.ResolvedExpression will be filled in during CheckTypeInference, at which time e.Type has been determined

      } else if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;

        if (e is StaticReceiverExpr) {
          StaticReceiverExpr eStatic = (StaticReceiverExpr)e;
          this.ResolveType(eStatic.tok, eStatic.UnresolvedType, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          eStatic.Type = eStatic.UnresolvedType;
        } else {
          if (e.Value == null) {
            e.Type = new InferredTypeProxy();
            AddXConstraint(e.tok, "IsNullableRefType", e.Type, "type of 'null' is a reference type, but it is used as {0}");
          } else if (e.Value is BigInteger) {
            var proxy = new InferredTypeProxy();
            e.Type = proxy;
            ConstrainSubtypeRelation(new IntVarietiesSupertype(), e.Type, e.tok, "integer literal used as if it had type {0}", e.Type);
          } else if (e.Value is Basetypes.BigDec) {
            var proxy = new InferredTypeProxy();
            e.Type = proxy;
            ConstrainSubtypeRelation(new RealVarietiesSupertype(), e.Type, e.tok, "type of real literal is used as {0}", e.Type);
          } else if (e.Value is bool) {
            e.Type = Type.Bool;
          } else if (e is CharLiteralExpr) {
            e.Type = Type.Char;
          } else if (e is StringLiteralExpr) {
            e.Type = Type.String();
            ResolveType(e.tok, e.Type, opts.codeContext, ResolveTypeOptionEnum.DontInfer, null);
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal type
          }
        }
      } else if (expr is ThisExpr) {
        if (!scope.AllowInstance) {
          reporter.Error(MessageSource.Resolver, expr, "'this' is not allowed in a 'static' context");
        }
        if (currentClass is ClassDecl cd && cd.IsDefaultClass) {
          // there's no type
        } else {
          expr.Type = GetThisType(expr.tok, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        e.Var = scope.Find(e.Name);
        if (e.Var != null) {
          expr.Type = e.Var.Type;
        } else {
          reporter.Error(MessageSource.Resolver, expr, "Identifier does not denote a local variable, parameter, or bound variable: {0}", e.Name);
        }

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        TopLevelDecl d;
        if (!moduleInfo.TopLevels.TryGetValue(dtv.DatatypeName, out d)) {
          reporter.Error(MessageSource.Resolver, expr.tok, "Undeclared datatype: {0}", dtv.DatatypeName);
        } else if (d is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)d;
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", dtv.DatatypeName, ad.ModuleNames());
        } else if (!(d is DatatypeDecl)) {
          reporter.Error(MessageSource.Resolver, expr.tok, "Expected datatype: {0}", dtv.DatatypeName);
        } else {
          ResolveDatatypeValue(opts, dtv, (DatatypeDecl)d, null);
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Type elementType = new InferredTypeProxy() { KeepConstraints = true };
        foreach (Expression ee in e.Elements) {
          ResolveExpression(ee, opts);
          Contract.Assert(ee.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(elementType, ee.Type, ee.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", ee.Type, elementType);
        }
        if (expr is SetDisplayExpr) {
          var se = (SetDisplayExpr)expr;
          expr.Type = new SetType(se.Finite, elementType);
        } else if (expr is MultiSetDisplayExpr) {
          expr.Type = new MultiSetType(elementType);
        } else {
          expr.Type = new SeqType(elementType);
        }
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        Type domainType = new InferredTypeProxy();
        Type rangeType = new InferredTypeProxy();
        foreach (ExpressionPair p in e.Elements) {
          ResolveExpression(p.A, opts);
          Contract.Assert(p.A.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(domainType, p.A.Type, p.A.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.A.Type, domainType);
          ResolveExpression(p.B, opts);
          Contract.Assert(p.B.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(rangeType, p.B.Type, p.B.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.B.Type, rangeType);
        }
        expr.Type = new MapType(e.Finite, domainType, rangeType);
      } else if (expr is NameSegment) {
        var e = (NameSegment)expr;
        ResolveNameSegment(e, true, null, opts, false);
        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of type ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        ResolveDotSuffix(e, true, null, opts, false);
        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of type ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        ResolveApplySuffix(e, opts, false);

      } else if (expr is RevealExpr) {
        var e = (RevealExpr)expr;
        ResolveRevealExpr(e, opts, true);
        e.ResolvedExpression = e.Expr;

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        ResolveExpression(e.Obj, opts);
        Contract.Assert(e.Obj.Type != null);  // follows from postcondition of ResolveExpression
        NonProxyType nptype;
        MemberDecl member = ResolveMember(expr.tok, e.Obj.Type, e.MemberName, out nptype);
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (member is Function) {
          var fn = member as Function;
          e.Member = fn;
          if (fn is TwoStateFunction && !opts.twoState) {
            reporter.Error(MessageSource.Resolver, e.tok, "a two-state function can be used only in a two-state context");
          }
          // build the type substitution map
          e.TypeApplication = new List<Type>();
          Dictionary<TypeParameter, Type> subst;
          var ctype = nptype as UserDefinedType;
          if (ctype == null) {
            subst = new Dictionary<TypeParameter, Type>();
          } else {
            subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            // instantiate all type arguments from the functions. no polymorphic application
            e.TypeApplication.AddRange(ctype.TypeArgs);
          }
          foreach (var tp in fn.TypeArgs) {
            Type prox = new InferredTypeProxy();
            subst[tp] = prox;
            e.TypeApplication.Add(prox);
          }
          subst = BuildTypeArgumentSubstitute(subst);
          e.Type = SelectAppropriateArrowType(fn.tok, fn.Formals.ConvertAll(f => SubstType(f.Type, subst)), SubstType(fn.ResultType, subst),
            fn.Reads.Count != 0, fn.Req.Count != 0);
          AddCallGraphEdge(opts.codeContext, fn, e, false);
        } else if (member is Field) {
          var field = (Field)member;
          e.Member = field;
          if (field.EnclosingClass == null) {
            // "field" is some built-in field
            e.TypeApplication = new List<Type>();
          } else {
            e.TypeApplication = field.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
          }
          if (e.Obj is StaticReceiverExpr && !field.IsStatic) {
            reporter.Error(MessageSource.Resolver, expr, "a field must be selected via an object, not just a class name");
          }
          var ctype = nptype as UserDefinedType;
          if (ctype == null) {
            e.Type = field.Type;
          } else {
            Contract.Assert(ctype.ResolvedClass != null); // follows from postcondition of ResolveMember
            // build the type substitution map
            var subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            e.Type = SubstType(field.Type, subst);
          }
          AddCallGraphEdgeForField(opts.codeContext, field, e);
        } else {
          reporter.Error(MessageSource.Resolver, expr, "member {0} in type {1} does not refer to a field or a function", e.MemberName, nptype);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        ResolveSeqSelectExpr(e, opts);

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, opts);
        Contract.Assert(e.Array.Type != null);  // follows from postcondition of ResolveExpression
        Type elementType = new InferredTypeProxy();
        ConstrainSubtypeRelation(ResolvedArrayType(e.Array.tok, e.Indices.Count, elementType, opts.codeContext, true), e.Array.Type, e.Array,
          "array selection requires an array{0} (got {1})", e.Indices.Count, e.Array.Type);
        int i = 0;
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          ResolveExpression(idx, opts);
          Contract.Assert(idx.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainToIntegerType(idx, "array selection requires integer-based numeric indices (got {0} for index " + i + ")");
          i++;
        }
        e.Type = elementType;

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        ResolveExpression(e.Seq, opts);
        Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Index, opts);
        ResolveExpression(e.Value, opts);
        AddXConstraint(expr.tok, "SeqUpdatable", e.Seq.Type, e.Index, e.Value, "update requires a sequence, map, multiset, or datatype (got {0})");
        expr.Type = e.Seq.Type;

      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        ResolveExpression(e.Root, opts);
        var ty = PartiallyResolveTypeForMemberSelection(expr.tok, e.Root.Type);
        if (!ty.IsDatatype) {
          reporter.Error(MessageSource.Resolver, expr, "datatype update expression requires a root expression of a datatype (got {0})", ty);
        } else {
          List<DatatypeCtor> legalSourceConstructors;
          var let = ResolveDatatypeUpdate(expr.tok, e.Root, ty.AsDatatype, e.Updates, opts, out legalSourceConstructors);
          if (let != null) {
            e.ResolvedExpression = let;
            e.LegalSourceConstructors = legalSourceConstructors;
            expr.Type = ty;
          }
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, opts);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        ResolveExpression(e.Function, opts);
        foreach (var arg in e.Args) {
          ResolveExpression(arg, opts);
        }

        // TODO: the following should be replaced by a type-class constraint that constrains the types of e.Function, e.Args[*], and e.Type
        var fnType = e.Function.Type.AsArrowType;
        if (fnType == null) {
          reporter.Error(MessageSource.Resolver, e.tok,
            "non-function expression (of type {0}) is called with parameters", e.Function.Type);
        } else if (fnType.Arity != e.Args.Count) {
          reporter.Error(MessageSource.Resolver, e.tok,
            "wrong number of arguments to function application (function type '{0}' expects {1}, got {2})", fnType,
            fnType.Arity, e.Args.Count);
        } else {
          for (var i = 0; i < fnType.Arity; i++) {
            AddAssignableConstraint(e.Args[i].tok, fnType.Args[i], e.Args[i].Type,
              "type mismatch for argument" + (fnType.Arity == 1 ? "" : " " + i) + " (function expects {0}, got {1})");
          }
        }

        expr.Type = fnType == null ? new InferredTypeProxy() : fnType.Result;

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var elementType = new InferredTypeProxy();
        ResolveExpression(e.N, opts);
        ConstrainToIntegerType(e.N, "sequence construction must use an integer-based expression for the sequence size (got {0})");
        ResolveExpression(e.Initializer, opts);
        var arrowType = new ArrowType(e.tok, builtIns.ArrowTypeDecls[1], new List<Type>() { Type.Int }, elementType);
        var hintString = " (perhaps write '_ =>' in front of the expression you gave in order to make it an arrow type)";
        ConstrainSubtypeRelation(arrowType, e.Initializer.Type, e.Initializer, "sequence-construction initializer expression expected to have type '{0}' (instead got '{1}'){2}",
          arrowType, e.Initializer.Type, new LazyString_OnTypeEquals(elementType, e.Initializer.Type, hintString));
        expr.Type = new SeqType(elementType);

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        ResolveExpression(e.E, opts);
        var elementType = new InferredTypeProxy();
        AddXConstraint(e.E.tok, "MultiSetConvertible", e.E.Type, elementType, "can only form a multiset from a seq or set (got {0})");
        expr.Type = new MultiSetType(elementType);

      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        if (!opts.twoState) {
          reporter.Error(MessageSource.Resolver, expr, "old expressions are not allowed in this context");
        } else if (e.At != null) {
          e.AtLabel = dominatingStatementLabels.Find(e.At);
          if (e.AtLabel == null) {
            reporter.Error(MessageSource.Resolver, expr, "no label '{0}' in scope at this time", e.At);
          }
        }
        ResolveExpression(e.E, new ResolveOpts(opts.codeContext, false, opts.isReveal, opts.isPostCondition, true));
        expr.Type = e.E.Type;

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        if (!opts.twoState) {
          reporter.Error(MessageSource.Resolver, expr, "unchanged expressions are not allowed in this context");
        } else if (e.At != null) {
          e.AtLabel = dominatingStatementLabels.Find(e.At);
          if (e.AtLabel == null) {
            reporter.Error(MessageSource.Resolver, expr, "no label '{0}' in scope at this time", e.At);
          }
        }
        foreach (var fe in e.Frame) {
          ResolveFrameExpression(fe, FrameExpressionUse.Unchanged, opts.codeContext);
        }
        expr.Type = Type.Bool;

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        ResolveExpression(e.E, opts);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not:
            AddXConstraint(e.E.tok, "BooleanBits", e.E.Type, "logical/bitwise negation expects a boolean or bitvector argument (instead got {0})");
            expr.Type = e.E.Type;
            break;
          case UnaryOpExpr.Opcode.Cardinality:
            AddXConstraint(expr.tok, "Sizeable", e.E.Type, "size operator expects a collection argument (instead got {0})");
            expr.Type = Type.Int;
            break;
          case UnaryOpExpr.Opcode.Fresh:
            if (!opts.twoState) {
              reporter.Error(MessageSource.Resolver, expr, "fresh expressions are not allowed in this context");
            }
            // the type of e.E must be either an object or a collection of objects
            AddXConstraint(expr.tok, "Freshable", e.E.Type, "the argument of a fresh expression must denote an object or a collection of objects (instead got {0})");
            expr.Type = Type.Bool;
            break;
          case UnaryOpExpr.Opcode.Allocated:
            // the argument is allowed to have any type at all
            expr.Type = Type.Bool;
            if (2 <= DafnyOptions.O.Allocated &&
              ((opts.codeContext is Function && !opts.InsideOld) || opts.codeContext is ConstantField || opts.codeContext is RedirectingTypeDecl)) {
              var declKind = opts.codeContext is RedirectingTypeDecl ? ((RedirectingTypeDecl)opts.codeContext).WhatKind : ((MemberDecl)opts.codeContext).WhatKind;
              reporter.Error(MessageSource.Resolver, expr, "a {0} definition is not allowed to depend on the set of allocated references", declKind);
            }
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        ResolveExpression(e.E, opts);
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(e.tok, e.ToType, opts.codeContext, new ResolveTypeOption(ResolveTypeOptionEnum.DontInfer), null);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          if (e.ToType.IsNumericBased(Type.NumericPersuation.Int)) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
            AddXConstraint(expr.tok, "NumericOrBitvector", e.E.Type, "type conversion to a real-based type is allowed only from numeric and bitvector types (got {0})");
          } else if (e.ToType.IsBitVectorType) {
            AddXConstraint(expr.tok, "NumericOrBitvector", e.E.Type, "type conversion to a bitvector-based type is allowed only from numeric and bitvector types (got {0})");
          } else if (e.ToType.IsCharType) {
            AddXConstraint(expr.tok, "NumericOrBitvector", e.E.Type, "type conversion to a char type is allowed only from numeric and bitvector types (got {0})");
          } else if (e.ToType.IsBigOrdinalType) {
            AddXConstraint(expr.tok, "NumericOrBitvector", e.E.Type, "type conversion to an ORDINAL type is allowed only from numeric and bitvector types (got {0})");
          } else {
            reporter.Error(MessageSource.Resolver, expr, "type conversions are not supported to this type (got {0})", e.ToType);
          }
          e.Type = e.ToType;
        } else {
          e.Type = new InferredTypeProxy();
        }

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        ResolveExpression(e.E0, opts);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.E1, opts);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case BinaryExpr.Opcode.Iff:
          case BinaryExpr.Opcode.Imp:
          case BinaryExpr.Opcode.Exp:
          case BinaryExpr.Opcode.And:
          case BinaryExpr.Opcode.Or: {
              ConstrainSubtypeRelation(Type.Bool, e.E0.Type, expr, "first argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
              ConstrainSubtypeRelation(Type.Bool, e.E1.Type, expr, "second argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E1.Type);
              expr.Type = Type.Bool;
              break;
            }

          case BinaryExpr.Opcode.Eq:
          case BinaryExpr.Opcode.Neq:
            AddXConstraint(expr.tok, "Equatable", e.E0.Type, e.E1.Type, "arguments must have comparable types (got {0} and {1})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Disjoint:
            Type disjointArgumentsType = new InferredTypeProxy();
            ConstrainSubtypeRelation(disjointArgumentsType, e.E0.Type, expr, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
            ConstrainSubtypeRelation(disjointArgumentsType, e.E1.Type, expr, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
            AddXConstraint(expr.tok, "Disjointable", disjointArgumentsType, "arguments must be of a [multi]set or map type (got {0})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le: {
              if (e.Op == BinaryExpr.Opcode.Lt && (e.E0.Type.IsIndDatatype || e.E0.Type.IsTypeParameter || e.E1.Type.IsIndDatatype)) {
                AddXConstraint(expr.tok, "RankOrderable", e.E0.Type, e.E1.Type, "arguments to rank comparison must be datatypes (got {0} and {1})");
                e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankLt;
              } else {
                var cmpType = new InferredTypeProxy();
                var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
                ConstrainSubtypeRelation(cmpType, e.E0.Type, err);
                ConstrainSubtypeRelation(cmpType, e.E1.Type, err);
                AddXConstraint(expr.tok, "Orderable_Lt", e.E0.Type, e.E1.Type,
                  "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got {0} and {1})");
              }
              expr.Type = Type.Bool;
            }
            break;

          case BinaryExpr.Opcode.Gt:
          case BinaryExpr.Opcode.Ge: {
              if (e.Op == BinaryExpr.Opcode.Gt && (e.E0.Type.IsIndDatatype || e.E1.Type.IsIndDatatype || e.E1.Type.IsTypeParameter)) {
                AddXConstraint(expr.tok, "RankOrderable", e.E1.Type, e.E0.Type, "arguments to rank comparison must be datatypes (got {1} and {0})");
                e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankGt;
              } else {
                var cmpType = new InferredTypeProxy();
                var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
                ConstrainSubtypeRelation(cmpType, e.E0.Type, err);
                ConstrainSubtypeRelation(cmpType, e.E1.Type, err);
                AddXConstraint(expr.tok, "Orderable_Gt", e.E0.Type, e.E1.Type,
                  "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0} and {1})");
              }
              expr.Type = Type.Bool;
            }
            break;

          case BinaryExpr.Opcode.LeftShift:
          case BinaryExpr.Opcode.RightShift: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "IsBitvector", expr.Type, "type of " + BinaryExpr.OpcodeString(e.Op) + " must be a bitvector type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              AddXConstraint(expr.tok, "IntLikeOrBitvector", e.E1.Type, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must be an integer-numeric or bitvector type");
            }
            break;

          case BinaryExpr.Opcode.Add: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Plussable", expr.Type, "type of + must be of a numeric type, a bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to + ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to + ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.Sub: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Minusable", expr.Type, "type of - must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to - ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to - ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.Mul: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Mullable", expr.Type, "type of * must be of a numeric type, bitvector type, or a set-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to * ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to * ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            AddXConstraint(expr.tok, "Innable", e.E1.Type, e.E0.Type, "second argument to \"" + BinaryExpr.OpcodeString(e.Op) + "\" must be a set, multiset, or sequence with elements of type {1}, or a map with domain {1} (instead got {0})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Div:
            expr.Type = new InferredTypeProxy();
            AddXConstraint(expr.tok, "NumericOrBitvector", expr.Type, "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be numeric or bitvector types (got {0})");
            ConstrainSubtypeRelation(expr.Type, e.E0.Type,
              expr, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E0.Type, expr.Type);
            ConstrainSubtypeRelation(expr.Type, e.E1.Type,
              expr, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E1.Type, expr.Type);
            break;

          case BinaryExpr.Opcode.Mod:
            expr.Type = new InferredTypeProxy();
            AddXConstraint(expr.tok, "IntLikeOrBitvector", expr.Type, "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be integer-numeric or bitvector types (got {0})");
            ConstrainSubtypeRelation(expr.Type, e.E0.Type,
              expr, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E0.Type, expr.Type);
            ConstrainSubtypeRelation(expr.Type, e.E1.Type,
              expr, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E1.Type, expr.Type);
            break;

          case BinaryExpr.Opcode.BitwiseAnd:
          case BinaryExpr.Opcode.BitwiseOr:
          case BinaryExpr.Opcode.BitwiseXor:
            expr.Type = NewIntegerBasedProxy(expr.tok);
            var errFormat = "first argument to " + BinaryExpr.OpcodeString(e.Op) + " must be of a bitvector type (instead got {0})";
            ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr, errFormat, e.E0.Type);
            AddXConstraint(expr.tok, "IsBitvector", e.E0.Type, errFormat);
            errFormat = "second argument to " + BinaryExpr.OpcodeString(e.Op) + " must be of a bitvector type (instead got {0})";
            ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr, errFormat, e.E1.Type);
            AddXConstraint(expr.tok, "IsBitvector", e.E1.Type, errFormat);
            break;

          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
        }
        // We should also fill in e.ResolvedOp, but we may not have enough information for that yet.  So, instead, delay
        // setting e.ResolvedOp until inside CheckTypeInference.

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        ResolveExpression(e.E0, opts);
        ResolveExpression(e.E1, opts);
        ResolveExpression(e.E2, opts);
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            AddXConstraint(expr.tok, "IntOrORDINAL", e.E0.Type, "prefix-equality limit argument must be an ORDINAL or integer expression (got {0})");
            AddXConstraint(expr.tok, "Equatable", e.E1.Type, e.E2.Type, "arguments must have the same type (got {0} and {1})");
            AddXConstraint(expr.tok, "IsCoDatatype", e.E1.Type, "arguments to prefix equality must be codatatypes (instead of {0})");
            expr.Type = Type.Bool;
            break;
          default:
            Contract.Assert(false);  // unexpected ternary operator
            break;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, opts);
          }
          scope.PushMarker();
          if (e.LHSs.Count != e.RHSs.Count) {
            reporter.Error(MessageSource.Resolver, expr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, rhsType, opts.codeContext);
            // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
            var c = 0;
            foreach (var v in lhs.Vars) {
              ScopePushAndReport(scope, v, "let-variable");
              c++;
            }
            if (c == 0) {
              // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
              reporter.Error(MessageSource.Resolver, lhs.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
            }
            i++;
          }
        } else {
          // let-such-that expression
          if (e.RHSs.Count != 1) {
            reporter.Error(MessageSource.Resolver, expr, "let-such-that expression must have just one RHS (found {0})", e.RHSs.Count);
          }
          // the bound variables are in scope in the RHS of a let-such-that expression
          scope.PushMarker();
          foreach (var lhs in e.LHSs) {
            Contract.Assert(lhs.Var != null);  // the parser already checked that every LHS is a BoundVar, not a general pattern
            var v = lhs.Var;
            ScopePushAndReport(scope, v, "let-variable");
            ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            AddTypeDependencyEdges(opts.codeContext, v.Type);
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, opts);
            ConstrainTypeExprBool(rhs, "type of RHS of let-such-that expression must be boolean (got {0})");
          }
        }
        ResolveExpression(e.Body, opts);
        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        expr.Type = e.Body.Type;
      } else if (expr is LetOrFailExpr) {
        var e = (LetOrFailExpr)expr;
        ResolveLetOrFailExpr(e, opts);
      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        ResolveExpression(e.Body, opts);
        if (e.Contract != null) ResolveExpression(e.Contract, opts);
        e.Type = e.Body.Type;
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (opts.codeContext is Function) {
          ((Function)opts.codeContext).ContainsQuantifier = true;
        }
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        bool _val = true;
        bool typeQuantifier = Attributes.ContainsBool(e.Attributes, "typeQuantifier", ref _val) && _val;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(e.TypeArgs, true, e);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          var option = typeQuantifier ? new ResolveTypeOption(e) : new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies);
          ResolveType(v.tok, v.Type, opts.codeContext, option, typeQuantifier ? e.TypeArgs : null);
        }
        if (e.TypeArgs.Count > 0 && !typeQuantifier) {
          reporter.Error(MessageSource.Resolver, expr, "a quantifier cannot quantify over types. Possible fix: use the experimental attribute :typeQuantifier");
        }
        if (e.Range != null) {
          ResolveExpression(e.Range, opts);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.Range, "range of quantifier must be of type bool (instead got {0})");
        }
        ResolveExpression(e.Term, opts);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Term, "body of quantifier must be of type bool (instead got {0})");
        // Since the body is more likely to infer the types of the bound variables, resolve it
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        allTypeParameters.PopMarker();
        expr.Type = Type.Bool;

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, opts);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        ResolveExpression(e.Term, opts);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        expr.Type = new SetType(e.Finite, e.Term.Type);

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        Contract.Assert(e.BoundVars.Count == 1 || (1 < e.BoundVars.Count && e.TermLeft != null));
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, opts);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        if (e.TermLeft != null) {
          ResolveExpression(e.TermLeft, opts);
          Contract.Assert(e.TermLeft.Type != null);  // follows from postcondition of ResolveExpression
        }
        ResolveExpression(e.Term, opts);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        expr.Type = new MapType(e.Finite, e.TermLeft != null ? e.TermLeft.Type : e.BoundVars[0].Type, e.Term.Type);

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }

        if (e.Range != null) {
          ResolveExpression(e.Range, opts);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.Range, "Precondition must be boolean (got {0})");
        }

        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, FrameExpressionUse.Reads, opts.codeContext);
        }

        ResolveExpression(e.Term, opts);
        Contract.Assert(e.Term.Type != null);
        scope.PopMarker();
        expr.Type = SelectAppropriateArrowType(e.tok, e.BoundVars.ConvertAll(v => v.Type), e.Body.Type, e.Reads.Count != 0, e.Range != null);
      } else if (expr is WildcardExpr) {
        expr.Type = new SetType(true, builtIns.ObjectQ());
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveStatement(e.S, opts.codeContext);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var r = e.S as UpdateStmt;
          if (r != null && r.ResolvedStatements.Count == 1) {
            var call = r.ResolvedStatements[0] as CallStmt;
            if (call.Method.Mod.Expressions.Count != 0) {
              reporter.Error(MessageSource.Resolver, call, "calls to methods with side-effects are not allowed inside a statement expression");
            } else if (call.Method is TwoStateLemma && !opts.twoState) {
              reporter.Error(MessageSource.Resolver, call, "two-state lemmas can only be used in two-state contexts");
            }
          }
        }
        ResolveExpression(e.E, opts);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        expr.Type = e.E.Type;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        ResolveExpression(e.Test, opts);
        Contract.Assert(e.Test.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Thn, opts);
        Contract.Assert(e.Thn.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Els, opts);
        Contract.Assert(e.Els.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Test, "guard condition in if-then-else expression must be a boolean (instead got {0})");
        expr.Type = new InferredTypeProxy();
        ConstrainSubtypeRelation(expr.Type, e.Thn.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);
        ConstrainSubtypeRelation(expr.Type, e.Els.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);

      } else if (expr is MatchExpr) {
        ResolveMatchExpr((MatchExpr)expr, opts);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (expr.Type == null) {
        // some resolution error occurred
        expr.Type = new InferredTypeProxy();
      }
    }

    private Expression VarDotFunction(IToken tok, string varname, string functionname) {
      return new ApplySuffix(tok, new ExprDotName(tok, new IdentifierExpr(tok, varname), functionname, null), new List<Expression>() { });
    }

    // TODO search for occurrences of "new LetExpr" which could benefit from this helper
    private LetExpr LetPatIn(IToken tok, CasePattern<BoundVar> lhs, Expression rhs, Expression body) {
      return new LetExpr(tok, new List<CasePattern<BoundVar>>() { lhs }, new List<Expression>() { rhs }, body, true);
    }

    private LetExpr LetVarIn(IToken tok, string name, Type tp, Expression rhs, Expression body) {
      var lhs = new CasePattern<BoundVar>(tok, new BoundVar(tok, name, tp));
      return LetPatIn(tok, lhs, rhs, body);
    }

    /// <summary>
    ///  If expr.Lhs != null: Desugars "var x: T :- E; F" into "var temp := E; if temp.IsFailure() then temp.PropagateFailure() else var x: T := temp.Extract(); F"
    ///  If expr.Lhs == null: Desugars "         :- E; F" into "var temp := E; if temp.IsFailure() then temp.PropagateFailure() else                             F"
    /// </summary>
    public void ResolveLetOrFailExpr(LetOrFailExpr expr, ResolveOpts opts) {
      var temp = FreshTempVarName("valueOrError", opts.codeContext);
      var tempType = new InferredTypeProxy();
      // "var temp := E;"
      expr.ResolvedExpression = LetVarIn(expr.tok, temp, tempType, expr.Rhs,
        // "if temp.IsFailure()"
        new ITEExpr(expr.tok, false, VarDotFunction(expr.tok, temp, "IsFailure"),
          // "then temp.PropagateFailure()"
          VarDotFunction(expr.tok, temp, "PropagateFailure"),
          // "else"
          expr.Lhs == null
            // "F"
            ? expr.Body
            // "var x: T := temp.Extract(); F"
            : LetPatIn(expr.tok, expr.Lhs, VarDotFunction(expr.tok, temp, "Extract"), expr.Body)));

      ResolveExpression(expr.ResolvedExpression, opts);
      bool expectExtract = (expr.Lhs != null);
      EnsureSupportsErrorHandling(expr.tok, PartiallyResolveTypeForMemberSelection(expr.tok, tempType), expectExtract);
    }

    private Type SelectAppropriateArrowType(IToken tok, List<Type> typeArgs, Type resultType, bool hasReads, bool hasReq) {
      Contract.Requires(tok != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(resultType != null);
      var arity = typeArgs.Count;
      var typeArgsAndResult = Util.Snoc(typeArgs, resultType);
      if (hasReads) {
        // any arrow
        return new ArrowType(tok, builtIns.ArrowTypeDecls[arity], typeArgsAndResult);
      } else if (hasReq) {
        // partial arrow
        return new UserDefinedType(tok, ArrowType.PartialArrowTypeName(arity), builtIns.PartialArrowTypeDecls[arity], typeArgsAndResult);
      } else {
        // total arrow
        return new UserDefinedType(tok, ArrowType.TotalArrowTypeName(arity), builtIns.TotalArrowTypeDecls[arity], typeArgsAndResult);
      }
    }

    /// <summary>
    /// Adds appropriate type constraints that says "expr" evaluates to an integer (not a bitvector, but possibly an
    /// int-based newtype).  The "errFormat" string can contain a "{0}", referring to the name of the type of "expr".
    /// </summary>
    void ConstrainToIntegerType(Expression expr, string errFormat) {
      Contract.Requires(expr != null);
      Contract.Requires(errFormat != null);
      // We do two constraints: the first can aid in determining types, but allows bit-vectors; the second excludes bit-vectors.
      // However, we reuse the error message, so that only one error gets reported.
      var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, errFormat, expr.Type);
      ConstrainSubtypeRelation(new IntVarietiesSupertype(), expr.Type, err);
      AddXConstraint(expr.tok, "IntegerType", expr.Type, err);
    }

    void AddAssignableConstraint(IToken tok, Type lhs, Type rhs, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsgFormat != null);
      AddXConstraint(tok, "Assignable", lhs, rhs, errMsgFormat);
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type != null);
      Contract.Requires(errMsgFormat != null);
      var types = new Type[] { type };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, new TypeConstraint.ErrorMsgWithToken(tok, errMsgFormat, types)));
    }
    void AddAssignableConstraint(IToken tok, Type lhs, Type rhs, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsg != null);
      AddXConstraint(tok, "Assignable", lhs, rhs, errMsg);
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type != null);
      Contract.Requires(errMsg != null);
      var types = new Type[] { type };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, errMsg));
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type0, Type type1, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type0 != null);
      Contract.Requires(type1 != null);
      Contract.Requires(errMsgFormat != null);
      var types = new Type[] { type0, type1 };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, new TypeConstraint.ErrorMsgWithToken(tok, errMsgFormat, types)));
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type0, Type type1, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type0 != null);
      Contract.Requires(type1 != null);
      Contract.Requires(errMsg != null);
      var types = new Type[] { type0, type1 };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, errMsg));
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type, Expression expr0, Expression expr1, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type != null);
      Contract.Requires(expr0 != null);
      Contract.Requires(expr1 != null);
      Contract.Requires(errMsgFormat != null);
      var types = new Type[] { type };
      var exprs = new Expression[] { expr0, expr1 };
      AllXConstraints.Add(new XConstraintWithExprs(tok, constraintName, types, exprs, new TypeConstraint.ErrorMsgWithToken(tok, errMsgFormat, types)));
    }

    /// <summary>
    /// Attempts to rewrite a datatype update into more primitive operations, after doing the appropriate resolution checks.
    /// Upon success, returns that rewritten expression and sets "legalSourceConstructors".
    /// Upon some resolution error, return null.
    /// </summary>
    Expression ResolveDatatypeUpdate(IToken tok, Expression root, DatatypeDecl dt, List<Tuple<IToken, string, Expression>> memberUpdates, ResolveOpts opts, out List<DatatypeCtor> legalSourceConstructors) {
      Contract.Requires(tok != null);
      Contract.Requires(root != null);
      Contract.Requires(dt != null);
      Contract.Requires(memberUpdates != null);
      Contract.Requires(opts != null);

      legalSourceConstructors = null;

      // First, compute the list of candidate result constructors, that is, the constructors
      // that have all of the mentioned destructors. Issue errors for duplicated names and for
      // names that are not destructors in the datatype.
      var candidateResultCtors = dt.Ctors;  // list of constructors that have all the so-far-mentioned destructors
      var memberNames = new HashSet<string>();
      var rhsBindings = new Dictionary<string, Tuple<BoundVar/*let variable*/, IdentifierExpr/*id expr for let variable*/, Expression /*RHS in given syntax*/>>();
      var subst = TypeSubstitutionMap(dt.TypeArgs, root.Type.NormalizeExpand().TypeArgs);
      foreach (var entry in memberUpdates) {
        var destructor_str = entry.Item2;
        if (memberNames.Contains(destructor_str)) {
          reporter.Error(MessageSource.Resolver, entry.Item1, "duplicate update member '{0}'", destructor_str);
        } else {
          memberNames.Add(destructor_str);
          MemberDecl member;
          if (!classMembers[dt].TryGetValue(destructor_str, out member)) {
            reporter.Error(MessageSource.Resolver, entry.Item1, "member '{0}' does not exist in datatype '{1}'", destructor_str, dt.Name);
          } else if (!(member is DatatypeDestructor)) {
            reporter.Error(MessageSource.Resolver, entry.Item1, "member '{0}' is not a destructor in datatype '{1}'", destructor_str, dt.Name);
          } else {
            var destructor = (DatatypeDestructor)member;
            var intersection = new List<DatatypeCtor>(candidateResultCtors.Intersect(destructor.EnclosingCtors));
            if (intersection.Count == 0) {
              reporter.Error(MessageSource.Resolver, entry.Item1,
                "updated datatype members must belong to the same constructor (unlike the previously mentioned destructors, '{0}' does not belong to {1})",
                destructor_str, DatatypeDestructor.PrintableCtorNameList(candidateResultCtors, "or"));
            } else {
              candidateResultCtors = intersection;
              if (destructor.IsGhost) {
                rhsBindings.Add(destructor_str, new Tuple<BoundVar, IdentifierExpr, Expression>(null, null, entry.Item3));
              } else {
                var xName = FreshTempVarName(string.Format("dt_update#{0}#", destructor_str), opts.codeContext);
                var xVar = new BoundVar(new AutoGeneratedToken(tok), xName, SubstType(destructor.Type, subst));
                var x = new IdentifierExpr(new AutoGeneratedToken(tok), xVar);
                rhsBindings.Add(destructor_str, new Tuple<BoundVar, IdentifierExpr, Expression>(xVar, x, entry.Item3));
              }
            }
          }
        }
      }
      if (candidateResultCtors.Count == 0) {
        return null;
      }

      // Check that every candidate result constructor has given a name to all of its parameters.
      var hasError = false;
      foreach (var ctor in candidateResultCtors) {
        if (ctor.Formals.Exists(f => !f.HasName)) {
          reporter.Error(MessageSource.Resolver, tok,
            "candidate result constructor '{0}' has an anonymous parameter (to use in datatype update expression, name all the parameters of the candidate result constructors)",
            ctor.Name);
          hasError = true;
        }
      }
      if (hasError) {
        return null;
      }

      // The legal source constructors are the candidate result constructors. (Yep, two names for the same thing.)
      legalSourceConstructors = candidateResultCtors;
      Contract.Assert(1 <= legalSourceConstructors.Count);

      // Rewrite the datatype update root.(x := X, y := Y, ...) to:
      //     var d := root;
      //     var x := X;  // EXCEPT: don't do this for ghost fields
      //     var y := Y;
      //     ..
      //     if d.CandidateResultConstructor0 then
      //       CandidateResultConstructor0(x, y, ..., d.f0, d.f1, ...)  // for a ghost field x, use the expression X directly
      //     else if d.CandidateResultConstructor1 then
      //       CandidateResultConstructor0(x, y, ..., d.g0, d.g1, ...)
      //     ...
      //     else
      //       CandidateResultConstructorN(x, y, ..., d.k0, d.k1, ...)
      //
      Expression rewrite = null;
      // Create a unique name for d', the variable we introduce in the let expression
      var dName = FreshTempVarName("dt_update_tmp#", opts.codeContext);
      var dVar = new BoundVar(new AutoGeneratedToken(tok), dName, root.Type);
      var d = new IdentifierExpr(new AutoGeneratedToken(tok), dVar);
      Expression body = null;
      candidateResultCtors.Reverse();
      foreach (var crc in candidateResultCtors) {
        // Build the arguments to the datatype constructor, using the updated value in the appropriate slot
        var ctor_args = new List<Expression>();
        foreach (var f in crc.Formals) {
          Tuple<BoundVar/*let variable*/, IdentifierExpr/*id expr for let variable*/, Expression /*RHS in given syntax*/> info;
          if (rhsBindings.TryGetValue(f.Name, out info)) {
            ctor_args.Add(info.Item2 ?? info.Item3);
          } else {
            ctor_args.Add(new ExprDotName(tok, d, f.Name, null));
          }
        }
        var ctor_call = new DatatypeValue(tok, crc.EnclosingDatatype.Name, crc.Name, ctor_args);
        ResolveDatatypeValue(opts, ctor_call, dt, root.Type.NormalizeExpand());  // resolve to root.Type, so that type parameters get filled in appropriately
        if (body == null) {
          body = ctor_call;
        } else {
          // body = if d.crc? then ctor_call else body
          var guard = new ExprDotName(tok, d, crc.QueryField.Name, null);
          body = new ITEExpr(tok, false, guard, ctor_call, body);
        }
      }
      Contract.Assert(body != null);  // because there was at least one element in candidateResultCtors

      // Wrap the let's around body
      rewrite = body;
      foreach (var entry in rhsBindings) {
        if (entry.Value.Item1 != null) {
          var lhs = new CasePattern<BoundVar>(tok, entry.Value.Item1);
          rewrite = new LetExpr(tok, new List<CasePattern<BoundVar>>() { lhs }, new List<Expression>() { entry.Value.Item3 }, rewrite, true);
        }
      }
      var dVarPat = new CasePattern<BoundVar>(tok, dVar);
      rewrite = new LetExpr(tok, new List<CasePattern<BoundVar>>() { dVarPat }, new List<Expression>() { root }, rewrite, true);
      Contract.Assert(rewrite != null);
      ResolveExpression(rewrite, opts);
      return rewrite;
    }

    void ResolveMatchExpr(MatchExpr me, ResolveOpts opts) {
      Contract.Requires(me != null);
      Contract.Requires(opts != null);
      Contract.Requires(me.OrigUnresolved == null);

      // first, clone the original expression
      me.OrigUnresolved = (MatchExpr)new Cloner().CloneExpr(me);
      ResolveExpression(me.Source, opts);
      Contract.Assert(me.Source.Type != null);  // follows from postcondition of ResolveExpression
      var errorCount = reporter.Count(ErrorLevel.Error);
      if (me.Source is DatatypeValue) {
        var e = (DatatypeValue)me.Source;
        if (e.Arguments.Count < 1) {
          reporter.Error(MessageSource.Resolver, me.tok, "match source tuple needs at least 1 argument");
        }
        foreach (var arg in e.Arguments) {
          if (arg is DatatypeValue && ((DatatypeValue)arg).Arguments.Count < 1) {
            reporter.Error(MessageSource.Resolver, me.tok, "match source tuple needs at least 1 argument");
          }
        }
      }
      if (reporter.Count(ErrorLevel.Error) != errorCount) {
        return;
      }
      var sourceType = PartiallyResolveTypeForMemberSelection(me.Source.tok, me.Source.Type).NormalizeExpand();
      var dtd = sourceType.AsDatatype;
      var subst = new Dictionary<TypeParameter, Type>();
      Dictionary<string, DatatypeCtor> ctors;
      if (dtd == null) {
        reporter.Error(MessageSource.Resolver, me.Source, "the type of the match source expression must be a datatype (instead found {0})", me.Source.Type);
        ctors = null;
      } else {
        Contract.Assert(sourceType != null);  // dtd and sourceType are set together above
        ctors = datatypeCtors[dtd];
        Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage

        // build the type-parameter substitution map for this use of the datatype
        subst = TypeSubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs);
      }

      // convert CasePattern in MatchCaseExpr to BoundVar and flatten the MatchCaseExpr.
      List<Tuple<CasePattern<BoundVar>, BoundVar>> patternSubst = new List<Tuple<CasePattern<BoundVar>, BoundVar>>();
      if (dtd != null) {
        DesugarMatchCaseExpr(me, dtd, patternSubst, opts.codeContext);
      }

      ISet<string> memberNamesUsed = new HashSet<string>();
      me.Type = new InferredTypeProxy();
      foreach (MatchCaseExpr mc in me.Cases) {
        DatatypeCtor ctor = null;
        if (ctors != null) {
          Contract.Assert(dtd != null);
          var ctorId = mc.Id;
          if (me.Source.Type.AsDatatype is TupleTypeDecl) {
            var tuple = (TupleTypeDecl)me.Source.Type.AsDatatype;
            var dims = tuple.Dims;
            ctorId = BuiltIns.TupleTypeCtorNamePrefix + dims;
          }
          if (!ctors.TryGetValue(ctorId, out ctor)) {
            reporter.Error(MessageSource.Resolver, mc.tok, "member {0} does not exist in datatype {1}", ctorId, dtd.Name);
          } else {
            Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
            mc.Ctor = ctor;
            if (ctor.Formals.Count != mc.Arguments.Count) {
              if (me.Source.Type.AsDatatype is TupleTypeDecl) {
                reporter.Error(MessageSource.Resolver, mc.tok, "case arguments count does not match source arguments count");
              } else {
                reporter.Error(MessageSource.Resolver, mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", ctorId, mc.Arguments.Count, ctor.Formals.Count);
              }
            }
            if (memberNamesUsed.Contains(ctorId)) {
              reporter.Error(MessageSource.Resolver, mc.tok, "member {0} appears in more than one case", mc.Id);
            } else {
              memberNamesUsed.Add(ctorId);  // add mc.Id to the set of names used
            }
          }
        }
        scope.PushMarker();
        int i = 0;
        if (mc.Arguments != null) {
          foreach (BoundVar v in mc.Arguments) {
            scope.Push(v.Name, v);
            ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            if (ctor != null && i < ctor.Formals.Count) {
              Formal formal = ctor.Formals[i];
              Type st = SubstType(formal.Type, subst);
              ConstrainSubtypeRelation(v.Type, st, me,
                "the declared type of the formal ({0}) does not agree with the corresponding type in the constructor's signature ({1})", v.Type, st);
              v.IsGhost = formal.IsGhost;

              // update the type of the boundvars in the MatchCaseToken
              if (v.tok is MatchCaseToken) {
                MatchCaseToken mt = (MatchCaseToken)v.tok;
                foreach (Tuple<IToken, BoundVar, bool> entry in mt.varList) {
                  ConstrainSubtypeRelation(entry.Item2.Type, v.Type, entry.Item1, "incorrect type for bound match-case variable (expected {0}, got {1})", v.Type, entry.Item2.Type);
                }
              }
            }
            i++;
          }
        }
        ResolveExpression(mc.Body, opts);
        // substitute body to replace the case pat with v. This needs to happen
        // after the body is resolved so we can scope the bv correctly.
        if (patternSubst.Count > 0) {
          var cloner = new MatchCaseExprSubstituteCloner(patternSubst);
          mc.UpdateBody(cloner.CloneExpr(mc.Body));
          // resolve it again since we just cloned it.
          ResolveExpression(mc.Body, opts);
        }

        Contract.Assert(mc.Body.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainSubtypeRelation(me.Type, mc.Body.Type, mc.Body.tok, "type of case bodies do not agree (found {0}, previous types {1})", mc.Body.Type, me.Type);
        scope.PopMarker();
      }
      if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
        // We could complain about the syntactic omission of constructors:
        //   reporter.Error(MessageSource.Resolver, expr, "match expression does not cover all constructors");
        // but instead we let the verifier do a semantic check.
        // So, for now, record the missing constructors:
        foreach (var ctr in dtd.Ctors) {
          if (!memberNamesUsed.Contains(ctr.Name)) {
            me.MissingCases.Add(ctr);
          }
        }
        Contract.Assert(memberNamesUsed.Count + me.MissingCases.Count == dtd.Ctors.Count);
      }
    }

    /*
     * Convert
     *   match xs
     *     case Cons(y, Cons(z, zs)) => last(Cons(z, zs))
     *     case Cons(y, Nil) => y
     * To
     *   match xs
     *     case Cons(y, ys) => match ys
     *       case Nil => y
     *       case Cons(z, zs) => last(ys)
     * */
    void DesugarMatchCaseExpr(MatchExpr me, DatatypeDecl dtd, List<Tuple<CasePattern<BoundVar>, BoundVar>> patterns, ICodeContext codeContext) {
      Contract.Assert(dtd != null);
      Dictionary<string, DatatypeCtor> ctors = datatypeCtors[dtd];
      if (ctors == null) {
        // no constructors, there is no need to desugar
        return;
      }
      // Each tuple element gets mapped to its constructor's dictionary.
      // Type variables get an empty dictionary.
      var tupleCtorsList = new List<Dictionary<string, DatatypeCtor>>();
      if (me.Source.Type.AsDatatype is TupleTypeDecl) {
        var udt = me.Source.Type.NormalizeExpand() as UserDefinedType;
        foreach (Type typeArg in udt.TypeArgs) {
          var t = PartiallyResolveTypeForMemberSelection(me.tok, typeArg).NormalizeExpand() as UserDefinedType;
          if (t != null) {
            var cls = t.ResolvedClass as DatatypeDecl;
            if (cls != null) {
              tupleCtorsList.Add(datatypeCtors[cls]);
            } else {
              tupleCtorsList.Add(new Dictionary<string, DatatypeCtor>());
            }
          } else {
            tupleCtorsList.Add(new Dictionary<string, DatatypeCtor>());
          }
        }
      }

      bool keepOrigToken = true;
      foreach (MatchCaseExpr mc in me.Cases) {
        if (mc.Arguments != null) {
          // already desugared. This happens during the second pass resolver after cloning.
          Contract.Assert(mc.CasePatterns == null);
          return;
        }

        Contract.Assert(mc.Arguments == null);
        Contract.Assert(mc.CasePatterns != null);
        Contract.Assert(ctors != null);
        DatatypeCtor ctor = null;
        if (ctors.TryGetValue(mc.Id, out ctor) || (me.Source.Type.AsDatatype is TupleTypeDecl)) {
          scope.PushMarker();
          if (me.Source.Type.AsDatatype is TupleTypeDecl) {
            int i = 0;
            foreach (var pat in mc.CasePatterns) {
              FindDuplicateIdentifier(pat, tupleCtorsList[i++], true);
            }
          } else {
            foreach (var pat in mc.CasePatterns) {
              FindDuplicateIdentifier(pat, ctors, true);
            }
          }
          List<BoundVar> arguments = new List<BoundVar>();
          Expression body = mc.Body;
          for (int i = mc.CasePatterns.Count-1; i>=0; i--) {
            string name = "_ms#" + i;
            Type type = new InferredTypeProxy();
            BoundVar sourceVar = new BoundVar(new MatchCaseToken(me.tok), name, type);
            var pat = mc.CasePatterns[i];
            if (pat.Var != null) {
              BoundVar v = pat.Var;
              arguments.Insert(0, v);
            } else {
              body = DesugarMatchCasePattern(mc, pat, sourceVar, body, keepOrigToken);
              patterns.Add(new Tuple<CasePattern<BoundVar>, BoundVar>(pat, sourceVar));
              arguments.Insert(0, sourceVar);
            }
          }
          keepOrigToken = false;
          mc.UpdateBody(body);
          mc.Arguments = arguments;
          mc.CasePatterns = null;
          scope.PopMarker();
        } else if (mc.CasePatterns != null) {
          reporter.Error(MessageSource.Resolver, mc.tok, "Type mismatch: expected constructor of type {0}.  Got {1}.", dtd.Name, mc.Id);
          return;
        }
      }


      List<MatchCaseExpr> newCases = new List<MatchCaseExpr>();

      // need to consolidate the cases.
      // Convert
      //  match xs
      //    case Cons(y, #mc#0) => match #mc#0
      //                case Cons((z, zs) => body
      //    case Cons(y, #mc#0) => match #mc#0
      //                case Nil => y
      // into
      //  match xs
      //    case Cons(y, #mc#0) => match #mc#0
      //                case Cons((z, zs) => body
      //                case Nil => y
      bool thingsChanged = false;
      Dictionary<string, MatchCaseExpr> caseMap = new Dictionary<string, MatchCaseExpr>();
      List<MatchCaseExpr> mcWithWildCard = new List<MatchCaseExpr>();
      foreach (MatchCaseExpr mc in me.Cases) {
        // check each CasePattern to see if it has wildcard.
        if (CaseExprHasWildCard(mc)) {
          mcWithWildCard.Add(mc);
        } else {
          thingsChanged |= CombineMatchCaseExpr(mc, newCases, caseMap, codeContext);
        }
      }

      foreach (MatchCaseExpr mc in mcWithWildCard) {
        // now process with cases with wildcard
        thingsChanged |= CombineMatchCaseExpr(mc, newCases, caseMap, codeContext);
      }

      if (thingsChanged) {
        me.UpdateCases(newCases);
      }
    }

    Expression DesugarMatchCasePattern(MatchCaseExpr mc, CasePattern<BoundVar> pat, BoundVar v, Expression body, bool keepToken) {
      // convert
      //    case Cons(y, Cons(z, zs)) => body
      // to
      //    case Cons(y, #mc#) => match #mc#
      //            case Cons(z, zs) => body

      Expression source = new NameSegment(new AutoGeneratedToken(pat.tok), v.Name, null);
      List<MatchCaseExpr> cases = new List<MatchCaseExpr>();
      cases.Add(new MatchCaseExpr(pat.tok, pat.Id, pat.Arguments == null ? new List<CasePattern<BoundVar>>() : pat.Arguments, body));
      if (!keepToken) {
        AutoGeneratedTokenCloner cloner = new AutoGeneratedTokenCloner();
        source = cloner.CloneExpr(source);
      }
      return new MatchExpr(pat.tok, source, cases, false);
    }


    bool CaseExprHasWildCard(MatchCase mc) {
      if (mc.Arguments != null) {
        foreach (BoundVar bv in mc.Arguments) {
          if (LocalVariable.HasWildcardName(bv)) {
            return true;
          }
        }
      }
      return false;
    }

    bool CombineMatchCaseExpr(MatchCaseExpr mc, List<MatchCaseExpr> newCases, Dictionary<string, MatchCaseExpr> caseMap, ICodeContext codeContext) {
      bool thingsChanged = false;
      MatchCaseExpr old_mc;
      if (caseMap.TryGetValue(mc.Id, out old_mc)) {
        // already has a case with the same ctor, try to consolidate the body.
        if (SameMatchCaseExpr(old_mc, mc, codeContext)) {
          MatchExpr old = (MatchExpr)old_mc.Body;
          MatchExpr current = (MatchExpr)mc.Body;
          foreach (MatchCaseExpr c in current.Cases) {
            old.Cases.Add(c);
          }
          // add the token from mc to old_mc so the identifiers will show correctly in the IDE
          List<BoundVar> arguments = new List<BoundVar>();
          Contract.Assert(old_mc.Arguments.Count == mc.Arguments.Count);
          for (int i = 0; i < old_mc.Arguments.Count; i++) {
            var bv = old_mc.Arguments[i];
            MatchCaseToken mcToken;
            if (!(bv.tok is MatchCaseToken)) {
              // create a MatchCaseToken
              mcToken = new MatchCaseToken(bv.tok);
              // clone the bv but with the MatchCaseToken
              var bvNew = new BoundVar(mcToken, bv.Name, bv.Type);
              bvNew.IsGhost = bv.IsGhost;
              arguments.Add(bvNew);
            } else {
              mcToken = (MatchCaseToken)bv.tok;
              arguments.Add(bv);
            }
            mcToken.AddVar(bv.tok, bv, true);
            mcToken.AddVar(mc.Arguments[i].tok, mc.Arguments[i], true);
          }
          old_mc.Arguments = arguments;
          thingsChanged = true;
        } else {
          // duplicate cases, do nothing for now. The error will be reported during resolving
        }
      } else {
        // it is a new case.
        newCases.Add(mc);
        caseMap.Add(mc.Id, mc);
      }
      return thingsChanged;
    }


    bool SameMatchCaseExpr(MatchCaseExpr one, MatchCaseExpr other, ICodeContext codeContext) {
      // this method is called after all the CasePattern in the match cases are converted
      // into BoundVars.
      Contract.Assert(one.CasePatterns == null && one.Arguments != null);
      Contract.Assert(other.CasePatterns == null && other.Arguments != null);
      // In order to combine the two match cases, the bodies need to be a MatchExpr and
      // the arguments and the source of the body are the same.
      // We do string equals since they should be in the same scope.
      if (one.Arguments.Count != other.Arguments.Count) {
        return false;
      }
      if (!(one.Body is MatchExpr) || !(other.Body is MatchExpr)) {
        return false;
      }
      var source1 = ((MatchExpr)one.Body).Source;
      var source2 = ((MatchExpr)other.Body).Source;
      if (!(source1 is NameSegment) || !(source2 is NameSegment)) {
        return false;
      }
      if (!((NameSegment)source1).Name.Equals(((NameSegment)source2).Name)) {
        return false;
      }
      for (int i = 0; i < one.Arguments.Count; i++) {
        BoundVar bv1 = one.Arguments[i];
        BoundVar bv2 = other.Arguments[i];
        if (!LocalVariable.HasWildcardName(bv1) && !LocalVariable.HasWildcardName(bv2)) {
          if (!bv1.Name.Equals(bv2.Name)) {
            // need to substitute bv2 with bv1 in the matchstmt body
            // what if match body already has the bv?? need to make a new bv
            Type type = new InferredTypeProxy();
            string name = FreshTempVarName("_mc#", codeContext);
            MatchCaseToken mcToken = new MatchCaseToken(one.tok);
            BoundVar bv = new BoundVar(mcToken, name, type);
            mcToken.AddVar(bv1.tok, bv1, true);
            mcToken.AddVar(bv2.tok, bv2, true);
            // substitute the appeareance of old bv with the new bv in the match case
            SubstituteMatchCaseBoundVar(one, bv1, bv);
            SubstituteMatchCaseBoundVar(other, bv2, bv);
          }
        }
      }
      return true;
    }

    void SubstituteMatchCaseBoundVar(MatchCaseExpr mc, BoundVar oldBv, BoundVar newBv) {
      List<BoundVar> arguments = new List<BoundVar>();
      for (int i = 0; i < mc.Arguments.Count; i++) {
        BoundVar bv = mc.Arguments[i];
        if (bv == oldBv) {
          arguments.Add(newBv);
        } else {
          arguments.Add(bv);
        }
      }
      mc.Arguments = arguments;

      // substitue the oldBv with newBv in the body
      MatchCaseExprSubstituteCloner cloner = new MatchCaseExprSubstituteCloner(oldBv, newBv);
      Expression clone = cloner.CloneExpr(mc.Body);
      mc.UpdateBody(clone);
    }

    void ResolveCasePattern<VT>(CasePattern<VT> pat, Type sourceType, ICodeContext context) where VT: IVariable {
      Contract.Requires(pat != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(context != null);

      DatatypeDecl dtd = null;
      UserDefinedType udt = null;
      if (sourceType.IsDatatype) {
        udt = (UserDefinedType)sourceType.NormalizeExpand();
        dtd = (DatatypeDecl)udt.ResolvedClass;
      }
      // Find the constructor in the given datatype
      // If what was parsed was just an identifier, we will interpret it as a datatype constructor, if possible
      DatatypeCtor ctor = null;
      if (dtd != null) {
        if (pat.Var == null || (pat.Var != null && pat.Var.Type is TypeProxy)) {
          if (datatypeCtors[dtd].TryGetValue(pat.Id, out ctor)) {
            pat.Ctor = ctor;
            pat.Var = default(VT);
          }
        }
      }

      if (pat.Var != null) {
        // this is a simple resolution
        var v = pat.Var;
        ResolveType(v.Tok, v.Type, context, ResolveTypeOptionEnum.InferTypeProxies, null);
        AddTypeDependencyEdges(context, v.Type);
        // Note, the following type constraint checks that the RHS type can be assigned to the new variable on the left. In particular, it
        // does not check that the entire RHS can be assigned to something of the type of the pattern on the left.  For example, consider
        // a type declared as "datatype Atom<T> = MakeAtom(T)", where T is an invariant type argument.  Suppose the RHS has type Atom<nat>
        // and that the LHS is the pattern MakeAtom(x: int).  This is okay, despite the fact that Atom<nat> is not assignable to Atom<int>.
        // The reason is that the purpose of the pattern on the left is really just to provide a skeleton to introduce bound variables in.
        AddAssignableConstraint(v.Tok, v.Type, sourceType, "type of corresponding source/RHS ({1}) does not match type of bound variable ({0})");
        pat.AssembleExpr(null);
        return;
      }
      if (dtd == null) {
        // look up the name of the pattern's constructor
        Tuple<DatatypeCtor, bool> pair;
        if (moduleInfo.Ctors.TryGetValue(pat.Id, out pair) && !pair.Item2) {
          ctor = pair.Item1;
          pat.Ctor = ctor;
          dtd = ctor.EnclosingDatatype;
          var typeArgs = new List<Type>();
          foreach (var xt in dtd.TypeArgs) {
            typeArgs.Add(new InferredTypeProxy());
          }
          udt = new UserDefinedType(pat.tok, dtd.Name, dtd, typeArgs);
          ConstrainSubtypeRelation(udt, sourceType, pat.tok, "type of RHS ({0}) does not match type of bound variable '{1}'", sourceType, pat.Id);
        }
      }
      if (dtd == null && ctor == null) {
        reporter.Error(MessageSource.Resolver, pat.tok, "to use a pattern, the type of the source/RHS expression must be a datatype (instead found {0})", sourceType);
      } else if (ctor == null) {
        reporter.Error(MessageSource.Resolver, pat.tok, "constructor {0} does not exist in datatype {1}", pat.Id, dtd.Name);
      } else {
        var argCount = pat.Arguments == null ? 0 : pat.Arguments.Count;
        if (ctor.Formals.Count != argCount) {
          reporter.Error(MessageSource.Resolver, pat.tok, "pattern for constructor {0} has wrong number of formals (found {1}, expected {2})", pat.Id, argCount, ctor.Formals.Count);
        }
        // build the type-parameter substitution map for this use of the datatype
        Contract.Assert(dtd.TypeArgs.Count == udt.TypeArgs.Count);  // follows from the type previously having been successfully resolved
        var subst = TypeSubstitutionMap(dtd.TypeArgs, udt.TypeArgs);
        // recursively call ResolveCasePattern on each of the arguments
        var j = 0;
        if (pat.Arguments != null) {
          foreach (var arg in pat.Arguments) {
            if (j < ctor.Formals.Count) {
              var formal = ctor.Formals[j];
              Type st = SubstType(formal.Type, subst);
              ResolveCasePattern(arg, st, context);
            }
            j++;
          }
        }
        if (j == ctor.Formals.Count) {
          pat.AssembleExpr(udt.TypeArgs);
        }
      }
    }

    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Local variable, parameter, or bound variable.
    ///     (Language design note:  If this clashes with something of interest, one can always rename the local variable locally.)
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. If isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module (if two constructors have the same name, an error message is produced here)
    ///     (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor name with the name of the datatype)
    ///  3. Member of the enclosing module (type name or the name of a module)
    ///  4. Static function or method in the enclosing module or its imports
    ///
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the NameSegment is not directly enclosed in another NameSegment or ExprDotName expression.</param>
    /// <param name="args">If the NameSegment is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="opts"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a MemberSelectExpr whose .Member is a Method.</param>
    Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<Expression> args, ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      // For 0:
      IVariable v;
      // For 1:
      Dictionary<string, MemberDecl> members;
      // For 1 and 4:
      MemberDecl member = null;
      // For 2:
      Tuple<DatatypeCtor, bool> pair;
      // For 3:
      TopLevelDecl decl;

      var name = opts.isReveal ? "reveal_" + expr.Name : expr.Name;
      v = scope.Find(name);
      if (v != null) {
        // ----- 0. local variable, parameter, or bound variable
        if (expr.OptTypeArguments != null) {
          reporter.Error(MessageSource.Resolver, expr.tok, "variable '{0}' does not take any type parameters", name);
        }
        r = new IdentifierExpr(expr.tok, v);
      } else if (currentClass is TopLevelDeclWithMembers cl && classMembers.TryGetValue(cl, out members) && members.TryGetValue(name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, (TopLevelDeclWithMembers)member.EnclosingClass, true);
        } else {
          if (!scope.AllowInstance) {
            reporter.Error(MessageSource.Resolver, expr.tok, "'this' is not allowed in a 'static' context"); //TODO: Rephrase this
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = GetThisType(expr.tok, (TopLevelDeclWithMembers)member.EnclosingClass);  // resolve here
        }
        r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, opts, allowMethodCall);
      } else if (isLastNameSegment && moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 2. datatype constructor
        if (pair.Item2) {
          // there is more than one constructor with this name
          reporter.Error(MessageSource.Resolver, expr.tok, "the name '{0}' denotes a datatype constructor, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", expr.Name, pair.Item1.EnclosingDatatype.Name);
        } else {
          if (expr.OptTypeArguments != null) {
            reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
          }
          var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, name, args ?? new List<Expression>());
          ResolveDatatypeValue(opts, rr, pair.Item1.EnclosingDatatype, null);
          if (args == null) {
            r = rr;
          } else {
            r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
            rWithArgs = rr;
          }
        }
      } else if (moduleInfo.TopLevels.TryGetValue(name, out decl)) {
        // ----- 3. Member of the enclosing module
        if (decl is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)decl;
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.Name, ad.ModuleNames());
        } else {
          // We have found a module name or a type name, neither of which is an expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          if (!isLastNameSegment) {
            if (decl is ClassDecl && ((ClassDecl)decl).NonNullTypeDecl != null) {
              // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
              // the name of the class, C. Report an error and continue.
              reporter.Error(MessageSource.Resolver, expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
            } else {
              decl = decl.ViewAsClass;
            }
          }
          r = CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
        }

      } else if (moduleInfo.StaticMembers.TryGetValue(name, out member)) {
        // ----- 4. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (member is AmbiguousMemberDecl) {
          var ambiguousMember = (AmbiguousMemberDecl)member;
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ambiguousMember.ModuleNames());
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass, true);
          r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, opts, allowMethodCall);
        }

      } else {
        // ----- None of the above
        reporter.Error(MessageSource.Resolver, expr.tok, "unresolved identifier: {0}", name);
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return rWithArgs;
    }

    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Type parameter
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. Member of the enclosing module (type name or the name of a module)
    ///  3. Static function or method in the enclosing module or its imports
    ///
    /// Note: 1 and 3 are not used now, but they will be of interest when async task types are supported.
    /// </summary>
    void ResolveNameSegment_Type(NameSegment expr, ResolveOpts opts, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(opts != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, option, defaultTypeArguments);
        }
      }

      Expression r = null;  // the resolved expression, if successful

      // For 0:
      TypeParameter tp;
#if ASYNC_TASK_TYPES
      // For 1:
      Dictionary<string, MemberDecl> members;
      // For 1 and 3:
      MemberDecl member = null;
#endif
      // For 2:
      TopLevelDecl decl;

      tp = allTypeParameters.Find(expr.Name);
      if (tp != null) {
        // ----- 0. type parameter
        if (expr.OptTypeArguments == null) {
          r = new Resolver_IdentifierExpr(expr.tok, tp);
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "Type parameter expects no type arguments: {0}", expr.Name);
        }
#if ASYNC_TASK_TYPES  // At the moment, there is no way for a class member to part of a type name, but this changes with async task types
      } else if (currentClass != null && classMembers.TryGetValue(currentClass, out members) && members.TryGetValue(expr.Name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
        } else {
          if (!scope.AllowInstance) {
            reporter.Error(MessageSource.Resolver, expr.tok, "'this' is not allowed in a 'static' context");
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = GetThisType(expr.tok, (ClassDecl)member.EnclosingClass);  // resolve here
        }
        r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
#endif
      } else if (moduleInfo.TopLevels.TryGetValue(expr.Name, out decl)) {
        // ----- 2. Member of the enclosing module
        if (decl is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)decl;
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.Name, ad.ModuleNames());
        } else {
          // We have found a module name or a type name, neither of which is a type expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into a type expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          r = CreateResolver_IdentifierExpr(expr.tok, expr.Name, expr.OptTypeArguments, decl);
        }

#if ASYNC_TASK_TYPES  // At the moment, there is no way for a class member to part of a type name, but this changes with async task types
      } else if (moduleInfo.StaticMembers.TryGetValue(expr.Name, out member)) {
        // ----- 3. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (ReallyAmbiguousThing(ref member)) {
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ((AmbiguousMemberDecl)member).ModuleNames());
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
          r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
        }
#endif
      } else {
        // ----- None of the above
        reporter.Error(MessageSource.Resolver, expr.tok, "Undeclared top-level type or type parameter: {0} (did you forget to qualify a name or declare a module import 'opened?')", expr.Name);
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
    }

    Resolver_IdentifierExpr CreateResolver_IdentifierExpr(IToken tok, string name, List<Type> optTypeArguments, TopLevelDecl decl) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<Resolver_IdentifierExpr>() != null);

      if (!moduleInfo.IsAbstract) {
        var md = decl as ModuleDecl;
        if (md != null && md.Signature.IsAbstract) {
          reporter.Error(MessageSource.Resolver, tok, "a compiled module is not allowed to use an abstract module ({0})", decl.Name);
        }
      }
      var n = optTypeArguments == null ? 0 : optTypeArguments.Count;
      if (optTypeArguments != null) {
        // type arguments were supplied; they must be equal in number to those expected
        if (n != decl.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "Wrong number of type arguments ({0} instead of {1}) passed to {2}: {3}", n, decl.TypeArgs.Count, decl.WhatKind, name);
        }
      }
      List<Type> tpArgs = new List<Type>();
      for (int i = 0; i < decl.TypeArgs.Count; i++) {
        tpArgs.Add(i < n ? optTypeArguments[i] : new InferredTypeProxy());
      }
      return new Resolver_IdentifierExpr(tok, decl, tpArgs);
    }

    /// <summary>
    /// To resolve "id" in expression "E . id", do:
    ///  * If E denotes a module name M:
    ///      0. If isLastNameSegment:
    ///         Unambiguous constructor name of a datatype in module M (if two constructors have the same name, an error message is produced here)
    ///         (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor name with the name of the datatype)
    ///      1. Member of module M:  sub-module (including submodules of imports), class, datatype, etc.
    ///         (if two imported types have the same name, an error message is produced here)
    ///      2. Static function or method of M._default
    ///    (Note that in contrast to ResolveNameSegment, imported modules, etc. are ignored)
    ///  * If E denotes a type:
    ///      3. Look up id as a member of that type
    ///  * If E denotes an expression:
    ///      4. Let T be the type of E.  Look up id in T.
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the ExprDotName is not directly enclosed in another ExprDotName expression.</param>
    /// <param name="args">If the ExprDotName is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="opts"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a Resolver_MethodCall.</param>
    Expression ResolveDotSuffix(ExprDotName expr, bool isLastNameSegment, List<Expression> args, ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      // resolve the LHS expression
      // LHS should not be reveal lemma
      ResolveOpts nonRevealOpts = new ResolveOpts(opts.codeContext, opts.twoState, false, opts.isPostCondition, opts.InsideOld);
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment((NameSegment)expr.Lhs, false, null, nonRevealOpts, false);
      } else if (expr.Lhs is ExprDotName) {
        ResolveDotSuffix((ExprDotName)expr.Lhs, false, null, nonRevealOpts, false);
      } else {
        ResolveExpression(expr.Lhs, nonRevealOpts);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"
      MemberDecl member = null;

      var name = opts.isReveal ? "reveal_" + expr.SuffixName : expr.SuffixName;
      var lhs = expr.Lhs.Resolved;
      if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
        var ri = (Resolver_IdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).AccessibleSignature(useCompileSignatures);
        sig = GetSignature(sig);
        // For 0:
        Tuple<DatatypeCtor, bool> pair;
        // For 1:
        TopLevelDecl decl;

        if (isLastNameSegment && sig.Ctors.TryGetValue(name, out pair)) {
          // ----- 0. datatype constructor
          if (pair.Item2) {
            // there is more than one constructor with this name
            reporter.Error(MessageSource.Resolver, expr.tok, "the name '{0}' denotes a datatype constructor in module {2}, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", name, pair.Item1.EnclosingDatatype.Name, ((ModuleDecl)ri.Decl).Name);
          } else {
            if (expr.OptTypeArguments != null) {
              reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
            }
            var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, name, args ?? new List<Expression>());
            ResolveDatatypeValue(opts, rr, pair.Item1.EnclosingDatatype, null);

            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        } else if (sig.TopLevels.TryGetValue(name, out decl)) {
          // ----- 1. Member of the specified module
          if (decl is AmbiguousTopLevelDecl) {
            var ad = (AmbiguousTopLevelDecl)decl;
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ad.ModuleNames());
          } else {
            // We have found a module name or a type name, neither of which is an expression. However, the ExprDotName we're
            // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
            // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            if (!isLastNameSegment) {
              if (decl is ClassDecl && ((ClassDecl)decl).NonNullTypeDecl != null) {
                // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
                // the name of the class, C. Report an error and continue.
                reporter.Error(MessageSource.Resolver, expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              } else {
                decl = decl.ViewAsClass;
              }
            }
            r = CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
          }
        } else if (sig.StaticMembers.TryGetValue(name, out member)) {
          // ----- 2. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (member is AmbiguousMemberDecl) {
            var ambiguousMember = (AmbiguousMemberDecl)member;
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ambiguousMember.ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass, true);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, opts, allowMethodCall);
          }
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "unresolved identifier: {0}", name);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 3. Look up name in type
        Type ty;
        if (ri.TypeParamDecl != null) {
          ty = new UserDefinedType(ri.TypeParamDecl);
        } else {
          // expand any synonyms
          ty = new UserDefinedType(expr.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs).NormalizeExpand();
        }
        if (ty.IsDatatype) {
          // ----- LHS is a datatype
          var dt = ty.AsDatatype;
          Dictionary<string, DatatypeCtor> members;
          DatatypeCtor ctor;
          if (datatypeCtors.TryGetValue(dt, out members) && members.TryGetValue(name, out ctor)) {
            if (expr.OptTypeArguments != null) {
              reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
            }
            var rr = new DatatypeValue(expr.tok, ctor.EnclosingDatatype.Name, name, args ?? new List<Expression>());
            ResolveDatatypeValue(opts, rr, ctor.EnclosingDatatype, ty);
            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        }
        if (r == null && ty.IsTopLevelTypeWithMembers) {
          // ----- LHS is a class
          var cd = (TopLevelDeclWithMembers)((UserDefinedType)ty).ResolvedClass;
          Dictionary<string, MemberDecl> members;
          if (classMembers.TryGetValue(cd, out members) && members.TryGetValue(name, out member)) {
            if (!VisibleInScope(member)) {
              reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' has not been imported in this scope and cannot be accessed here", name);
            }
            if (!member.IsStatic) {
              reporter.Error(MessageSource.Resolver, expr.tok, "accessing member '{0}' requires an instance expression", name); //TODO Unify with similar error messages
              // nevertheless, continue creating an expression that approximates a correct one
            }
            var receiver = new StaticReceiverExpr(expr.tok, (UserDefinedType)ty.NormalizeExpand(), (TopLevelDeclWithMembers)member.EnclosingClass, false);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, opts, allowMethodCall);
          }
        } 
        if (r == null) {
          reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' does not exist in type '{1}'", name, ri.TypeParamDecl != null ? ri.TypeParamDecl.Name : ri.Decl.Name);
        }
      } else if (lhs != null) {
        // ----- 4. Look up name in the type of the Lhs
        NonProxyType nptype;
        member = ResolveMember(expr.tok, expr.Lhs.Type, name, out nptype);
        if (member != null) {
          Expression receiver;
          if (!member.IsStatic) {
            receiver = expr.Lhs;
          } else {
            receiver = new StaticReceiverExpr(expr.tok, (UserDefinedType)nptype, (TopLevelDeclWithMembers)member.EnclosingClass, false);
          }
          r = ResolveExprDotCall(expr.tok, receiver, nptype, member, args, expr.OptTypeArguments, opts, allowMethodCall);
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return rWithArgs;
    }

    /// <summary>
    /// To resolve "id" in expression "E . id", do:
    ///  * If E denotes a module name M:
    ///      0. Member of module M:  sub-module (including submodules of imports), class, datatype, etc.
    ///         (if two imported types have the same name, an error message is produced here)
    ///      1. Static member of M._default denoting an async task type
    ///    (Note that in contrast to ResolveNameSegment_Type, imported modules, etc. are ignored)
    ///  * If E denotes a type:
    ///      2. a. Member of that type denoting an async task type, or:
    ///         b. If allowDanglingDotName:
    ///            Return the type "E" and the given "expr", letting the caller try to make sense of the final dot-name.
    ///
    /// Note: 1 and 2a are not used now, but they will be of interest when async task types are supported.
    /// </summary>
    ResolveTypeReturn ResolveDotSuffix_Type(ExprDotName expr, ResolveOpts opts, bool allowDanglingDotName, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(expr.Lhs is NameSegment || expr.Lhs is ExprDotName);
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<ResolveTypeReturn>() == null || allowDanglingDotName);

      // resolve the LHS expression
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment_Type((NameSegment)expr.Lhs, opts, option, defaultTypeArguments);
      } else {
        ResolveDotSuffix_Type((ExprDotName)expr.Lhs, opts, false, option, defaultTypeArguments);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, opts.codeContext, option, defaultTypeArguments);
        }
      }

      Expression r = null;  // the resolved expression, if successful

      var lhs = expr.Lhs.Resolved;
      if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
        var ri = (Resolver_IdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).AccessibleSignature(useCompileSignatures);
        sig = GetSignature(sig);
        // For 0:
        TopLevelDecl decl;

        if (sig.TopLevels.TryGetValue(expr.SuffixName, out decl)) {
          // ----- 0. Member of the specified module
          if (decl is AmbiguousTopLevelDecl) {
            var ad = (AmbiguousTopLevelDecl)decl;
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ad.ModuleNames());
          } else {
            // We have found a module name or a type name.  We create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            r = CreateResolver_IdentifierExpr(expr.tok, expr.SuffixName, expr.OptTypeArguments, decl);
          }
#if ASYNC_TASK_TYPES
        } else if (sig.StaticMembers.TryGetValue(expr.SuffixName, out member)) {
          // ----- 1. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (ReallyAmbiguousThing(ref member)) {
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ((AmbiguousMemberDecl)member).ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
            r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.codeContext, allowMethodCall);
          }
#endif
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "module '{0}' does not declare a type '{1}'", ri.Decl.Name, expr.SuffixName);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 2. Look up name in type
        Type ty;
        if (ri.TypeParamDecl != null) {
          ty = new UserDefinedType(ri.TypeParamDecl);
        } else {
          ty = new UserDefinedType(expr.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs);
        }
        if (allowDanglingDotName && ty.IsRefType) {
          return new ResolveTypeReturn(ty, expr);
        }
        if (r == null) {
          reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' does not exist in type '{1}' or cannot be part of type name", expr.SuffixName, ri.TypeParamDecl != null ? ri.TypeParamDecl.Name : ri.Decl.Name);
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return null;
    }

    Expression ResolveExprDotCall(IToken tok, Expression receiver, Type receiverTypeBound/*?*/, MemberDecl member, List<Expression> args, List<Type> optTypeArguments, ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(receiver.WasResolved());
      Contract.Requires(member != null);
      Contract.Requires(opts != null && opts.codeContext != null);

      var rr = new MemberSelectExpr(tok, receiver, member.Name);
      rr.Member = member;

      // Now, fill in rr.Type.  This requires taking into consideration the type parameters passed to the receiver's type as well as any type
      // parameters used in this NameSegment/ExprDotName.
      // Add to "subst" the type parameters given to the member's class/datatype
      rr.TypeApplication = new List<Type>();
      Dictionary<TypeParameter, Type> subst;
      var rType = (receiverTypeBound ?? receiver.Type).NormalizeExpand();
      if (rType is UserDefinedType udt && udt.ResolvedClass != null) {
        subst = TypeSubstitutionMap(udt.ResolvedClass.TypeArgs, udt.TypeArgs);
        rr.TypeApplication.AddRange(udt.TypeArgs);
      } else {
        var vtd = AsValuetypeDecl(rType);
        if (vtd != null) {
          Contract.Assert(vtd.TypeArgs.Count == rType.TypeArgs.Count);
          subst = TypeSubstitutionMap(vtd.TypeArgs, rType.TypeArgs);
          rr.TypeApplication.AddRange(rType.TypeArgs);
        } else {
          Contract.Assert(rType.TypeArgs.Count == 0);
          subst = new Dictionary<TypeParameter, Type>();
        }
      }

      if (member is Field) {
        var field = (Field)member;
        if (optTypeArguments != null) {
          reporter.Error(MessageSource.Resolver, tok, "a field ({0}) does not take any type arguments (got {1})", field.Name, optTypeArguments.Count);
        }
        subst = BuildTypeArgumentSubstitute(subst);
        rr.Type = SubstType(field.Type, subst);
        AddCallGraphEdgeForField(opts.codeContext, field, rr);
      } else if (member is Function) {
        var fn = (Function)member;
        if (fn is TwoStateFunction && !opts.twoState) {
          reporter.Error(MessageSource.Resolver, tok, "two-state function ('{0}') can only be called in a two-state context", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != fn.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "function '{0}' expects {1} type arguments (got {2})", member.Name, fn.TypeArgs.Count, suppliedTypeArguments);
        }
        for (int i = 0; i < fn.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication.Add(ta);
          subst.Add(fn.TypeArgs[i], ta);
        }
        subst = BuildTypeArgumentSubstitute(subst);
        rr.Type = SelectAppropriateArrowType(fn.tok,
          fn.Formals.ConvertAll(f => SubstType(f.Type, subst)),
          SubstType(fn.ResultType, subst),
          fn.Reads.Count != 0, fn.Req.Count != 0);
        AddCallGraphEdge(opts.codeContext, fn, rr, IsFunctionReturnValue(fn, args, opts));
      } else {
        // the member is a method
        var m = (Method)member;
        if (!allowMethodCall) {
          // it's a method and method calls are not allowed in the given context
          reporter.Error(MessageSource.Resolver, tok, "expression is not allowed to invoke a method ({0})", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != m.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "method '{0}' expects {1} type arguments (got {2})", member.Name, m.TypeArgs.Count, suppliedTypeArguments);
        }
        for (int i = 0; i < m.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication.Add(ta);
        }
        rr.Type = new InferredTypeProxy();  // fill in this field, in order to make "rr" resolved
      }
      return rr;
    }

    private bool IsFunctionReturnValue(Function fn, List<Expression> args, ResolveOpts opts) {
      bool isFunctionReturnValue = true;
      // if the call is in post-condition and it is calling itself, and the arguments matches
      // formal parameter, then it denotes function return value.
      if (args != null && opts.isPostCondition && opts.codeContext == fn) {
        foreach (var arg in args) {
          if (arg is NameSegment) {
            var name = ((NameSegment)arg).Name;
            IVariable v = scope.Find(name);
            if (!(v is Formal)) {
              isFunctionReturnValue = false;
            }
          } else {
            isFunctionReturnValue = false;
          }
        }
      } else {
        isFunctionReturnValue = false;
      }
      return isFunctionReturnValue;
    }

    class MethodCallInformation
    {
      public readonly IToken Tok;
      public readonly MemberSelectExpr Callee;
      public readonly List<Expression> Args;

      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Tok != null);
        Contract.Invariant(Callee != null);
        Contract.Invariant(Callee.Member is Method);
        Contract.Invariant(cce.NonNullElements(Args));
      }

      public MethodCallInformation(IToken tok, MemberSelectExpr callee, List<Expression> args) {
        Contract.Requires(tok != null);
        Contract.Requires(callee != null);
        Contract.Requires(callee.Member is Method);
        Contract.Requires(cce.NonNullElements(args));
        this.Tok = tok;
        this.Callee = callee;
        this.Args = args;
      }
    }

    MethodCallInformation ResolveRevealExpr(RevealExpr e, ResolveOpts opts, bool allowMethodCall) {
      var revealOpts = new ResolveOpts(opts.codeContext, opts.twoState, true, opts.isPostCondition, opts.InsideOld);
      MethodCallInformation info = null;
      if (e.Expr is ApplySuffix) {
        info = ResolveApplySuffix((ApplySuffix)e.Expr, revealOpts, true);
      } else {
        ResolveExpression(e.Expr, revealOpts);
      }
      return info;
    }

    MethodCallInformation ResolveApplySuffix(ApplySuffix e, ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(e != null);
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<MethodCallInformation>() == null || allowMethodCall);
      Expression r = null;  // upon success, the expression to which the ApplySuffix resolves
      var errorCount = reporter.Count(ErrorLevel.Error);
      if (e.Lhs is NameSegment) {
        r = ResolveNameSegment((NameSegment)e.Lhs, true, e.Args, opts, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else if (e.Lhs is ExprDotName) {
        r = ResolveDotSuffix((ExprDotName)e.Lhs, true, e.Args, opts, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else {
        ResolveExpression(e.Lhs, opts);
      }
      if (r == null) {
        foreach (var arg in e.Args) {
          ResolveExpression(arg, opts);
        }
        var improvedType = PartiallyResolveTypeForMemberSelection(e.Lhs.tok, e.Lhs.Type, "_#apply");
        var fnType = improvedType.AsArrowType;
        if (fnType == null) {
          var lhs = e.Lhs.Resolved;
          if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
            reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a function", ((Resolver_IdentifierExpr)lhs).Decl.Name);
          } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            // It may be a conversion expression
            var ri = (Resolver_IdentifierExpr)lhs;
            if (ri.TypeParamDecl != null) {
              reporter.Error(MessageSource.Resolver, e.tok, "name of type parameter ({0}) is used as a function", ri.TypeParamDecl.Name);
            } else {
              var decl = ri.Decl;
              var ty = new UserDefinedType(e.tok, decl.Name, decl, ri.TypeArgs);
              if (ty.AsNewtype != null) {
                reporter.Deprecated(MessageSource.Resolver, e.tok, "the syntax \"{0}(expr)\" for type conversions has been deprecated; the new syntax is \"expr as {0}\"", decl.Name);
                if (e.Args.Count != 1) {
                  reporter.Error(MessageSource.Resolver, e.tok, "conversion operation to {0} got wrong number of arguments (expected 1, got {1})", decl.Name, e.Args.Count);
                }
                var conversionArg = 1 <= e.Args.Count ? e.Args[0] :
                  ty.IsNumericBased(Type.NumericPersuation.Int) ? LiteralExpr.CreateIntLiteral(e.tok, 0) :
                  LiteralExpr.CreateRealLiteral(e.tok, Basetypes.BigDec.ZERO);
                r = new ConversionExpr(e.tok, conversionArg, ty);
                ResolveExpression(r, opts);
                // resolve the rest of the arguments, if any
                for (int i = 1; i < e.Args.Count; i++) {
                  ResolveExpression(e.Args[i], opts);
                }
              } else {
                reporter.Error(MessageSource.Resolver, e.tok, "name of type ({0}) is used as a function", decl.Name);
              }
            }
          } else {
            if (lhs is MemberSelectExpr && ((MemberSelectExpr)lhs).Member is Method) {
              var mse = (MemberSelectExpr)lhs;
              if (allowMethodCall) {
                var cRhs = new MethodCallInformation(e.tok, mse, e.Args);
                return cRhs;
              } else {
                reporter.Error(MessageSource.Resolver, e.tok, "method call is not allowed to be used in an expression context ({0})", mse.Member.Name);
              }
            } else if (lhs != null) {  // if e.Lhs.Resolved is null, then e.Lhs was not successfully resolved and an error has already been reported
              reporter.Error(MessageSource.Resolver, e.tok, "non-function expression (of type {0}) is called with parameters", e.Lhs.Type);
            }
          }
        } else {
          var mse = e.Lhs is NameSegment || e.Lhs is ExprDotName ? e.Lhs.Resolved as MemberSelectExpr : null;
          var callee = mse == null ? null : mse.Member as Function;
          if (fnType.Arity != e.Args.Count) {
            var what = callee != null ? string.Format("function '{0}'", callee.Name) : string.Format("function type '{0}'", fnType);
            reporter.Error(MessageSource.Resolver, e.tok, "wrong number of arguments to function application ({0} expects {1}, got {2})", what, fnType.Arity, e.Args.Count);
          } else {
            for (var i = 0; i < fnType.Arity; i++) {
              AddAssignableConstraint(e.Args[i].tok, fnType.Args[i], e.Args[i].Type, "type mismatch for argument" + (fnType.Arity == 1 ? "" : " " + i) + " (function expects {0}, got {1})");
            }
            if (errorCount != reporter.Count(ErrorLevel.Error)) {
              // do nothing else; error has been reported
            } else if (callee != null) {
              // produce a FunctionCallExpr instead of an ApplyExpr(MemberSelectExpr)
              var rr = new FunctionCallExpr(e.Lhs.tok, callee.Name, mse.Obj, e.tok, e.Args);
              // resolve it here:
              rr.Function = callee;
              Contract.Assert(!(mse.Obj is StaticReceiverExpr) || callee.IsStatic);  // this should have been checked already
              Contract.Assert(callee.Formals.Count == rr.Args.Count);  // this should have been checked already
              // build the type substitution map
              rr.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>();
              int enclosingTypeArgsCount = callee.EnclosingClass == null ? 0 : callee.EnclosingClass.TypeArgs.Count;
              Contract.Assert(mse.TypeApplication.Count == enclosingTypeArgsCount + callee.TypeArgs.Count);
              for (int i = 0; i < enclosingTypeArgsCount; i++) {
                rr.TypeArgumentSubstitutions.Add(callee.EnclosingClass.TypeArgs[i], mse.TypeApplication[i]);
              }

              for (int i = 0; i < callee.TypeArgs.Count; i++) {
                rr.TypeArgumentSubstitutions.Add(callee.TypeArgs[i], mse.TypeApplication[enclosingTypeArgsCount + i]);
              }
              Dictionary<TypeParameter, Type> subst = BuildTypeArgumentSubstitute(rr.TypeArgumentSubstitutions);

              // type check the arguments
#if DEBUG
              Contract.Assert(callee.Formals.Count == fnType.Arity);
              for (int i = 0; i < callee.Formals.Count; i++) {
                Expression farg = rr.Args[i];
                Contract.Assert(farg.WasResolved());
                Contract.Assert(farg.Type != null);
                Type s = SubstType(callee.Formals[i].Type, subst);
                Contract.Assert(s.Equals(fnType.Args[i]));
                Contract.Assert(farg.Type.Equals(e.Args[i].Type));
              }
#endif
              rr.Type = SubstType(callee.ResultType, subst);
              // further bookkeeping
              if (callee is FixpointPredicate) {
                ((FixpointPredicate)callee).Uses.Add(rr);
              }
              AddCallGraphEdge(opts.codeContext, callee, rr, IsFunctionReturnValue(callee, e.Args, opts));
              r = rr;
            } else {
              r = new ApplyExpr(e.Lhs.tok, e.Lhs, e.Args);
              r.Type = fnType.Result;
            }
          }
        }
      }
      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        e.Type = new InferredTypeProxy();
      } else {
        e.ResolvedExpression = r;
        e.Type = r.Type;
      }
      return null;
    }

    private Dictionary<TypeParameter, Type> BuildTypeArgumentSubstitute(Dictionary<TypeParameter, Type> typeArgumentSubstitutions) {
      Contract.Requires(typeArgumentSubstitutions != null);

      Dictionary<TypeParameter, Type> subst = new Dictionary<TypeParameter, Type>();
      foreach (var entry in typeArgumentSubstitutions) {
        subst.Add(entry.Key, entry.Value);
      }

      if (SelfTypeSubstitution != null) {
        foreach (var entry in SelfTypeSubstitution) {
          subst.Add(entry.Key, entry.Value);
        }
      }
      return subst;
    }

    private void ResolveDatatypeValue(ResolveOpts opts, DatatypeValue dtv, DatatypeDecl dt, Type ty) {
      Contract.Requires(opts != null);
      Contract.Requires(dtv != null);
      Contract.Requires(dt != null);
      Contract.Requires(ty == null || (ty.AsDatatype == dt && ty.TypeArgs.Count == dt.TypeArgs.Count));

      var gt = new List<Type>(dt.TypeArgs.Count);
      var subst = new Dictionary<TypeParameter, Type>();
      for (int i = 0; i < dt.TypeArgs.Count; i++) {
        Type t = ty == null ? new InferredTypeProxy() : ty.TypeArgs[i];
        gt.Add(t);
        dtv.InferredTypeArgs.Add(t);
        subst.Add(dt.TypeArgs[i], t);
      }
      // Construct a resolved type directly, as we know the declaration is dt.
      dtv.Type = new UserDefinedType(dtv.tok, dt.Name, dt, gt);

      DatatypeCtor ctor;
      if (!datatypeCtors[dt].TryGetValue(dtv.MemberName, out ctor)) {
        reporter.Error(MessageSource.Resolver, dtv.tok, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
      } else {
        Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
        dtv.Ctor = ctor;
        if (ctor.Formals.Count != dtv.Arguments.Count) {
          reporter.Error(MessageSource.Resolver, dtv.tok, "wrong number of arguments to datatype constructor {0} (found {1}, expected {2})", ctor.Name, dtv.Arguments.Count, ctor.Formals.Count);
        }
      }
      int j = 0;
      foreach (var arg in dtv.Arguments) {
        Formal formal = ctor != null && j < ctor.Formals.Count ? ctor.Formals[j] : null;
        ResolveExpression(arg, opts);
        Contract.Assert(arg.Type != null);  // follows from postcondition of ResolveExpression
        if (formal != null) {
          Type st = SubstType(formal.Type, subst);
          AddAssignableConstraint(arg.tok, st, arg.Type, "incorrect type of datatype constructor argument (found {1}, expected {0})");
        }
        j++;
      }
    }

    /// <summary>
    /// Generate an error for every non-ghost feature used in "expr".
    /// Requires "expr" to have been successfully resolved.
    /// </summary>
    void CheckIsCompilable(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved

      if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        if (e.Var != null && e.Var.IsGhost) {
          reporter.Error(MessageSource.Resolver, expr, "ghost variables are allowed only in specification contexts");
          return;
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member != null && e.Member.IsGhost) {
          reporter.Error(MessageSource.Resolver, expr, "ghost fields are allowed only in specification contexts");
          return;
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (e.Function != null) {
          if (e.Function.IsGhost) {
            reporter.Error(MessageSource.Resolver, expr, "function calls are allowed only in specification contexts (consider declaring the function a 'function method')");
            return;
          }
          // function is okay, so check all NON-ghost arguments
          CheckIsCompilable(e.Receiver);
          for (int i = 0; i < e.Function.Formals.Count; i++) {
            if (!e.Function.Formals[i].IsGhost) {
              CheckIsCompilable(e.Args[i]);
            }
          }
        }
        return;

      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        // check all NON-ghost arguments
        // note that if resolution is successful, then |e.Arguments| == |e.Ctor.Formals|
        for (int i = 0; i < e.Arguments.Count; i++) {
          if (!e.Ctor.Formals[i].IsGhost) {
            CheckIsCompilable(e.Arguments[i]);
          }
        }
        return;

      } else if (expr is OldExpr) {
        reporter.Error(MessageSource.Resolver, expr, "old expressions are allowed only in specification and ghost contexts");
        return;

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Fresh) {
          reporter.Error(MessageSource.Resolver, expr, "fresh expressions are allowed only in specification and ghost contexts");
          return;
        }

      } else if (expr is UnchangedExpr) {
        reporter.Error(MessageSource.Resolver, expr, "unchanged expressions are allowed only in specification and ghost contexts");
        return;

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        // ignore the statement
        CheckIsCompilable(e.E);
        return;

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        switch (e.ResolvedOp_PossiblyStillUndetermined) {
          case BinaryExpr.ResolvedOpcode.RankGt:
          case BinaryExpr.ResolvedOpcode.RankLt:
            reporter.Error(MessageSource.Resolver, expr, "rank comparisons are allowed only in specification and ghost contexts");
            return;
          default:
            break;
        }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            reporter.Error(MessageSource.Resolver, expr, "prefix equalities are allowed only in specification and ghost contexts");
            return;
          default:
            break;
        }
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          Contract.Assert(e.LHSs.Count == e.RHSs.Count);
          var i = 0;
          foreach (var ee in e.RHSs) {
            if (!e.LHSs[i].Vars.All(bv => bv.IsGhost)) {
              CheckIsCompilable(ee);
            }
            i++;
          }
          CheckIsCompilable(e.Body);
        } else {
          Contract.Assert(e.RHSs.Count == 1);
          var lhsVarsAreAllGhost = e.BoundVars.All(bv => bv.IsGhost);
          if (!lhsVarsAreAllGhost) {
            CheckIsCompilable(e.RHSs[0]);
          }
          CheckIsCompilable(e.Body);

          // fill in bounds for this to-be-compiled let-such-that expression
          Contract.Assert(e.RHSs.Count == 1);  // if we got this far, the resolver will have checked this condition successfully
          var constraint = e.RHSs[0];
          e.Constraint_Bounds = DiscoverBestBounds_MultipleVars(e.BoundVars.ToList<IVariable>(), constraint, true, ComprehensionExpr.BoundedPool.PoolVirtues.None);
        }
        return;
      } else if (expr is LambdaExpr) {
        var e = expr as LambdaExpr;
        CheckIsCompilable(e.Body);
        return;
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var uncompilableBoundVars = e.UncompilableBoundVars();
        if (uncompilableBoundVars.Count != 0) {
          string what;
          if (e is SetComprehension) {
            what = ((SetComprehension)e).Finite ? "set comprehensions" : "iset comprehensions";
          } else if (e is MapComprehension) {
            what = ((MapComprehension)e).Finite ? "map comprehensions" : "imap comprehensions";
          } else {
            Contract.Assume(e is QuantifierExpr);  // otherwise, unexpected ComprehensionExpr (since LambdaExpr is handled separately above)
            Contract.Assert(((QuantifierExpr)e).SplitQuantifier == null); // No split quantifiers during resolution
            what = "quantifiers";
          }
          foreach (var bv in uncompilableBoundVars) {
            reporter.Error(MessageSource.Resolver, expr, "{0} in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{1}'", what, bv.Name);
          }
          return;
        }
        // don't recurse down any attributes
        if (e.Range != null) { CheckIsCompilable(e.Range); }
        CheckIsCompilable(e.Term);
        return;

      } else if (expr is NamedExpr) {
        if (!moduleInfo.IsAbstract)
          CheckIsCompilable(((NamedExpr)expr).Body);
        return;
      } else if (expr is ChainingExpression) {
        // We don't care about the different operators; we only want the operands, so let's get them directly from
        // the chaining expression
        var e = (ChainingExpression)expr;
        e.Operands.ForEach(CheckIsCompilable);
        return;
      }

      foreach (var ee in expr.SubExpressions) {
        CheckIsCompilable(ee);
      }
    }

    public void ResolveFunctionCallExpr(FunctionCallExpr e, ResolveOpts opts) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type == null);  // should not have been type checked before

      ResolveReceiver(e.Receiver, opts);
      Contract.Assert(e.Receiver.Type != null);  // follows from postcondition of ResolveExpression
      NonProxyType nptype;

      MemberDecl member = ResolveMember(e.tok, e.Receiver.Type, e.Name, out nptype);
#if !NO_WORK_TO_BE_DONE
      UserDefinedType ctype = (UserDefinedType)nptype;
#endif
      if (member == null) {
        // error has already been reported by ResolveMember
      } else if (member is Method) {
        reporter.Error(MessageSource.Resolver, e, "member {0} in type {1} refers to a method, but only functions can be used in this context", e.Name, cce.NonNull(ctype).Name);
      } else if (!(member is Function)) {
        reporter.Error(MessageSource.Resolver, e, "member {0} in type {1} does not refer to a function", e.Name, cce.NonNull(ctype).Name);
      } else {
        Function function = (Function)member;
        e.Function = function;
        if (function is FixpointPredicate) {
          ((FixpointPredicate)function).Uses.Add(e);
        }
        if (function is TwoStateFunction && !opts.twoState) {
          reporter.Error(MessageSource.Resolver, e.tok, "a two-state function can be used only in a two-state context");
        }
        if (e.Receiver is StaticReceiverExpr && !function.IsStatic) {
          reporter.Error(MessageSource.Resolver, e, "an instance function must be selected via an object, not just a class name");
        }
        if (function.Formals.Count != e.Args.Count) {
          reporter.Error(MessageSource.Resolver, e, "wrong number of function arguments (got {0}, expected {1})", e.Args.Count, function.Formals.Count);
        } else {
          Contract.Assert(ctype != null);  // follows from postcondition of ResolveMember
          if (!function.IsStatic) {
            if (!scope.AllowInstance && e.Receiver is ThisExpr) {
              // The call really needs an instance, but that instance is given as 'this', which is not
              // available in this context.  In most cases, occurrences of 'this' inside e.Receiver would
              // have been caught in the recursive call to resolve e.Receiver, but not the specific case
              // of e.Receiver being 'this' (explicitly or implicitly), for that case needs to be allowed
              // in the event that a static function calls another static function (and note that we need the
              // type of the receiver in order to find the method, so we could not have made this check
              // earlier).
              reporter.Error(MessageSource.Resolver, e.Receiver, "'this' is not allowed in a 'static' context");
            } else if (e.Receiver is StaticReceiverExpr) {
              reporter.Error(MessageSource.Resolver, e.Receiver, "call to instance function requires an instance");
            }
          }
          // build the type substitution map
          e.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>();
          for (int i = 0; i < ctype.TypeArgs.Count; i++) {
            e.TypeArgumentSubstitutions.Add(cce.NonNull(ctype.ResolvedClass).TypeArgs[i], ctype.TypeArgs[i]);
          }
          foreach (TypeParameter p in function.TypeArgs) {
            e.TypeArgumentSubstitutions.Add(p, new ParamTypeProxy(p));
          }
          Dictionary<TypeParameter, Type> subst = BuildTypeArgumentSubstitute(e.TypeArgumentSubstitutions);

          // type check the arguments
          for (int i = 0; i < function.Formals.Count; i++) {
            Expression farg = e.Args[i];
            ResolveExpression(farg, opts);
            Contract.Assert(farg.Type != null);  // follows from postcondition of ResolveExpression
            Type s = SubstType(function.Formals[i].Type, subst);
            AddAssignableConstraint(e.tok, s, farg.Type, "incorrect type of function argument" + (function.Formals.Count == 1 ? "" : " " + i) + " (expected {0}, got {1})");
          }
          e.Type = SubstType(function.ResultType, subst).NormalizeExpand();
        }
        AddCallGraphEdge(opts.codeContext, function, e, IsFunctionReturnValue(function, e.Args, opts));
      }
    }

    private void AddCallGraphEdgeForField(ICodeContext callingContext, Field field, Expression e) {
      Contract.Requires(callingContext != null);
      Contract.Requires(field != null);
      Contract.Requires(e != null);
      var cf = field as ConstantField;
      if (cf != null) {
        if (cf == callingContext) {
          // detect self-loops here, since they don't show up in the graph's SSC methods
          reporter.Error(MessageSource.Resolver, cf.tok, "recursive dependency involving constant initialization: {0} -> {0}", cf.Name);
        } else {
          AddCallGraphEdge(callingContext, cf, e, false);
        }
      }
    }

    private static void AddCallGraphEdge(ICodeContext callingContext, ICallable function, Expression e, bool isFunctionReturnValue) {
      Contract.Requires(callingContext != null);
      Contract.Requires(function != null);
      Contract.Requires(e != null);
      // Resolution termination check
      ModuleDefinition callerModule = callingContext.EnclosingModule;
      ModuleDefinition calleeModule = function is SpecialFunction ? null : function.EnclosingModule;
      if (callerModule == calleeModule) {
        // intra-module call; add edge in module's call graph
        var caller = callingContext as ICallable;
        if (caller == null) {
          // don't add anything to the call graph after all
        } else if (caller is IteratorDecl) {
          callerModule.CallGraph.AddEdge(((IteratorDecl)callingContext).Member_MoveNext, function);
        } else {
          callerModule.CallGraph.AddEdge(caller, function);
          if (caller is Function) {
            FunctionCallExpr ee = e as FunctionCallExpr;
            if (ee != null) {
              ((Function)caller).AllCalls.Add(ee);
            }
          }
          // if the call denotes the function return value in the function postconditions, then we don't
          // mark it as recursive.
          if (caller == function && (function is Function) && !isFunctionReturnValue) {
            ((Function)function).IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
          }
        }
      }
    }


    private static ModuleSignature GetSignatureExt(ModuleSignature sig, bool useCompileSignatures) {
      Contract.Requires(sig != null);
      Contract.Ensures(Contract.Result<ModuleSignature>() != null);
      if (useCompileSignatures) {
        while (sig.CompileSignature != null)
          sig = sig.CompileSignature;
      }
      return sig;
    }

    private ModuleSignature GetSignature(ModuleSignature sig) {
      return GetSignatureExt(sig, useCompileSignatures);
    }

    public static List<ComprehensionExpr.BoundedPool> DiscoverBestBounds_MultipleVars_AllowReordering<VT>(List<VT> bvars, Expression expr, bool polarity, ComprehensionExpr.BoundedPool.PoolVirtues requiredVirtues) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<ComprehensionExpr.BoundedPool>>() != null);
      var bounds = DiscoverBestBounds_MultipleVars(bvars, expr, polarity, requiredVirtues);
      if (bvars.Count > 1) {
        // It may be helpful to try all permutations (or, better yet, to use an algorithm that keeps track of the dependencies
        // and discovers good bounds more efficiently). However, all permutations would be expensive. Therefore, we try just one
        // other permutation, namely the reversal "bvars". This covers the important case where there are two bound variables
        // that work out in the opposite order. It also covers one more case for the (probably rare) case of there being more
        // than two bound variables.
        var bvarsMissyElliott = new List<VT>(bvars);  // make a copy
        bvarsMissyElliott.Reverse();  // and then flip it and reverse it, Ti esrever dna ti pilf nwod gniht ym tup I
        var boundsMissyElliott = DiscoverBestBounds_MultipleVars(bvarsMissyElliott, expr, polarity, requiredVirtues);
        // Figure out which one seems best
        var meBetter = 0;
        for (int i = 0; i < bvars.Count; i++) {
          var orig = bounds[i];
          var me = boundsMissyElliott[i];
          if (orig == null && me != null) {
            meBetter = 1; break; // end game
          } else if (orig != null && me == null) {
            meBetter = -1; break; // end game
          } else if (orig != null && me != null) {
            if ((orig.Virtues & ComprehensionExpr.BoundedPool.PoolVirtues.Finite) != 0) { meBetter--; }
            if ((orig.Virtues & ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable) != 0) { meBetter--; }
            if ((me.Virtues & ComprehensionExpr.BoundedPool.PoolVirtues.Finite) != 0) { meBetter++; }
            if ((me.Virtues & ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable) != 0) { meBetter++; }
          }
        }
        if (meBetter > 0) {
          // yes, this reordering seems to have been better
          bvars.Reverse();
          return boundsMissyElliott;
        }
      }
      return bounds;
    }

    /// <summary>
    /// For a list of variables "bvars", returns a list of best bounds, subject to the constraint "requiredVirtues", for each respective variable.
    /// If no bound matching "requiredVirtues" is found for a variable "v", then the bound for "v" in the returned list is set to "null".
    /// </summary>
    public static List<ComprehensionExpr.BoundedPool> DiscoverBestBounds_MultipleVars<VT>(List<VT> bvars, Expression expr, bool polarity, ComprehensionExpr.BoundedPool.PoolVirtues requiredVirtues) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<ComprehensionExpr.BoundedPool>>() != null);
      foreach (var bv in bvars) {
        var c = GetImpliedTypeConstraint(bv, bv.Type);
        expr = polarity ? Expression.CreateAnd(c, expr) : Expression.CreateImplies(c, expr);
      }
      var bests = DiscoverAllBounds_Aux_MultipleVars(bvars, expr, polarity, requiredVirtues);
      return bests;
    }

    public static List<ComprehensionExpr.BoundedPool> DiscoverAllBounds_SingleVar<VT>(VT v, Expression expr) where VT : IVariable {
      expr = Expression.CreateAnd(GetImpliedTypeConstraint(v, v.Type), expr);
      return DiscoverAllBounds_Aux_SingleVar(new List<VT> { v }, 0, expr, true, new List<ComprehensionExpr.BoundedPool>() { null });
    }

    private static List<ComprehensionExpr.BoundedPool> DiscoverAllBounds_Aux_MultipleVars<VT>(List<VT> bvars, Expression expr, bool polarity, ComprehensionExpr.BoundedPool.PoolVirtues requiredVirtues) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<ComprehensionExpr.BoundedPool>>() != null);
      Contract.Ensures(Contract.Result<List<ComprehensionExpr.BoundedPool>>().Count == bvars.Count);
      var knownBounds = new List<ComprehensionExpr.BoundedPool>();
      for (var j = 0; j < bvars.Count; j++) {
        knownBounds.Add(null);
      }
      for (var j = bvars.Count; 0 <= --j; ) {  // important to go backwards, because DiscoverAllBounds_Aux_SingleVar assumes "knownBounds" has been filled in for higher-indexed variables
        var bounds = DiscoverAllBounds_Aux_SingleVar(bvars, j, expr, polarity, knownBounds);
        knownBounds[j] = ComprehensionExpr.BoundedPool.GetBest(bounds, requiredVirtues);
#if DEBUG_PRINT
        if (knownBounds[j] is ComprehensionExpr.IntBoundedPool) {
          var ib = (ComprehensionExpr.IntBoundedPool)knownBounds[j];
          var lo = ib.LowerBound == null ? "" : Printer.ExprToString(ib.LowerBound);
          var hi = ib.UpperBound == null ? "" : Printer.ExprToString(ib.UpperBound);
          Console.WriteLine("DEBUG: Bound for var {3}, {0}:  {1} .. {2}", bvars[j].Name, lo, hi, j);
        } else if (knownBounds[j] is ComprehensionExpr.SetBoundedPool) {
          Console.WriteLine("DEBUG: Bound for var {2}, {0}:  in {1}", bvars[j].Name, Printer.ExprToString(((ComprehensionExpr.SetBoundedPool)knownBounds[j]).Set), j);
        } else {
          Console.WriteLine("DEBUG: Bound for var {2}, {0}:  {1}", bvars[j].Name, knownBounds[j], j);
        }
#endif
      }
      return knownBounds;
    }

    /// <summary>
    /// Returns a list of (possibly partial) bounds for "bvars[j]", each of which can be written without mentioning any variable in "bvars[j..]" that is not bounded.
    /// </summary>
    private static List<ComprehensionExpr.BoundedPool> DiscoverAllBounds_Aux_SingleVar<VT>(List<VT> bvars, int j, Expression expr, bool polarity, List<ComprehensionExpr.BoundedPool> knownBounds) where VT : IVariable {
      Contract.Requires(bvars != null);
      Contract.Requires(0 <= j && j < bvars.Count);
      Contract.Requires(expr != null);
      Contract.Requires(knownBounds != null);
      Contract.Requires(knownBounds.Count == bvars.Count);
      var bv = bvars[j];
      var bounds = new List<ComprehensionExpr.BoundedPool>();

      // Maybe the type itself gives a bound
      if (bv.Type.IsBoolType) {
        bounds.Add(new ComprehensionExpr.BoolBoundedPool());
      } else if (bv.Type.IsCharType) {
        bounds.Add(new ComprehensionExpr.CharBoundedPool());
      } else if (bv.Type.IsDatatype && bv.Type.AsDatatype.HasFinitePossibleValues) {
        bounds.Add(new ComprehensionExpr.DatatypeBoundedPool(bv.Type.AsIndDatatype));
      } else if (bv.Type.IsNumericBased(Type.NumericPersuation.Int)) {
        bounds.Add(new AssignSuchThatStmt.WiggleWaggleBound());
      } else if (bv.Type.IsAllocFree) {
        bounds.Add(new ComprehensionExpr.AllocFreeBoundedPool(bv.Type));
      }

      // Go through the conjuncts of the range expression to look for bounds.
      foreach (var conjunct in NormalizedConjuncts(expr, polarity)) {
        if (conjunct is IdentifierExpr) {
          var ide = (IdentifierExpr)conjunct;
          if (ide.Var == (IVariable)bv) {
            Contract.Assert(bv.Type.IsBoolType);
            bounds.Add(new ComprehensionExpr.ExactBoundedPool(Expression.CreateBoolLiteral(Token.NoToken, true)));
          }
          continue;
        }
        if (conjunct is UnaryExpr || conjunct is OldExpr) {
          // we also consider a unary expression sitting immediately inside an old
          var unary = conjunct as UnaryOpExpr ?? ((OldExpr)conjunct).E.Resolved as UnaryOpExpr;
          if (unary != null) {
            var ide = unary.E.Resolved as IdentifierExpr;
            if (ide != null && ide.Var == (IVariable)bv) {
              if (unary.Op == UnaryOpExpr.Opcode.Not) {
                Contract.Assert(bv.Type.IsBoolType);
                bounds.Add(new ComprehensionExpr.ExactBoundedPool(Expression.CreateBoolLiteral(Token.NoToken, false)));
              } else if (unary.Op == UnaryOpExpr.Opcode.Allocated) {
                bounds.Add(new ComprehensionExpr.ExplicitAllocatedBoundedPool());
              }
            }
          }
          continue;
        }
        var c = conjunct as BinaryExpr;
        if (c == null) {
          // other than what we already covered above, we only know what to do with binary expressions
          continue;
        }
        var e0 = c.E0;
        var e1 = c.E1;
        int whereIsBv = SanitizeForBoundDiscovery(bvars, j, c.ResolvedOp, knownBounds, ref e0, ref e1);
        if (whereIsBv < 0) {
          continue;
        }
        switch (c.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.InSet:
            if (whereIsBv == 0) {
              bounds.Add(new ComprehensionExpr.SetBoundedPool(e1, e0.Type.Equals(e1.Type.AsSetType.Arg), e1.Type.AsSetType.Finite));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Subset:
            if (whereIsBv == 0) {
              bounds.Add(new ComprehensionExpr.SubSetBoundedPool(e1, e1.Type.AsSetType.Finite));
            } else {
              bounds.Add(new ComprehensionExpr.SuperSetBoundedPool(e0));
            }
            break;
          case BinaryExpr.ResolvedOpcode.InMultiSet:
            if (whereIsBv == 0) {
              bounds.Add(new ComprehensionExpr.MultiSetBoundedPool(e1, e0.Type.Equals(e1.Type.AsMultiSetType.Arg)));
            }
            break;
          case BinaryExpr.ResolvedOpcode.InSeq:
            if (whereIsBv == 0) {
              bounds.Add(new ComprehensionExpr.SeqBoundedPool(e1, e0.Type.Equals(e1.Type.AsSeqType.Arg)));
            }
            break;
          case BinaryExpr.ResolvedOpcode.InMap:
            if (whereIsBv == 0) {
              bounds.Add(new ComprehensionExpr.MapBoundedPool(e1, e0.Type.Equals(e1.Type.AsMapType.Arg), e1.Type.AsMapType.Finite));
            }
            break;
          case BinaryExpr.ResolvedOpcode.EqCommon:
          case BinaryExpr.ResolvedOpcode.SetEq:
          case BinaryExpr.ResolvedOpcode.SeqEq:
          case BinaryExpr.ResolvedOpcode.MultiSetEq:
          case BinaryExpr.ResolvedOpcode.MapEq:
            var otherOperand = whereIsBv == 0 ? e1 : e0;
            bounds.Add(new ComprehensionExpr.ExactBoundedPool(otherOperand));
            break;
          case BinaryExpr.ResolvedOpcode.Gt:
          case BinaryExpr.ResolvedOpcode.Ge:
            Contract.Assert(false); throw new cce.UnreachableException();  // promised by postconditions of NormalizedConjunct
          case BinaryExpr.ResolvedOpcode.Lt:
            if (e0.Type.IsNumericBased(Type.NumericPersuation.Int)) {
              if (whereIsBv == 0) {  // bv < E
                bounds.Add(new ComprehensionExpr.IntBoundedPool(null, e1));
              } else {  // E < bv
                bounds.Add(new ComprehensionExpr.IntBoundedPool(Expression.CreateIncrement(e0, 1), null));
              }
            }
            break;
          case BinaryExpr.ResolvedOpcode.Le:
            if (e0.Type.IsNumericBased(Type.NumericPersuation.Int)) {
              if (whereIsBv == 0) {  // bv <= E
                bounds.Add(new ComprehensionExpr.IntBoundedPool(null, Expression.CreateIncrement(e1, 1)));
              } else {  // E <= bv
                bounds.Add(new ComprehensionExpr.IntBoundedPool(e0, null));
              }
            }
            break;
          case BinaryExpr.ResolvedOpcode.RankLt:
            if (whereIsBv == 0) {
              bounds.Add(new ComprehensionExpr.DatatypeInclusionBoundedPool(e0.Type.IsIndDatatype));
            }
            break;
          case BinaryExpr.ResolvedOpcode.RankGt:
            if (whereIsBv == 1) {
              bounds.Add(new ComprehensionExpr.DatatypeInclusionBoundedPool(e1.Type.IsIndDatatype));
            }
            break;
          default:
            break;
        }
      }
      return bounds;
    }

    private static Translator translator = new Translator(null);

    public static Expression GetImpliedTypeConstraint(IVariable bv, Type ty) {
      return GetImpliedTypeConstraint(Expression.CreateIdentExpr(bv), ty);
    }

    public static Expression GetImpliedTypeConstraint(Expression e, Type ty) {
      Contract.Requires(e != null);
      Contract.Requires(ty != null);
      ty = ty.NormalizeExpandKeepConstraints();
      var udt = ty as UserDefinedType;
      if (udt != null) {
        if (udt.ResolvedClass is NewtypeDecl) {
          var dd = (NewtypeDecl)udt.ResolvedClass;
          var c = GetImpliedTypeConstraint(e, dd.BaseType);
          if (dd.Var != null) {
            Dictionary<IVariable, Expression/*!*/> substMap = new Dictionary<IVariable, Expression>();
            substMap.Add(dd.Var, e);
            Translator.Substituter sub = new Translator.Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
            c = Expression.CreateAnd(c, sub.Substitute(dd.Constraint));
          }
          return c;
        } else if (udt.ResolvedClass is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)udt.ResolvedClass;
          var c = GetImpliedTypeConstraint(e, dd.RhsWithArgument(udt.TypeArgs));
          Dictionary<IVariable, Expression/*!*/> substMap = new Dictionary<IVariable, Expression>();
          substMap.Add(dd.Var, e);
          Translator.Substituter sub = new Translator.Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
          c = Expression.CreateAnd(c, sub.Substitute(dd.Constraint));
          return c;
        }
      }
      return Expression.CreateBoolLiteral(e.tok, true);
    }

    /// <summary>
    /// If the return value is negative, the resulting "e0" and "e1" should not be used.
    /// Otherwise, the following is true on return:
    /// The new "e0 op e1" is equivalent to the old "e0 op e1".
    /// One of "e0" and "e1" is the identifier "boundVars[bvi]"; the return value is either 0 or 1, and indicates which.
    /// The other of "e0" and "e1" is an expression whose free variables are not among "boundVars[bvi..]".
    /// Ensures that the resulting "e0" and "e1" are not ConcreteSyntaxExpression's.
    /// </summary>
    static int SanitizeForBoundDiscovery<VT>(List<VT> boundVars, int bvi, BinaryExpr.ResolvedOpcode op, List<ComprehensionExpr.BoundedPool> knownBounds, ref Expression e0, ref Expression e1) where VT : IVariable {
      Contract.Requires(boundVars != null);
      Contract.Requires(0 <= bvi && bvi < boundVars.Count);
      Contract.Requires(knownBounds != null);
      Contract.Requires(knownBounds.Count == boundVars.Count);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<int>() < 2);
      Contract.Ensures(!(Contract.ValueAtReturn(out e0) is ConcreteSyntaxExpression));
      Contract.Ensures(!(Contract.ValueAtReturn(out e1) is ConcreteSyntaxExpression));

      IVariable bv = boundVars[bvi];
      e0 = e0.Resolved;
      e1 = e1.Resolved;

      // make an initial assessment of where bv is; to continue, we need bv to appear in exactly one operand
      var fv0 = FreeVariables(e0);
      var fv1 = FreeVariables(e1);
      Expression thisSide;
      Expression thatSide;
      int whereIsBv;
      if (fv0.Contains(bv)) {
        if (fv1.Contains(bv)) {
          return -1;
        }
        whereIsBv = 0;
        thisSide = e0; thatSide = e1;
      } else if (fv1.Contains(bv)) {
        whereIsBv = 1;
        thisSide = e1; thatSide = e0;
      } else {
        return -1;
      }

      // Next, clean up the side where bv is by adjusting both sides of the expression
      switch (op) {
        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.NeqCommon:
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Lt:
          // Repeatedly move additive or subtractive terms from thisSide to thatSide
          while (true) {
            var bin = thisSide as BinaryExpr;
            if (bin == null) {
              break;  // done simplifying

            } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
              // Change "A+B op C" into either "A op C-B" or "B op C-A", depending on where we find bv among A and B.
              if (!FreeVariables(bin.E1).Contains(bv)) {
                thisSide = bin.E0.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Sub, thatSide, bin.E1);
              } else if (!FreeVariables(bin.E0).Contains(bv)) {
                thisSide = bin.E1.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Sub, thatSide, bin.E0);
              } else {
                break;  // done simplifying
              }
              ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;
              thatSide.Type = bin.Type;

            } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub) {
              // Change "A-B op C" in a similar way.
              if (!FreeVariables(bin.E1).Contains(bv)) {
                // change to "A op C+B"
                thisSide = bin.E0.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Add, thatSide, bin.E1);
                ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Add;
              } else if (!FreeVariables(bin.E0).Contains(bv)) {
                // In principle, change to "-B op C-A" and then to "B dualOp A-C".  But since we don't want
                // to change "op", we instead end with "A-C op B" and switch the mapping of thisSide/thatSide
                // to e0/e1 (by inverting "whereIsBv").
                thisSide = bin.E1.Resolved;
                thatSide = new BinaryExpr(bin.tok, BinaryExpr.Opcode.Sub, bin.E0, thatSide);
                ((BinaryExpr)thatSide).ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;
                whereIsBv = 1 - whereIsBv;
              } else {
                break;  // done simplifying
              }
              thatSide.Type = bin.Type;

            } else {
              break;  // done simplifying
            }
          }
          break;

        default:
          break;
      }
      // our transformation above maintained the following invariant:
      Contract.Assert(!FreeVariables(thatSide).Contains(bv));

      // Now, see if the interesting side is simply bv itself
      if (thisSide is IdentifierExpr && ((IdentifierExpr)thisSide).Var == bv) {
        // we're cool
      } else {
        // no, the situation is more complicated than we care to understand
        return -1;
      }

      // Finally, check the bound variables of "thatSide". We allow "thatSide" to
      // depend on bound variables that are listed before "bv" (that is, a bound variable
      // "boundVars[k]" where "k < bvi"). By construction, "thatSide" does not depend
      // on "bv". Generally, for any bound variable "bj" that is listed after "bv"
      // (that is, "bj" is some "boundVars[j]" where "bvi < j"), we do not allow
      // "thatSide" to depend on "bv", but there is an important exception:
      // If
      //   *  "op" makes "thatSide" denote an integer upper bound on "bv" (or, analogously,
      //      a integer lower bound),
      //   *  "thatSide" depends on "bj",
      //   *  "thatSide" is monotonic in "bj",
      //   *  "bj" has a known integer upper bound "u",
      //   *  "u" does not depend on "bv" or any bound variable listed after "bv"
      //      (from the way we're constructing bounds, we already know that "u"
      //      does not depend on "bj" or any bound variable listed after "bj")
      // then we can substitute "u" for "bj" in "thatSide".
      // By going from right to left, we can make the rule above slightly more
      // liberal by considering a cascade of substitutions.
      var fvThatSide = FreeVariables(thatSide);
      for (int j = boundVars.Count; bvi + 1 <= --j; ) {
        if (fvThatSide.Contains(boundVars[j])) {
          if (knownBounds[j] is ComprehensionExpr.IntBoundedPool) {
            var jBounds = (ComprehensionExpr.IntBoundedPool)knownBounds[j];
            Expression u = null;
            if (op == BinaryExpr.ResolvedOpcode.Lt || op == BinaryExpr.ResolvedOpcode.Le) {
              u = whereIsBv == 0 ? jBounds.UpperBound : jBounds.LowerBound;
            } else if (op == BinaryExpr.ResolvedOpcode.Gt || op == BinaryExpr.ResolvedOpcode.Ge) {
              u = whereIsBv == 0 ? jBounds.LowerBound : jBounds.UpperBound;
            }
            if (u != null && !FreeVariables(u).Contains(bv) && IsMonotonic(u, boundVars[j], true)) {
              thatSide = Translator.Substitute(thatSide, boundVars[j], u);
              fvThatSide = FreeVariables(thatSide);
              continue;
            }
          }
          return -1;  // forget about "bv OP thatSide"
        }
      }

      // As we return, also return the adjusted sides
      if (whereIsBv == 0) {
        e0 = thisSide; e1 = thatSide;
      } else {
        e0 = thatSide; e1 = thisSide;
      }
      return whereIsBv;
    }

    /// <summary>
    /// If "position", then returns "true" if "x" occurs only positively in "expr".
    /// If "!position", then returns "true" if "x" occurs only negatively in "expr".
    /// </summary>
    public static bool IsMonotonic(Expression expr, IVariable x, bool position) {
      Contract.Requires(expr != null && expr.Type != null);
      Contract.Requires(x != null);

      if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return e.Var != x || position;
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
          return IsMonotonic(e.E0, x, position) && IsMonotonic(e.E1, x, position);
        } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub) {
          return IsMonotonic(e.E0, x, position) && IsMonotonic(e.E1, x, !position);
        }
      }
      return !FreeVariables(expr).Contains(x);
    }

    /// <summary>
    /// Returns all conjuncts of "expr" in "polarity" positions.  That is, if "polarity" is "true", then
    /// returns the conjuncts of "expr" in positive positions; else, returns the conjuncts of "expr" in
    /// negative positions.  The method considers a canonical-like form of the expression that pushes
    /// negations inwards far enough that one can determine what the result is going to be (so, almost
    /// a negation normal form).
    /// As a convenience, arithmetic inequalities are rewritten so that the negation of an arithmetic
    /// inequality is never returned and the comparisons > and >= are never returned; the negation of
    /// a common equality or disequality is rewritten analogously.
    /// Requires "expr" to be successfully resolved.
    /// Ensures that what is returned is not a ConcreteSyntaxExpression.
    /// </summary>
    static IEnumerable<Expression> NormalizedConjuncts(Expression expr, bool polarity) {
      // We consider 5 cases.  To describe them, define P(e)=Conjuncts(e,true) and N(e)=Conjuncts(e,false).
      //   *  X ==> Y    is treated as a shorthand for !X || Y, and so is described by the remaining cases
      //   *  X && Y     P(_) = P(X),P(Y)    and    N(_) = !(X && Y)
      //   *  X || Y     P(_) = (X || Y)     and    N(_) = N(X),N(Y)
      //   *  !X         P(_) = N(X)         and    N(_) = P(X)
      //   *  else       P(_) = else         and    N(_) = !else
      // So for ==>, we have:
      //   *  X ==> Y    P(_) = P(!X || Y) = (!X || Y) = (X ==> Y)
      //                 N(_) = N(!X || Y) = N(!X),N(Y) = P(X),N(Y)
      expr = expr.Resolved;

      // Binary expressions
      var b = expr as BinaryExpr;
      if (b != null) {
        bool breakDownFurther = false;
        bool p0 = polarity;
        switch (b.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
            breakDownFurther = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Or:
            breakDownFurther = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Imp:
            breakDownFurther = !polarity;
            p0 = !p0;
            break;
          default:
            break;
        }
        if (breakDownFurther) {
          foreach (var c in NormalizedConjuncts(b.E0, p0)) {
            yield return c;
          }
          foreach (var c in NormalizedConjuncts(b.E1, polarity)) {
            yield return c;
          }
          yield break;
        }
      }

      // Unary expression
      var u = expr as UnaryOpExpr;
      if (u != null && u.Op == UnaryOpExpr.Opcode.Not) {
        foreach (var c in NormalizedConjuncts(u.E, !polarity)) {
          yield return c;
        }
        yield break;
      }

      // no other case applied, so return the expression or its negation, but first clean it up a little
      b = expr as BinaryExpr;
      if (b != null) {
        BinaryExpr.Opcode newOp;
        BinaryExpr.ResolvedOpcode newROp;
        bool swapOperands;
        switch (b.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Gt:  // A > B         yield polarity ? (B < A) : (A <= B);
            newOp = polarity ? BinaryExpr.Opcode.Lt : BinaryExpr.Opcode.Le;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Lt : BinaryExpr.ResolvedOpcode.Le;
            swapOperands = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Ge:  // A >= B        yield polarity ? (B <= A) : (A < B);
            newOp = polarity ? BinaryExpr.Opcode.Le : BinaryExpr.Opcode.Lt;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Le : BinaryExpr.ResolvedOpcode.Lt;
            swapOperands = polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Le:  // A <= B        yield polarity ? (A <= B) : (B < A);
            newOp = polarity ? BinaryExpr.Opcode.Le : BinaryExpr.Opcode.Lt;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Le : BinaryExpr.ResolvedOpcode.Lt;
            swapOperands = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.Lt:  // A < B         yield polarity ? (A < B) : (B <= A);
            newOp = polarity ? BinaryExpr.Opcode.Lt : BinaryExpr.Opcode.Le;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.Lt : BinaryExpr.ResolvedOpcode.Le;
            swapOperands = !polarity;
            break;
          case BinaryExpr.ResolvedOpcode.EqCommon:  // A == B         yield polarity ? (A == B) : (A != B);
            newOp = polarity ? BinaryExpr.Opcode.Eq : BinaryExpr.Opcode.Neq;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.EqCommon : BinaryExpr.ResolvedOpcode.NeqCommon;
            swapOperands = false;
            break;
          case BinaryExpr.ResolvedOpcode.NeqCommon:  // A != B         yield polarity ? (A != B) : (A == B);
            newOp = polarity ? BinaryExpr.Opcode.Neq : BinaryExpr.Opcode.Eq;
            newROp = polarity ? BinaryExpr.ResolvedOpcode.NeqCommon : BinaryExpr.ResolvedOpcode.EqCommon;
            swapOperands = false;
            break;
          default:
            goto JUST_RETURN_IT;
        }
        if (newROp != b.ResolvedOp || swapOperands) {
          b = new BinaryExpr(b.tok, newOp, swapOperands ? b.E1 : b.E0, swapOperands ? b.E0 : b.E1);
          b.ResolvedOp = newROp;
          b.Type = Type.Bool;
          yield return b;
          yield break;
        }
      }
    JUST_RETURN_IT: ;
      if (polarity) {
        yield return expr;
      } else {
        expr = new UnaryOpExpr(expr.tok, UnaryOpExpr.Opcode.Not, expr);
        expr.Type = Type.Bool;
        yield return expr;
      }
    }

    /// <summary>
    /// Returns the set of free variables in "expr".
    /// Requires "expr" to be successfully resolved.
    /// Ensures that the set returned has no aliases.
    /// </summary>
    static ISet<IVariable> FreeVariables(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Ensures(expr.Type != null);

      if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return new HashSet<IVariable>() { e.Var };

      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution

        var s = FreeVariables(e.LogicalBody());
        foreach (var bv in e.BoundVars) {
          s.Remove(bv);
        }
        return s;

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var s = FreeVariables(e.Source);
        foreach (MatchCaseExpr mc in e.Cases) {
          var t = FreeVariables(mc.Body);
          Contract.Assert(mc.CasePatterns == null);  // CasePatterns should be converted to List<BoundVar> during resolver
          foreach (var bv in mc.Arguments) {
            t.Remove(bv);
          }
          s.UnionWith(t);
        }
        return s;

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        var s = FreeVariables(e.Term);
        if (e.Range != null) {
          s.UnionWith(FreeVariables(e.Range));
        }
        foreach (var fe in e.Reads) {
          s.UnionWith(FreeVariables(fe.E));
        }
        foreach (var bv in e.BoundVars) {
          s.Remove(bv);
        }
        return s;

      } else {
        ISet<IVariable> s = null;
        foreach (var e in expr.SubExpressions) {
          var t = FreeVariables(e);
          if (s == null) {
            s = t;
          } else {
            s.UnionWith(t);
          }
        }
        return s == null ? new HashSet<IVariable>() : s;
      }
    }

    void ResolveReceiver(Expression expr, ResolveOpts opts) {
      Contract.Requires(expr != null);
      Contract.Ensures(expr.Type != null);

      if (expr is ThisExpr && !expr.WasResolved()) {
        // Allow 'this' here, regardless of scope.AllowInstance.  The caller is responsible for
        // making sure 'this' does not really get used when it's not available.
        Contract.Assume(currentClass != null);  // this is really a precondition, in this case
        expr.Type = GetThisType(expr.tok, currentClass);
      } else {
        ResolveExpression(expr, opts);
      }
    }

    void ResolveSeqSelectExpr(SeqSelectExpr e, ResolveOpts opts) {
      Contract.Requires(e != null);
      if (e.Type != null) {
        // already resolved
        return;
      }

      ResolveExpression(e.Seq, opts);
      Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression

      if (e.SelectOne) {
        AddXConstraint(e.tok, "Indexable", e.Seq.Type, "element selection requires a sequence, array, multiset, or map (got {0})");
        ResolveExpression(e.E0, opts);
        AddXConstraint(e.E0.tok, "ContainerIndex", e.Seq.Type, e.E0.Type, "incorrect type for selection into {0} (got {1})");
        Contract.Assert(e.E1 == null);
        e.Type = new InferredTypeProxy() { KeepConstraints = true };
        AddXConstraint(e.tok, "ContainerResult", e.Seq.Type, e.Type, "type does not agree with element type of {0} (got {1})");
      } else {
        AddXConstraint(e.tok, "MultiIndexable", e.Seq.Type, "multi-selection of elements requires a sequence or array (got {0})");
        if (e.E0 != null) {
          ResolveExpression(e.E0, opts);
          AddXConstraint(e.E0.tok, "ContainerIndex", e.Seq.Type, e.E0.Type, "incorrect type for selection into {0} (got {1})");
          ConstrainSubtypeRelation(NewIntegerBasedProxy(e.tok), e.E0.Type, e.E0, "wrong number of indices for multi-selection");
        }
        if (e.E1 != null) {
          ResolveExpression(e.E1, opts);
          AddXConstraint(e.E1.tok, "ContainerIndex", e.Seq.Type, e.E1.Type, "incorrect type for selection into {0} (got {1})");
          ConstrainSubtypeRelation(NewIntegerBasedProxy(e.tok), e.E1.Type, e.E1, "wrong number of indices for multi-selection");
        }
        var resultType = new InferredTypeProxy() { KeepConstraints = true };
        e.Type = new SeqType(resultType);
        AddXConstraint(e.tok, "ContainerResult", e.Seq.Type, resultType, "type does not agree with element type of {0} (got {1})");
      }
    }

    /// <summary>
    /// Note: this method is allowed to be called even if "type" does not make sense for "op", as might be the case if
    /// resolution of the binary expression failed.  If so, an arbitrary resolved opcode is returned.
    /// </summary>
    public static BinaryExpr.ResolvedOpcode ResolveOp(BinaryExpr.Opcode op, Type operandType) {
      Contract.Requires(operandType != null);
      operandType = operandType.NormalizeExpand();
      switch (op) {
        case BinaryExpr.Opcode.Iff: return BinaryExpr.ResolvedOpcode.Iff;
        case BinaryExpr.Opcode.Imp: return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.Exp: return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.And: return BinaryExpr.ResolvedOpcode.And;
        case BinaryExpr.Opcode.Or: return BinaryExpr.ResolvedOpcode.Or;
        case BinaryExpr.Opcode.Eq:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetEq;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetEq;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.SeqEq;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapEq;
          } else {
            return BinaryExpr.ResolvedOpcode.EqCommon;
          }
        case BinaryExpr.Opcode.Neq:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetNeq;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetNeq;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.SeqNeq;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapNeq;
          } else {
            return BinaryExpr.ResolvedOpcode.NeqCommon;
          }
        case BinaryExpr.Opcode.Disjoint:
          if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetDisjoint;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapDisjoint;
          } else {
            return BinaryExpr.ResolvedOpcode.Disjoint;
          }
        case BinaryExpr.Opcode.Lt:
          if (operandType.IsIndDatatype) {
            return BinaryExpr.ResolvedOpcode.RankLt;
          } else if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.ProperSubset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.ProperMultiSubset;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.ProperPrefix;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.LtChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Lt;
          }
        case BinaryExpr.Opcode.Le:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Subset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSubset;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.Prefix;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.LeChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Le;
          }
        case BinaryExpr.Opcode.LeftShift:
          return BinaryExpr.ResolvedOpcode.LeftShift;
        case BinaryExpr.Opcode.RightShift:
          return BinaryExpr.ResolvedOpcode.RightShift;
        case BinaryExpr.Opcode.Add:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Union;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetUnion;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapUnion;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.Concat;
          } else {
            return BinaryExpr.ResolvedOpcode.Add;
          }
        case BinaryExpr.Opcode.Sub:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.SetDifference;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetDifference;
          } else {
            return BinaryExpr.ResolvedOpcode.Sub;
          }
        case BinaryExpr.Opcode.Mul:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Intersection;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSetIntersection;
          } else {
            return BinaryExpr.ResolvedOpcode.Mul;
          }
        case BinaryExpr.Opcode.Gt:
          if (operandType.IsDatatype) {
            return BinaryExpr.ResolvedOpcode.RankGt;
          } else if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.ProperSuperset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.ProperMultiSuperset;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.GtChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Gt;
          }
        case BinaryExpr.Opcode.Ge:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.Superset;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.MultiSuperset;
          } else if (operandType is CharType) {
            return BinaryExpr.ResolvedOpcode.GeChar;
          } else {
            return BinaryExpr.ResolvedOpcode.Ge;
          }
        case BinaryExpr.Opcode.In:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.InSet;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.InMultiSet;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.InMap;
          } else {
            return BinaryExpr.ResolvedOpcode.InSeq;
          }
        case BinaryExpr.Opcode.NotIn:
          if (operandType is SetType) {
            return BinaryExpr.ResolvedOpcode.NotInSet;
          } else if (operandType is MultiSetType) {
            return BinaryExpr.ResolvedOpcode.NotInMultiSet;
          } else if (operandType is MapType) {
            return BinaryExpr.ResolvedOpcode.NotInMap;
          } else {
            return BinaryExpr.ResolvedOpcode.NotInSeq;
          }
        case BinaryExpr.Opcode.Div: return BinaryExpr.ResolvedOpcode.Div;
        case BinaryExpr.Opcode.Mod: return BinaryExpr.ResolvedOpcode.Mod;
        case BinaryExpr.Opcode.BitwiseAnd: return BinaryExpr.ResolvedOpcode.BitwiseAnd;
        case BinaryExpr.Opcode.BitwiseOr: return BinaryExpr.ResolvedOpcode.BitwiseOr;
        case BinaryExpr.Opcode.BitwiseXor: return BinaryExpr.ResolvedOpcode.BitwiseXor;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
      }
    }

    /// <summary>
    /// Returns whether or not 'expr' has any subexpression that uses some feature (like a ghost or quantifier)
    /// that is allowed only in specification contexts.
    /// Requires 'expr' to be a successfully resolved expression.
    /// </summary>
    bool UsesSpecFeatures(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved

      if (expr is LiteralExpr) {
        return false;
      } else if (expr is ThisExpr) {
        return false;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        return cce.NonNull(e.Var).IsGhost;
      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        // check all NON-ghost arguments
        // note that if resolution is successful, then |e.Arguments| == |e.Ctor.Formals|
        for (int i = 0; i < e.Arguments.Count; i++) {
          if (!e.Ctor.Formals[i].IsGhost && UsesSpecFeatures(e.Arguments[i])) {
            return true;
          }
        }
        return false;
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        return e.Elements.Exists(ee => UsesSpecFeatures(ee));
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        return e.Elements.Exists(p => UsesSpecFeatures(p.A) || UsesSpecFeatures(p.B));
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr) expr;
        if (e.Member != null) {
          return cce.NonNull(e.Member).IsGhost || UsesSpecFeatures(e.Obj);
        } else {
          return false;
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        return UsesSpecFeatures(e.Seq) ||
               (e.E0 != null && UsesSpecFeatures(e.E0)) ||
               (e.E1 != null && UsesSpecFeatures(e.E1));
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        return UsesSpecFeatures(e.Array) || e.Indices.Exists(ee => UsesSpecFeatures(ee));
      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        return UsesSpecFeatures(e.Seq) ||
               UsesSpecFeatures(e.Index) ||
               UsesSpecFeatures(e.Value);
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (e.Function.IsGhost) {
          return true;
        }
        // check all NON-ghost arguments
        if (UsesSpecFeatures(e.Receiver)) {
          return true;
        }
        for (int i = 0; i < e.Function.Formals.Count; i++) {
          if (!e.Function.Formals[i].IsGhost && UsesSpecFeatures(e.Args[i])) {
            return true;
          }
        }
        return false;
      } else if (expr is ApplyExpr) {
        ApplyExpr e = (ApplyExpr)expr;
        return UsesSpecFeatures(e.Function) || e.Args.Exists(UsesSpecFeatures);
      } else if (expr is OldExpr || expr is UnchangedExpr) {
        return true;
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        var unaryOpExpr = e as UnaryOpExpr;
        if (unaryOpExpr != null && (unaryOpExpr.Op == UnaryOpExpr.Opcode.Fresh || unaryOpExpr.Op == UnaryOpExpr.Opcode.Allocated)) {
          return true;
        }
        return UsesSpecFeatures(e.E);
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        switch (e.ResolvedOp_PossiblyStillUndetermined) {
          case BinaryExpr.ResolvedOpcode.RankGt:
          case BinaryExpr.ResolvedOpcode.RankLt:
            return true;
          default:
            return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1);
        }
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            return true;
          default:
            break;
        }
        return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1) || UsesSpecFeatures(e.E2);
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          return Contract.Exists(e.RHSs, ee => UsesSpecFeatures(ee)) || UsesSpecFeatures(e.Body);
        } else {
          return true;  // let-such-that is always ghost
        }
      } else if (expr is NamedExpr) {
        return moduleInfo.IsAbstract ? false : UsesSpecFeatures(((NamedExpr)expr).Body);
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        return e.UncompilableBoundVars().Count != 0 || UsesSpecFeatures(e.LogicalBody());
      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        return !e.Finite || e.UncompilableBoundVars().Count != 0 || (e.Range != null && UsesSpecFeatures(e.Range)) || (e.Term != null && UsesSpecFeatures(e.Term));
      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        return !e.Finite || e.UncompilableBoundVars().Count != 0 || UsesSpecFeatures(e.Range) || (e.TermLeft != null && UsesSpecFeatures(e.TermLeft)) || UsesSpecFeatures(e.Term);
      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        return UsesSpecFeatures(e.Term);
      } else if (expr is WildcardExpr) {
        return false;
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return UsesSpecFeatures(e.E);
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        return UsesSpecFeatures(e.Test) || UsesSpecFeatures(e.Thn) || UsesSpecFeatures(e.Els);
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        if (UsesSpecFeatures(me.Source)) {
          return true;
        }
        return me.Cases.Exists(mc => UsesSpecFeatures(mc.Body));
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return e.ResolvedExpression != null && UsesSpecFeatures(e.ResolvedExpression);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }


    /// <summary>
    /// This method adds to "friendlyCalls" all
    ///     inductive calls                                   if !co
    ///     copredicate calls and codatatype equalities       if co
    /// that occur in positive positions and not under
    ///     universal quantification                          if !co
    ///     existential quantification.                       if co
    /// If "expr" is the
    ///     precondition of an inductive lemma                if !co
    ///     postcondition of a colemma,                       if co
    /// then the "friendlyCalls" are the subexpressions that need to be replaced in order
    /// to create the
    ///     precondition                                      if !co
    ///     postcondition                                     if co
    /// of the corresponding prefix lemma.
    /// </summary>
    void CollectFriendlyCallsInFixpointLemmaSpecification(Expression expr, bool position, ISet<Expression> friendlyCalls, bool co, FixpointLemma context) {
      Contract.Requires(expr != null);
      Contract.Requires(friendlyCalls != null);
      var visitor = new CollectFriendlyCallsInSpec_Visitor(this, friendlyCalls, co, context);
      visitor.Visit(expr, position ? CallingPosition.Positive : CallingPosition.Negative);
    }

    class CollectFriendlyCallsInSpec_Visitor : FindFriendlyCalls_Visitor
    {
      readonly ISet<Expression> friendlyCalls;
      readonly FixpointLemma Context;
      public CollectFriendlyCallsInSpec_Visitor(Resolver resolver, ISet<Expression> friendlyCalls, bool co, FixpointLemma context)
        : base(resolver, co, context.KNat)
      {
        Contract.Requires(resolver != null);
        Contract.Requires(friendlyCalls != null);
        Contract.Requires(context != null);
        this.friendlyCalls = friendlyCalls;
        this.Context = context;
      }
      protected override bool VisitOneExpr(Expression expr, ref CallingPosition cp) {
        if (cp == CallingPosition.Neither) {
          // no friendly calls in "expr"
          return false;  // don't recurse into subexpressions
        }
        if (expr is FunctionCallExpr) {
          if (cp == CallingPosition.Positive) {
            var fexp = (FunctionCallExpr)expr;
            if (IsCoContext ? fexp.Function is CoPredicate : fexp.Function is InductivePredicate) {
              if (Context.KNat != ((FixpointPredicate)fexp.Function).KNat) {
                resolver.KNatMismatchError(expr.tok, Context.Name, Context.TypeOfK, ((FixpointPredicate)fexp.Function).TypeOfK);
              } else {
                friendlyCalls.Add(fexp);
              }
            }
          }
          return false;  // don't explore subexpressions any further
        } else if (expr is BinaryExpr && IsCoContext) {
          var bin = (BinaryExpr)expr;
          if (cp == CallingPosition.Positive && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon && bin.E0.Type.IsCoDatatype) {
            friendlyCalls.Add(bin);
            return false;  // don't explore subexpressions any further
          } else if (cp == CallingPosition.Negative && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon && bin.E0.Type.IsCoDatatype) {
            friendlyCalls.Add(bin);
            return false;  // don't explore subexpressions any further
          }
        }
        return base.VisitOneExpr(expr, ref cp);
      }
    }
  }

  class CoCallResolution
  {
    readonly Function currentFunction;
    readonly bool dealsWithCodatatypes;
    public bool HasIntraClusterCallsInDestructiveContexts = false;
    public readonly List<CoCallInfo> FinalCandidates = new List<CoCallInfo>();

    public CoCallResolution(Function currentFunction, bool dealsWithCodatatypes) {
      Contract.Requires(currentFunction != null);
      this.currentFunction = currentFunction;
      this.dealsWithCodatatypes = dealsWithCodatatypes;
    }

    /// <summary>
    /// Determines which calls in "expr" can be considered to be co-calls, which co-constructor
    /// invocations host such co-calls, and which destructor operations are not allowed.
    /// Also records whether or not there are any intra-cluster calls in a destructive context.
    /// Assumes "expr" to have been successfully resolved.
    /// </summary>
    public void CheckCoCalls(Expression expr) {
      Contract.Requires(expr != null);
      CheckCoCalls(expr, 0, null, FinalCandidates);
    }

    public struct CoCallInfo
    {
      public readonly FunctionCallExpr CandidateCall;
      public readonly DatatypeValue EnclosingCoConstructor;
      public CoCallInfo(FunctionCallExpr candidateCall, DatatypeValue enclosingCoConstructor) {
        Contract.Requires(candidateCall != null);
        Contract.Requires(enclosingCoConstructor != null);
        CandidateCall = candidateCall;
        EnclosingCoConstructor = enclosingCoConstructor;
      }
    }

    /// <summary>
    /// Recursively goes through the entire "expr".  Every call within the same recursive cluster is a potential
    /// co-call.  If the call is determined not to be a co-recursive call, then its .CoCall field is filled in;
    /// if the situation deals with co-datatypes, then one of the NoBecause... values is chosen (rather
    /// than just No), so that any error message that may later be produced when trying to prove termination of the
    /// recursive call can include a note pointing out that the call was not selected to be a co-call.
    /// If the call looks like it is guarded, then it is added to the list "coCandicates", so that a later analysis
    /// can either set all of those .CoCall fields to Yes or to NoBecauseRecursiveCallsInDestructiveContext, depending
    /// on other intra-cluster calls.
    /// The "destructionLevel" indicates how many pending co-destructors the context has.  It may be infinity (int.MaxValue)
    /// if the enclosing context has no easy way of controlling the uses of "expr" (for example, if the enclosing context
    /// passes "expr" to a function or binds "expr" to a variable).  It is never negative -- excess co-constructors are
    /// not considered an asset, and any immediately enclosing co-constructor is passed in as a non-null "coContext" anyway.
    /// "coContext" is non-null if the immediate context is a co-constructor.
    /// </summary>
    void CheckCoCalls(Expression expr, int destructionLevel, DatatypeValue coContext, List<CoCallInfo> coCandidates, Function functionYouMayWishWereAbstemious = null) {
      Contract.Requires(expr != null);
      Contract.Requires(0 <= destructionLevel);
      Contract.Requires(coCandidates != null);

      expr = expr.Resolved;
      if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        if (e.Ctor.EnclosingDatatype is CoDatatypeDecl) {
          int dl = destructionLevel == int.MaxValue ? int.MaxValue : destructionLevel == 0 ? 0 : destructionLevel - 1;
          foreach (var arg in e.Arguments) {
            CheckCoCalls(arg, dl, e, coCandidates);
          }
          return;
        }
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member.EnclosingClass is CoDatatypeDecl) {
          int dl = destructionLevel == int.MaxValue ? int.MaxValue : destructionLevel + 1;
          CheckCoCalls(e.Obj, dl, coContext, coCandidates);
          return;
        }
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) {
          // Equality and disequality (for any type that may contain a co-datatype) are as destructive as can be--in essence,
          // they destruct the values indefinitely--so don't allow any co-recursive calls in the operands.
          CheckCoCalls(e.E0, int.MaxValue, null, coCandidates);
          CheckCoCalls(e.E1, int.MaxValue, null, coCandidates);
          return;
        }
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        if (e.Op == TernaryExpr.Opcode.PrefixEqOp || e.Op == TernaryExpr.Opcode.PrefixNeqOp) {
          // Prefix equality and disequality (for any type that may contain a co-datatype) are destructive.
          CheckCoCalls(e.E0, int.MaxValue, null, coCandidates);
          CheckCoCalls(e.E1, int.MaxValue, null, coCandidates);
          CheckCoCalls(e.E2, int.MaxValue, null, coCandidates);
          return;
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        CheckCoCalls(e.Source, int.MaxValue, null, coCandidates);
        foreach (var kase in e.Cases) {
          CheckCoCalls(kase.Body, destructionLevel, coContext, coCandidates);
        }
        return;
      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        CheckCoCalls(e.Test, int.MaxValue, null, coCandidates);
        CheckCoCalls(e.Thn, destructionLevel, coContext, coCandidates);
        CheckCoCalls(e.Els, destructionLevel, coContext, coCandidates);
        return;
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        // First, consider the arguments of the call, making sure that they do not include calls within the recursive cluster,
        // unless the callee is abstemious.
        var abstemious = true;
        if (!Attributes.ContainsBool(e.Function.Attributes, "abstemious", ref abstemious)) {
          abstemious = false;
        }
        Contract.Assert(e.Args.Count == e.Function.Formals.Count);
        for (var i = 0; i < e.Args.Count; i++) {
          var arg = e.Args[i];
          if (!e.Function.Formals[i].Type.IsCoDatatype) {
            CheckCoCalls(arg, int.MaxValue, null, coCandidates);
          } else if (abstemious) {
            CheckCoCalls(arg, 0, coContext, coCandidates);
          } else {
            // don't you wish the callee were abstemious
            CheckCoCalls(arg, int.MaxValue, null, coCandidates, e.Function);
          }
        }
        // Second, investigate the possibility that this call itself may be a candidate co-call
        if (e.Name != "requires" && ModuleDefinition.InSameSCC(currentFunction, e.Function)) {
          // This call goes to another function in the same recursive cluster
          if (destructionLevel != 0 && GuaranteedCoCtors(e.Function) <= destructionLevel) {
            // a potentially destructive context
            HasIntraClusterCallsInDestructiveContexts = true;  // this says we found an intra-cluster call unsuitable for recursion, if there were any co-recursive calls
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsAreNotAllowedInThisContext;
              if (functionYouMayWishWereAbstemious != null) {
                e.CoCallHint = string.Format("perhaps try declaring function '{0}' with '{{:abstemious}}'", functionYouMayWishWereAbstemious.Name);
              }
            }
          } else if (coContext == null) {
            // no immediately enclosing co-constructor
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseIsNotGuarded;
            }
          } else if (e.Function.Reads.Count != 0) {
            // this call is disqualified from being a co-call, because of side effects
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasSideEffects;
            }
          } else if (e.Function.Ens.Count != 0) {
            // this call is disqualified from being a co-call, because it has a postcondition
            // (a postcondition could be allowed, as long as it does not get to be used with
            // co-recursive calls, because that could be unsound; for example, consider
            // "ensures false")
            if (!dealsWithCodatatypes) {
              e.CoCall = FunctionCallExpr.CoCallResolution.No;
            } else {
              e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasPostcondition;
            }
          } else {
            // e.CoCall is not filled in here, but will be filled in when the list of candidates are processed
            coCandidates.Add(new CoCallInfo(e, coContext));
          }
        }
        return;
      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        CheckCoCalls(e.Body, destructionLevel, coContext, coCandidates);
        if (e.Range != null) {
          CheckCoCalls(e.Range, int.MaxValue, null, coCandidates);
        }
        foreach (var read in e.Reads) {
          CheckCoCalls(read.E, int.MaxValue, null, coCandidates);
        }
        return;
      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        foreach (var ee in Attributes.SubExpressions(e.Attributes)) {
          CheckCoCalls(ee, int.MaxValue, null, coCandidates);
        }
        if (e.Range != null) {
          CheckCoCalls(e.Range, int.MaxValue, null, coCandidates);
        }
        // allow co-calls in the term
        if (e.TermLeft != null) {
          CheckCoCalls(e.TermLeft, destructionLevel, coContext, coCandidates);
        }
        CheckCoCalls(e.Term, destructionLevel, coContext, coCandidates);
        return;
      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        // here, "coContext" is passed along (the use of "old" says this must be ghost code, so the compiler does not need to handle this case)
        CheckCoCalls(e.E, destructionLevel, coContext, coCandidates);
        return;
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var rhs in e.RHSs) {
          CheckCoCalls(rhs, int.MaxValue, null, coCandidates);
        }
        CheckCoCalls(e.Body, destructionLevel, coContext, coCandidates);
        return;
      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        CheckCoCalls(e.Function, int.MaxValue, null, coCandidates);
        foreach (var ee in e.Args) {
          CheckCoCalls(ee, destructionLevel, null, coCandidates);
        }
        return;
      }

      // Default handling:
      foreach (var ee in expr.SubExpressions) {
        CheckCoCalls(ee, destructionLevel, null, coCandidates);
      }
    }

    public static int GuaranteedCoCtors(Function function) {
      Contract.Requires(function != null);
      return function.Body != null ? GuaranteedCoCtorsAux(function.Body) : 0;
    }

    private static int GuaranteedCoCtorsAux(Expression expr) {
      Contract.Requires(expr != null);
      expr = expr.Resolved;
      if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        if (e.Ctor.EnclosingDatatype is CoDatatypeDecl) {
          var minOfArgs = int.MaxValue;  // int.MaxValue means: not yet encountered a formal whose type is a co-datatype
          Contract.Assert(e.Arguments.Count == e.Ctor.Formals.Count);
          for (var i = 0; i < e.Arguments.Count; i++) {
            if (e.Ctor.Formals[i].Type.IsCoDatatype) {
              var n = GuaranteedCoCtorsAux(e.Arguments[i]);
              minOfArgs = Math.Min(minOfArgs, n);
            }
          }
          return minOfArgs == int.MaxValue ? 1 : 1 + minOfArgs;
        }
      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        var thn = GuaranteedCoCtorsAux(e.Thn);
        var els = GuaranteedCoCtorsAux(e.Els);
        return thn < els ? thn : els;
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var min = int.MaxValue;
        foreach (var kase in e.Cases) {
          var n = GuaranteedCoCtorsAux(kase.Body);
          min = Math.Min(min, n);
        }
        return min == int.MaxValue ? 0 : min;
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return GuaranteedCoCtorsAux(e.Body);
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        if (e.Type.IsCoDatatype && e.Var is Formal) {
          // even though this is not a co-constructor, count this as 1, since that's what we would have done if it were, e.g., "Cons(s.head, s.tail)" instead of "s"
          return 1;
        }
      }
      return 0;
    }
  }

  class Scope<Thing> where Thing : class
  {
    [Rep]
    readonly List<string> names = new List<string>();  // a null means a marker
    [Rep]
    readonly List<Thing> things = new List<Thing>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(names != null);
      Contract.Invariant(things != null);
      Contract.Invariant(names.Count == things.Count);
      Contract.Invariant(-1 <= scopeSizeWhereInstancesWereDisallowed && scopeSizeWhereInstancesWereDisallowed <= names.Count);
    }

    int scopeSizeWhereInstancesWereDisallowed = -1;

    public bool AllowInstance {
      get { return scopeSizeWhereInstancesWereDisallowed == -1; }
      set {
        Contract.Requires(AllowInstance && !value);  // only allowed to change from true to false (that's all that's currently needed in Dafny); Pop is what can make the change in the other direction
        scopeSizeWhereInstancesWereDisallowed = names.Count;
      }
    }

    public void PushMarker() {
      names.Add(null);
      things.Add(null);
    }

    public void PopMarker() {
      int n = names.Count;
      while (true) {
        n--;
        if (names[n] == null) {
          break;
        }
      }
      names.RemoveRange(n, names.Count - n);
      things.RemoveRange(n, things.Count - n);
      if (names.Count < scopeSizeWhereInstancesWereDisallowed) {
        scopeSizeWhereInstancesWereDisallowed = -1;
      }
    }

    public enum PushResult { Duplicate, Shadow, Success }

    /// <summary>
    /// Pushes name-->thing association and returns "Success", if name has not already been pushed since the last marker.
    /// If name already has been pushed since the last marker, does nothing and returns "Duplicate".
    /// If the appropriate command-line option is supplied, then this method will also check if "name" shadows a previous
    /// name; if it does, then it will return "Shadow" instead of "Success".
    /// </summary>
    public PushResult Push(string name, Thing thing) {
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      if (Find(name, true) != null) {
        return PushResult.Duplicate;
      } else {
        var r = PushResult.Success;
        if (DafnyOptions.O.WarnShadowing && Find(name, false) != null) {
          r = PushResult.Shadow;
        }
        names.Add(name);
        things.Add(thing);
        return r;
      }
    }

    Thing Find(string name, bool topScopeOnly) {
      Contract.Requires(name != null);
      for (int n = names.Count; 0 <= --n; ) {
        if (names[n] == null) {
          if (topScopeOnly) {
            return null;  // not present
          }
        } else if (names[n] == name) {
          Thing t = things[n];
          Contract.Assert(t != null);
          return t;
        }
      }
      return null;  // not present
    }

    public Thing Find(string name) {
      Contract.Requires(name != null);
      return Find(name, false);
    }

    public Thing FindInCurrentScope(string name) {
      Contract.Requires(name != null);
      return Find(name, true);
    }

    public bool ContainsDecl(Thing t) {
      return things.Exists(thing => thing == t);
    }
  }
}
