#define TI_DEBUG_PRINT
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny.Plugins;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny {
  public partial class Resolver {
    public readonly BuiltIns builtIns;

    public ErrorReporter reporter;
    ModuleSignature moduleInfo = null;

    public ErrorReporter Reporter => reporter;
    public List<TypeConstraint.ErrorMsg> TypeConstraintErrorsToBeReported { get; } = new();

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

    public static FreshIdGenerator defaultTempVarIdGenerator = new FreshIdGenerator();

    public string FreshTempVarName(string prefix, ICodeContext context) {
      var gen = context is Declaration decl ? decl.IdGenerator : defaultTempVarIdGenerator;
      var freshTempVarName = gen.FreshId(prefix);
      return freshTempVarName;
    }

    interface IAmbiguousThing<Thing> {
      /// <summary>
      /// Returns a plural number of non-null Thing's
      /// </summary>
      ISet<Thing> Pool { get; }
    }

    class AmbiguousThingHelper<Thing> where Thing : class {
      public static Thing Create(ModuleDefinition m, Thing a, Thing b, IEqualityComparer<Thing> eq, out ISet<Thing> s) {
        Contract.Requires(a != null);
        Contract.Requires(b != null);
        Contract.Requires(eq != null);
        Contract.Ensures(Contract.Result<Thing>() != null ||
                         Contract.ValueAtReturn(out s) != null || 2 <= Contract.ValueAtReturn(out s).Count);
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

    public class AmbiguousTopLevelDecl : TopLevelDecl, IAmbiguousThing<TopLevelDecl> // only used with "classes"
    {
      public static TopLevelDecl Create(ModuleDefinition m, TopLevelDecl a, TopLevelDecl b) {
        ISet<TopLevelDecl> s;
        var t = AmbiguousThingHelper<TopLevelDecl>.Create(m, a, b, new Eq(), out s);
        return t ?? new AmbiguousTopLevelDecl(m, AmbiguousThingHelper<TopLevelDecl>.Name(s, tld => tld.Name), s);
      }

      class Eq : IEqualityComparer<TopLevelDecl> {
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

      public override string WhatKind {
        get { return Pool.First().WhatKind; }
      }

      readonly ISet<TopLevelDecl> Pool = new HashSet<TopLevelDecl>();

      ISet<TopLevelDecl> IAmbiguousThing<TopLevelDecl>.Pool {
        get { return Pool; }
      }

      private AmbiguousTopLevelDecl(ModuleDefinition m, string name, ISet<TopLevelDecl> pool)
        : base(pool.First().RangeToken, new Name(pool.First().RangeToken, name), m, new List<TypeParameter>(), null, false) {
        Contract.Requires(name != null);
        Contract.Requires(pool != null && 2 <= pool.Count);
        Pool = pool;
      }

      public string ModuleNames() {
        return AmbiguousThingHelper<TopLevelDecl>.ModuleNames(this, d => d.EnclosingModuleDefinition.Name);
      }
    }

    class AmbiguousMemberDecl : MemberDecl, IAmbiguousThing<MemberDecl> // only used with "classes"
    {
      public static MemberDecl Create(ModuleDefinition m, MemberDecl a, MemberDecl b) {
        ISet<MemberDecl> s;
        var t = AmbiguousThingHelper<MemberDecl>.Create(m, a, b, new Eq(), out s);
        return t ?? new AmbiguousMemberDecl(m, AmbiguousThingHelper<MemberDecl>.Name(s, member => member.Name), s);
      }

      class Eq : IEqualityComparer<MemberDecl> {
        public bool Equals(MemberDecl d0, MemberDecl d1) {
          return d0 == d1;
        }

        public int GetHashCode(MemberDecl d) {
          return d.GetHashCode();
        }
      }

      public override string WhatKind {
        get { return Pool.First().WhatKind; }
      }

      readonly ISet<MemberDecl> Pool = new HashSet<MemberDecl>();

      ISet<MemberDecl> IAmbiguousThing<MemberDecl>.Pool {
        get { return Pool; }
      }

      private AmbiguousMemberDecl(ModuleDefinition m, string name, ISet<MemberDecl> pool)
        : base(pool.First().RangeToken, new Name(pool.First().RangeToken, name), true, pool.First().IsGhost, null, false) {
        Contract.Requires(name != null);
        Contract.Requires(pool != null && 2 <= pool.Count);
        Pool = pool;
      }

      public string ModuleNames() {
        return AmbiguousThingHelper<MemberDecl>.ModuleNames(this, d => d.EnclosingClass.EnclosingModuleDefinition.Name);
      }
    }

    readonly HashSet<RevealableTypeDecl> revealableTypes = new HashSet<RevealableTypeDecl>();
    //types that have been seen by the resolver - used for constraining type inference during exports

    readonly Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> classMembers =
      new Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>>();

    enum ValuetypeVariety {
      Bool = 0,
      Int,
      Real,
      BigOrdinal,
      Bitvector,
      Map,
      IMap,
      None
    } // note, these are ordered, so they can be used as indices into valuetypeDecls

    readonly ValuetypeDecl[] valuetypeDecls;
    private Dictionary<TypeParameter, Type> SelfTypeSubstitution;
    readonly Graph<ModuleDecl> dependencies = new Graph<ModuleDecl>();
    private ModuleSignature systemNameInfo = null;
    private bool useCompileSignatures = false;

    private List<IRewriter> rewriters;
    private RefinementTransformer refinementTransformer;

    public Resolver() {
    }

    public Resolver(Program prog) {
      Contract.Requires(prog != null);

      builtIns = prog.BuiltIns;
      reporter = prog.Reporter;

      // Map#Items relies on the two destructors for 2-tuples
      builtIns.TupleType(Token.NoToken, 2, true);
      // Several methods and fields rely on 1-argument arrow types
      builtIns.CreateArrowTypeDecl(1);

      valuetypeDecls = new ValuetypeDecl[] {
        new ValuetypeDecl("bool", builtIns.SystemModule, 0, t => t.IsBoolType, typeArgs => Type.Bool),
        new ValuetypeDecl("int", builtIns.SystemModule, 0, t => t.IsNumericBased(Type.NumericPersuasion.Int), typeArgs => Type.Int),
        new ValuetypeDecl("real", builtIns.SystemModule, 0, t => t.IsNumericBased(Type.NumericPersuasion.Real), typeArgs => Type.Real),
        new ValuetypeDecl("ORDINAL", builtIns.SystemModule, 0, t => t.IsBigOrdinalType, typeArgs => Type.BigOrdinal),
        new ValuetypeDecl("_bv", builtIns.SystemModule, 0, t => t.IsBitVectorType, null), // "_bv" represents a family of classes, so no typeTester or type creator is supplied
        new ValuetypeDecl("map", builtIns.SystemModule, 2, t => t.IsMapType, typeArgs => new MapType(true, typeArgs[0], typeArgs[1])),
        new ValuetypeDecl("imap", builtIns.SystemModule, 2, t => t.IsIMapType, typeArgs => new MapType(false, typeArgs[0], typeArgs[1]))
      };
      builtIns.SystemModule.TopLevelDecls.AddRange(valuetypeDecls);
      // Resolution error handling relies on being able to get to the 0-tuple declaration
      builtIns.TupleType(Token.NoToken, 0, true);

      // Populate the members of the basic types
      var floor = new SpecialField(RangeToken.NoToken, "Floor", SpecialField.ID.Floor, null, false, false, false, Type.Int, null);
      floor.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Real].Members.Add(floor.Name, floor);

      var isLimit = new SpecialField(RangeToken.NoToken, "IsLimit", SpecialField.ID.IsLimit, null, false, false, false,
        Type.Bool, null);
      isLimit.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isLimit.Name, isLimit);

      var isSucc = new SpecialField(RangeToken.NoToken, "IsSucc", SpecialField.ID.IsSucc, null, false, false, false,
        Type.Bool, null);
      isSucc.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isSucc.Name, isSucc);

      var limitOffset = new SpecialField(RangeToken.NoToken, "Offset", SpecialField.ID.Offset, null, false, false, false,
        Type.Int, null);
      limitOffset.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(limitOffset.Name, limitOffset);
      builtIns.ORDINAL_Offset = limitOffset;

      var isNat = new SpecialField(RangeToken.NoToken, "IsNat", SpecialField.ID.IsNat, null, false, false, false, Type.Bool, null);
      isNat.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isNat.Name, isNat);

      // Add "Keys", "Values", and "Items" to map, imap
      foreach (var typeVariety in new[] { ValuetypeVariety.Map, ValuetypeVariety.IMap }) {
        var vtd = valuetypeDecls[(int)typeVariety];
        var isFinite = typeVariety == ValuetypeVariety.Map;

        var r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[0]));
        var keys = new SpecialField(RangeToken.NoToken, "Keys", SpecialField.ID.Keys, null, false, false, false, r, null);

        r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[1]));
        var values = new SpecialField(RangeToken.NoToken, "Values", SpecialField.ID.Values, null, false, false, false, r, null);

        var gt = vtd.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
        var dt = builtIns.TupleType(Token.NoToken, 2, true);
        var tupleType = new UserDefinedType(Token.NoToken, dt.Name, dt, gt);
        r = new SetType(isFinite, tupleType);
        var items = new SpecialField(RangeToken.NoToken, "Items", SpecialField.ID.Items, null, false, false, false, r, null);

        foreach (var memb in new[] { keys, values, items }) {
          memb.EnclosingClass = vtd;
          memb.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
          vtd.Members.Add(memb.Name, memb);
        }
      }

      // The result type of the following bitvector methods is the type of the bitvector itself. However, we're representing all bitvector types as
      // a family of types rolled up in one ValuetypeDecl. Therefore, we use the special SelfType as the result type.
      List<Formal> formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, null, false) };
      var rotateLeft = new SpecialFunction(RangeToken.NoToken, "RotateLeft", prog.BuiltIns.SystemModule, false, false,
        new List<TypeParameter>(), formals, new SelfType(),
        new List<AttributedExpression>(), new List<FrameExpression>(), new List<AttributedExpression>(),
        new Specification<Expression>(new List<Expression>(), null), null, null, null);
      rotateLeft.EnclosingClass = valuetypeDecls[(int)ValuetypeVariety.Bitvector];
      rotateLeft.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Bitvector].Members.Add(rotateLeft.Name, rotateLeft);

      formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, null, false) };
      var rotateRight = new SpecialFunction(RangeToken.NoToken, "RotateRight", prog.BuiltIns.SystemModule, false, false,
        new List<TypeParameter>(), formals, new SelfType(),
        new List<AttributedExpression>(), new List<FrameExpression>(), new List<AttributedExpression>(),
        new Specification<Expression>(new List<Expression>(), null), null, null, null);
      rotateRight.EnclosingClass = valuetypeDecls[(int)ValuetypeVariety.Bitvector];
      rotateRight.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Bitvector].Members.Add(rotateRight.Name, rotateRight);
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(builtIns != null);
      Contract.Invariant(cce.NonNullElements(dependencies.GetVertices()));
      Contract.Invariant(cce.NonNullDictionaryAndValues(classMembers) && Contract.ForAll(classMembers.Values, v => cce.NonNullDictionaryAndValues(v)));
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
        var compileIt = true;
        Attributes.ContainsBool(m.Attributes, "compile", ref compileIt);
        if (m.IsAbstract || !compileIt) {
          // the purpose of an abstract module is to skip compilation
          continue;
        }
        string compileName = m.CompileName;
        ModuleDefinition priorModDef;
        if (compileNameMap.TryGetValue(compileName, out priorModDef)) {
          reporter.Error(MessageSource.Resolver, m.tok,
            "modules '{0}' and '{1}' both have CompileName '{2}'",
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
      var origErrorCount = reporter.ErrorCount; //TODO: This is used further below, but not in the >0 comparisons in the next few lines. Is that right?
      var bindings = new ModuleBindings(null);
      var b = BindModuleNames(prog.DefaultModuleDef, bindings);
      bindings.BindName(prog.DefaultModule.Name, prog.DefaultModule, b);
      if (reporter.ErrorCount > 0) {
        return;
      } // if there were errors, then the implict ModuleBindings data structure invariant

      // is violated, so Processing dependencies will not succeed.
      ProcessDependencies(prog.DefaultModule, b, dependencies);
      // check for cycles in the import graph
      foreach (var cycle in dependencies.AllCycles()) {
        ReportCycleError(cycle, m => m.tok,
          m => (m is AliasModuleDecl ? "import " : "module ") + m.Name,
          "module definition contains a cycle (note: parent modules implicitly depend on submodules)");
      }

      if (reporter.ErrorCount > 0) {
        return;
      } // give up on trying to resolve anything else

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

      if (DafnyOptions.O.AuditProgram) {
        rewriters.Add(new Auditor.Auditor(reporter));
      }

      refinementTransformer = new RefinementTransformer(prog);
      rewriters.Add(refinementTransformer);
      rewriters.Add(new AutoContractsRewriter(reporter, builtIns));
      rewriters.Add(new OpaqueMemberRewriter(this.reporter));
      rewriters.Add(new AutoReqFunctionRewriter(this.reporter));
      rewriters.Add(new TimeLimitRewriter(reporter));
      rewriters.Add(new ForallStmtRewriter(reporter));
      rewriters.Add(new ProvideRevealAllRewriter(this.reporter));
      rewriters.Add(new MatchFlattener(this.reporter, Resolver.defaultTempVarIdGenerator));

      if (DafnyOptions.O.AutoTriggers) {
        rewriters.Add(new QuantifierSplittingRewriter(reporter));
        rewriters.Add(new TriggerGeneratingRewriter(reporter));
      }

      if (DafnyOptions.O.TestContracts != DafnyOptions.ContractTestingMode.None) {
        rewriters.Add(new ExpectContracts(reporter));
      }

      if (DafnyOptions.O.RunAllTests) {
        rewriters.Add(new RunAllTestsMainMethod(reporter));
      }

      rewriters.Add(new InductionRewriter(reporter));
      rewriters.Add(new PrintEffectEnforcement(reporter));
      rewriters.Add(new BitvectorOptimization(reporter));

      if (DafnyOptions.O.DisallowConstructorCaseWithoutParentheses) {
        rewriters.Add(new ConstructorWarning(reporter));
      }
      rewriters.Add(new UselessOldLinter(reporter));
      rewriters.Add(new PrecedenceLinter(reporter));

      foreach (var plugin in DafnyOptions.O.Plugins) {
        rewriters.AddRange(plugin.GetRewriters(reporter));
      }

      systemNameInfo = RegisterTopLevelDecls(prog.BuiltIns.SystemModule, false);
      prog.CompileModules.Add(prog.BuiltIns.SystemModule);
      RevealAllInScope(prog.BuiltIns.SystemModule.TopLevelDecls, systemNameInfo.VisibilityScope);
      ResolveValuetypeDecls();
      // The SystemModule is constructed with all its members already being resolved. Except for
      // the non-null type corresponding to class types.  They are resolved here:
      var systemModuleClassesWithNonNullTypes =
        prog.BuiltIns.SystemModule.TopLevelDecls.Where(d => (d as ClassDecl)?.NonNullTypeDecl != null).ToList();
      foreach (var cl in systemModuleClassesWithNonNullTypes) {
        var d = ((ClassDecl)cl).NonNullTypeDecl;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        ResolveType(d.tok, d.Rhs, d, ResolveTypeOptionEnum.AllowPrefix, d.TypeArgs);
        allTypeParameters.PopMarker();
      }
      ResolveTopLevelDecls_Core(ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(systemModuleClassesWithNonNullTypes).ToList(),
        new Graph<IndDatatypeDecl>(), new Graph<CoDatatypeDecl>());

      foreach (var rewriter in rewriters) {
        rewriter.PreResolve(prog);
      }

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

          var errorCount = reporter.ErrorCount;
          if (m.RefinementQId != null) {
            ModuleDecl md = ResolveModuleQualifiedId(m.RefinementQId.Root, m.RefinementQId, reporter);
            m.RefinementQId.Set(md); // If module is not found, md is null and an error message has been emitted
          }

          foreach (var rewriter in rewriters) {
            rewriter.PreResolve(m);
          }

          literalDecl.Signature = RegisterTopLevelDecls(m, true);
          literalDecl.Signature.Refines = refinementTransformer.RefinedSig;

          var sig = literalDecl.Signature;
          // set up environment
          var preResolveErrorCount = reporter.ErrorCount;

          ResolveModuleExport(literalDecl, sig);
          var good = ResolveModuleDefinition(m, sig);

          if (good && reporter.ErrorCount == preResolveErrorCount) {
            // Check that the module export gives a self-contained view of the module.
            CheckModuleExportConsistency(m);
          }

          var tempVis = new VisibilityScope();
          tempVis.Augment(sig.VisibilityScope);
          tempVis.Augment(systemNameInfo.VisibilityScope);
          Type.PushScope(tempVis);

          prog.ModuleSigs[m] = sig;

          foreach (var rewriter in rewriters) {
            if (!good || reporter.ErrorCount != preResolveErrorCount) {
              break;
            }
            rewriter.PostResolveIntermediate(m);
          }
          if (good && reporter.ErrorCount == errorCount) {
            m.SuccessfullyResolved = true;
          }
          Type.PopScope(tempVis);

          if (reporter.ErrorCount == errorCount && !m.IsAbstract) {
            // compilation should only proceed if everything is good, including the signature (which preResolveErrorCount does not include);
            CompilationCloner cloner = new CompilationCloner(compilationModuleClones);
            var nw = cloner.CloneModuleDefinition(m, new Name(m.NameNode.RangeToken, m.CompileName + "_Compile"));
            compilationModuleClones.Add(m, nw);
            var oldErrorsOnly = reporter.ErrorsOnly;
            reporter.ErrorsOnly = true; // turn off warning reporting for the clone
            // Next, compute the compile signature
            Contract.Assert(!useCompileSignatures);
            useCompileSignatures = true; // set Resolver-global flag to indicate that Signatures should be followed to their CompiledSignature
            Type.DisableScopes();
            var compileSig = RegisterTopLevelDecls(nw, true);
            compileSig.Refines = refinementTransformer.RefinedSig;
            sig.CompileSignature = compileSig;
            foreach (var exportDecl in sig.ExportSets.Values) {
              exportDecl.Signature.CompileSignature = cloner.CloneModuleSignature(exportDecl.Signature, compileSig);
            }
            // Now we're ready to resolve the cloned module definition, using the compile signature

            ResolveModuleDefinition(nw, compileSig);

            foreach (var rewriter in rewriters) {
              rewriter.PostCompileCloneAndResolve(nw);
            }

            prog.CompileModules.Add(nw);
            useCompileSignatures = false; // reset the flag
            Type.EnableScopes();
            reporter.ErrorsOnly = oldErrorsOnly;
          }
        } else if (decl is AliasModuleDecl alias) {
          // resolve the path
          ModuleSignature p;
          if (ResolveExport(alias, alias.EnclosingModuleDefinition, alias.TargetQId, alias.Exports, out p, reporter)) {
            if (alias.Signature == null) {
              alias.Signature = p;
            }
          } else {
            alias.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
          }
        } else if (decl is AbstractModuleDecl abs) {
          ModuleSignature p;
          if (ResolveExport(abs, abs.EnclosingModuleDefinition, abs.QId, abs.Exports, out p, reporter)) {
            abs.OriginalSignature = p;
            abs.Signature = MakeAbstractSignature(p, abs.FullSanitizedName, abs.Height, prog.ModuleSigs, compilationModuleClones);
          } else {
            abs.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
          }
        } else if (decl is ModuleExportDecl) {
          ((ModuleExportDecl)decl).SetupDefaultSignature();

          Contract.Assert(decl.Signature != null);
          Contract.Assert(decl.Signature.VisibilityScope != null);

        } else {
          Contract.Assert(false); // Unknown kind of ModuleDecl
        }

        Contract.Assert(decl.Signature != null);
      }

      if (reporter.ErrorCount != origErrorCount) {
        // do nothing else
        return;
      }

      // compute IsRecursive bit for mutually recursive functions and methods
      foreach (var module in prog.Modules()) {
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls)) {
          if (clbl is Function) {
            var fn = (Function)clbl;
            if (!fn.IsRecursive) { // note, self-recursion has already been determined
              int n = module.CallGraph.GetSCCSize(fn);
              if (2 <= n) {
                // the function is mutually recursive (note, the SCC does not determine self recursion)
                fn.IsRecursive = true;
              }
            }
            if (fn.IsRecursive && fn is ExtremePredicate) {
              // this means the corresponding prefix predicate is also recursive
              var prefixPred = ((ExtremePredicate)fn).PrefixPredicate;
              if (prefixPred != null) {
                prefixPred.IsRecursive = true;
              }
            }
          } else {
            var m = (Method)clbl;
            if (!m.IsRecursive) {
              // note, self-recursion has already been determined
              int n = module.CallGraph.GetSCCSize(m);
              if (2 <= n) {
                // the function is mutually recursive (note, the SCC does not determine self recursion)
              }
            }
          }
        }

        foreach (var rewriter in rewriters) {
          rewriter.PostCyclicityResolve(module);
        }
      }

      // fill in default decreases clauses:  for functions and methods, and for loops
      new InferDecreasesClause(this).FillInDefaultDecreasesClauses(prog);
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

      foreach (var module in prog.Modules()) {
        foreach (var rewriter in rewriters) {
          rewriter.PostDecreasesResolve(module);
        }
      }

      // fill in other additional information
      foreach (var module in prog.Modules()) {
        foreach (var clbl in ModuleDefinition.AllItersAndCallables(module.TopLevelDecls)) {
          Statement body = null;
          if (clbl is ExtremeLemma) {
            body = ((ExtremeLemma)clbl).PrefixLemma.Body;
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

      foreach (var module in prog.Modules()) {
        foreach (var rewriter in rewriters) {
          rewriter.PostResolve(module);
        }
      }

      foreach (var rewriter in rewriters) {
        rewriter.PostResolve(prog);
      }
    }



    private void ResolveValuetypeDecls() {
      moduleInfo = systemNameInfo;
      foreach (var valueTypeDecl in valuetypeDecls) {
        foreach (var kv in valueTypeDecl.Members) {
          if (kv.Value is Function function) {
            ResolveFunctionSignature(function);
            CallGraphBuilder.VisitFunction(function, reporter);
          } else if (kv.Value is Method method) {
            ResolveMethodSignature(method);
            CallGraphBuilder.VisitMethod(method, reporter);
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
    private bool ResolveModuleDefinition(ModuleDefinition m, ModuleSignature sig, bool isAnExport = false) {
      Contract.Requires(AllTypeConstraints.Count == 0);
      Contract.Ensures(AllTypeConstraints.Count == 0);

      sig.VisibilityScope.Augment(systemNameInfo.VisibilityScope);
      // make sure all imported modules were successfully resolved
      foreach (var d in m.TopLevelDecls) {
        if (d is AliasModuleDecl || d is AbstractModuleDecl) {
          ModuleSignature importSig;
          if (d is AliasModuleDecl) {
            var alias = (AliasModuleDecl)d;
            importSig = alias.TargetQId.Root != null ? alias.TargetQId.Root.Signature : alias.Signature;
          } else {
            importSig = ((AbstractModuleDecl)d).OriginalSignature;
          }

          if (importSig.ModuleDef == null || !importSig.ModuleDef.SuccessfullyResolved) {
            if (!m.IsEssentiallyEmptyModuleBody()) {
              // say something only if this will cause any testing to be omitted
              reporter.Error(MessageSource.Resolver, d,
                "not resolving module '{0}' because there were errors in resolving its import '{1}'", m.Name, d.Name);
            }

            return false;
          }
        } else if (d is LiteralModuleDecl) {
          var nested = (LiteralModuleDecl)d;
          if (!nested.ModuleDef.SuccessfullyResolved) {
            if (!m.IsEssentiallyEmptyModuleBody()) {
              // say something only if this will cause any testing to be omitted
              reporter.Error(MessageSource.Resolver, nested,
                "not resolving module '{0}' because there were errors in resolving its nested module '{1}'", m.Name,
                nested.Name);
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
      var allDeclarations = ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(m.TopLevelDecls).ToList();
      int prevErrorCount = reporter.Count(ErrorLevel.Error);
      ResolveTopLevelDecls_Signatures(m, sig, allDeclarations, datatypeDependencies, codatatypeDependencies);
      Contract.Assert(AllTypeConstraints.Count == 0); // signature resolution does not add any type constraints

      scope.PushMarker();
      scope.AllowInstance = false;
      ResolveAttributes(m, new ResolutionContext(new NoContext(m.EnclosingModule), false), true); // Must follow ResolveTopLevelDecls_Signatures, in case attributes refer to members
      scope.PopMarker();

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        ResolveTopLevelDecls_Core(allDeclarations, datatypeDependencies, codatatypeDependencies, isAnExport);
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
          foreach (IToken s in d.Extends) {
            ModuleExportDecl extend;
            if (sig.ExportSets.TryGetValue(s.val, out extend)) {
              d.ExtendDecls.Add(extend);
              exportDependencies.AddEdge(d, extend);
            } else {
              reporter.Error(MessageSource.Resolver, s, s.val + " must be an export of " + m.Name + " to be extended");
            }
          }
        }
      }

      // detect cycles in the extend
      var cycleError = false;
      foreach (var cycle in exportDependencies.AllCycles()) {
        ReportCycleError(cycle, m => m.tok, m => m.Name, "module export contains a cycle");
        cycleError = true;
      }

      if (cycleError) {
        return;
      } // give up on trying to resolve anything else

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
          if (classMembers.TryGetValue((ClassDecl)defaultClass, out members) &&
              members.TryGetValue(d.Name, out member)) {
            reporter.Warning(MessageSource.Resolver, ErrorID.None, d.tok,
              "note, this export set is empty (did you perhaps forget the 'provides' or 'reveals' keyword?)");
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
            if (!sig.TopLevels.TryGetValue(export.ClassId, out cldecl)) {
              reporter.Error(MessageSource.Resolver, export.ClassIdTok, "'{0}' is not a top-level type declaration",
                export.ClassId);
              continue;
            }

            if (cldecl is ClassDecl && ((ClassDecl)cldecl).NonNullTypeDecl != null) {
              // cldecl is a possibly-null type (syntactically given with a question mark at the end)
              reporter.Error(MessageSource.Resolver, export.ClassIdTok, "'{0}' is not a type that can declare members",
                export.ClassId);
              continue;
            }

            if (cldecl is NonNullTypeDecl) {
              // cldecl was given syntactically like the name of a class, but here it's referring to the corresponding non-null subset type
              cldecl = cldecl.ViewAsClass;
            }

            var mt = cldecl as TopLevelDeclWithMembers;
            if (mt == null) {
              reporter.Error(MessageSource.Resolver, export.ClassIdTok, "'{0}' is not a type that can declare members",
                export.ClassId);
              continue;
            }

            var lmem = mt.Members.FirstOrDefault(l => l.Name == export.Id);
            if (lmem == null) {
              reporter.Error(MessageSource.Resolver, export.Tok, "No member '{0}' found in type '{1}'", export.Id,
                export.ClassId);
              continue;
            }

            decl = lmem;
          } else if (sig.TopLevels.TryGetValue(name, out tdecl)) {
            if (tdecl is ClassDecl && ((ClassDecl)tdecl).NonNullTypeDecl != null) {
              // cldecl is a possibly-null type (syntactically given with a question mark at the end)
              var nn = ((ClassDecl)tdecl).NonNullTypeDecl;
              Contract.Assert(nn != null);
              reporter.Error(MessageSource.Resolver, export.Tok,
                export.Opaque
                  ? "Type '{1}' can only be revealed, not provided"
                  : "Types '{0}' and '{1}' are exported together, which is accomplished by revealing the name '{0}'",
                nn.Name, name);
              continue;
            }

            // Member of the enclosing module
            decl = tdecl;
          } else if (sig.StaticMembers.TryGetValue(name, out member)) {
            decl = member;
          } else if (sig.ExportSets.ContainsKey(name)) {
            reporter.Error(MessageSource.Resolver, export.Tok,
              "'{0}' is an export set and cannot be provided/revealed by another export set (did you intend to list it in an \"extends\"?)",
              name);
            continue;
          } else {
            reporter.Error(MessageSource.Resolver, export.Tok, "'{0}' must be a member of '{1}' to be exported", name,
              m.Name);
            continue;
          }

          if (!decl.CanBeExported()) {
            reporter.Error(MessageSource.Resolver, export.Tok, "'{0}' is not a valid export of '{1}'", name, m.Name);
            continue;
          }

          if (!export.Opaque && !decl.CanBeRevealed()) {
            reporter.Error(MessageSource.Resolver, export.Tok,
              "'{0}' cannot be revealed in an export. Use \"provides\" instead.", name);
            continue;
          }

          export.Decl = decl;
          if (decl is NonNullTypeDecl nntd) {
            nntd.AddVisibilityScope(d.ThisScope, export.Opaque);
            if (!export.Opaque) {
              nntd.Class.AddVisibilityScope(d.ThisScope, export.Opaque);
              // add the anonymous constructor, if any
              var anonymousConstructor = nntd.Class.Members.Find(mdecl => mdecl.Name == "_ctor");
              if (anonymousConstructor != null) {
                anonymousConstructor.AddVisibilityScope(d.ThisScope, false);
              }
            }
          } else {
            decl.AddVisibilityScope(d.ThisScope, export.Opaque);
          }
        }
      }

      foreach (ModuleExportDecl decl in sortedExportDecls) {
        if (decl.IsDefault) {
          if (defaultExport == null) {
            defaultExport = decl;
          } else {
            reporter.Error(MessageSource.Resolver, m.tok, "more than one default export set declared in module {0}",
              m.Name);
          }
        }

        // fill in export signature
        ModuleSignature signature = decl.Signature;
        if (signature != null) {
          signature.ModuleDef = m;
        }

        foreach (var top in sig.TopLevels) {
          if (!top.Value.CanBeExported() || !top.Value.IsVisibleInScope(signature.VisibilityScope)) {
            continue;
          }

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
        }

        foreach (var mem in sig.StaticMembers.Where(t =>
          t.Value.IsVisibleInScope(signature.VisibilityScope) && t.Value.CanBeExported())) {
          if (!signature.StaticMembers.ContainsKey(mem.Key)) {
            signature.StaticMembers.Add(mem.Key, (MemberDecl)mem.Value);
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

      var exported = new HashSet<Tuple<Declaration, bool>>();

      //some decls may not be set due to resolution errors
      foreach (var e in sortedExportDecls.SelectMany(e => e.Exports).Where(e => e.Decl != null)) {
        var decl = e.Decl;
        exported.Add(new Tuple<Declaration, bool>(decl, e.Opaque));
        if (!e.Opaque && decl.CanBeRevealed()) {
          exported.Add(new Tuple<Declaration, bool>(decl, true));
          if (decl is NonNullTypeDecl nntd) {
            exported.Add(new Tuple<Declaration, bool>(nntd.Class, true));
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

        VisibilityScope newscope = new VisibilityScope(e.Item1.Name);

        foreach (var rt in declScopes) {
          if (!rt.Value.HasValue) {
            continue;
          }

          rt.Key.AsTopLevelDecl.AddVisibilityScope(newscope, rt.Value.Value);
        }
      }
    }

    //check for export consistency by resolving internal modules
    //this should be effect-free, as it only operates on clones
    private void CheckModuleExportConsistency(ModuleDefinition m) {
      var oldModuleInfo = moduleInfo;
      foreach (var exportDecl in m.TopLevelDecls.OfType<ModuleExportDecl>()) {

        var prevErrors = reporter.Count(ErrorLevel.Error);

        foreach (var export in exportDecl.Exports) {
          if (export.Decl is MemberDecl member) {
            // For classes and traits, the visibility test is performed on the corresponding non-null type
            var enclosingType = member.EnclosingClass is ClassDecl cl && cl.NonNullTypeDecl != null
              ? cl.NonNullTypeDecl
              : member.EnclosingClass;
            if (!enclosingType.IsVisibleInScope(exportDecl.Signature.VisibilityScope)) {
              reporter.Error(MessageSource.Resolver, export.Tok,
                "Cannot export type member '{0}' without providing its enclosing {1} '{2}'", member.Name,
                member.EnclosingClass.WhatKind, member.EnclosingClass.Name);
            } else if (member is Constructor &&
                       !member.EnclosingClass.IsRevealedInScope(exportDecl.Signature.VisibilityScope)) {
              reporter.Error(MessageSource.Resolver, export.Tok,
                "Cannot export constructor '{0}' without revealing its enclosing {1} '{2}'", member.Name,
                member.EnclosingClass.WhatKind, member.EnclosingClass.Name);
            } else if (member is Field && !(member is ConstantField) &&
                       !member.EnclosingClass.IsRevealedInScope(exportDecl.Signature.VisibilityScope)) {
              reporter.Error(MessageSource.Resolver, export.Tok,
                "Cannot export mutable field '{0}' without revealing its enclosing {1} '{2}'", member.Name,
                member.EnclosingClass.WhatKind, member.EnclosingClass.Name);
            }
          }
        }

        var scope = exportDecl.Signature.VisibilityScope;
        Cloner cloner = new ScopeCloner(scope);
        var exportView = cloner.CloneModuleDefinition(m, m.NameNode);
        if (DafnyOptions.O.DafnyPrintExportedViews.Contains(exportDecl.FullName)) {
          var wr = Console.Out;
          wr.WriteLine("/* ===== export set {0}", exportDecl.FullName);
          var pr = new Printer(wr);
          pr.PrintTopLevelDecls(exportView.TopLevelDecls, 0, null, null);
          wr.WriteLine("*/");
        }

        if (reporter.Count(ErrorLevel.Error) != prevErrors) {
          continue;
        }

        reporter = new ErrorReporterWrapper(reporter,
          String.Format("Raised while checking export set {0}: ", exportDecl.Name));
        var testSig = RegisterTopLevelDecls(exportView, true);
        //testSig.Refines = refinementTransformer.RefinedSig;
        ResolveModuleDefinition(exportView, testSig, true);
        var wasError = reporter.Count(ErrorLevel.Error) > 0;
        reporter = ((ErrorReporterWrapper)reporter).WrappedReporter;

        if (wasError) {
          reporter.Error(MessageSource.Resolver, exportDecl.tok, "This export set is not consistent: {0}", exportDecl.Name);
        }
      }

      moduleInfo = oldModuleInfo;
    }

    public class ModuleBindings {
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
        } else {
          return false;
        }
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

      // First, register all literal modules, and transferring their prefix-named modules downwards
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
        }
      }

      // Next, add new modules for any remaining entries in "prefixNames".
      foreach (var entry in prefixNames) {
        var name = entry.Key;
        var prefixNamedModules = entry.Value;
        var tok = prefixNamedModules.First().Item1[0];
        var modDef = new ModuleDefinition(tok.ToRange(), new Name(tok.ToRange(), name), new List<IToken>(), false, false, null, moduleDecl, null, false,
          true, true);
        // Every module is expected to have a default class, so we create and add one now
        var defaultClass = new DefaultClassDecl(modDef, new List<MemberDecl>());
        modDef.TopLevelDecls.Add(defaultClass);
        // Add the new module to the top-level declarations of its parent and then bind its names as usual
        var subdecl = new LiteralModuleDecl(modDef, moduleDecl);
        moduleDecl.TopLevelDecls.Add(subdecl);
        BindModuleName_LiteralModuleDecl(subdecl, prefixNamedModules.ConvertAll(ShortenPrefix), bindings);
      }

      // Finally, go through import declarations (that is, AbstractModuleDecl's and AliasModuleDecl's).
      foreach (var tld in moduleDecl.TopLevelDecls) {
        if (tld is AbstractModuleDecl || tld is AliasModuleDecl) {
          var subdecl = (ModuleDecl)tld;
          if (bindings.BindName(subdecl.Name, subdecl, null)) {
            // the add was successful
          } else {
            // there's already something with this name
            ModuleDecl prevDecl;
            var yes = bindings.TryLookup(subdecl.tok, out prevDecl);
            Contract.Assert(yes);
            if (prevDecl is AbstractModuleDecl || prevDecl is AliasModuleDecl) {
              reporter.Error(MessageSource.Resolver, subdecl.tok, "Duplicate name of import: {0}", subdecl.Name);
            } else if (tld is AliasModuleDecl importDecl && importDecl.Opened && importDecl.TargetQId.Path.Count == 1 &&
                       importDecl.Name == importDecl.TargetQId.rootName()) {
              importDecl.ShadowsLiteralModule = true;
            } else {
              reporter.Error(MessageSource.Resolver, subdecl.tok,
                "Import declaration uses same name as a module in the same scope: {0}", subdecl.Name);
            }
          }
        }
      }

      return bindings;
    }

    private Tuple<List<IToken>, LiteralModuleDecl> ShortenPrefix(Tuple<List<IToken>, LiteralModuleDecl> tup) {
      Contract.Requires(tup.Item1.Count != 0);
      var rest = tup.Item1.GetRange(1, tup.Item1.Count - 1);
      return new Tuple<List<IToken>, LiteralModuleDecl>(rest, tup.Item2);
    }

    private void BindModuleName_LiteralModuleDecl(LiteralModuleDecl litmod,
      List<Tuple<List<IToken>, LiteralModuleDecl>> /*?*/ prefixModules, ModuleBindings parentBindings) {
      Contract.Requires(litmod != null);
      Contract.Requires(parentBindings != null);

      // Transfer prefix-named modules downwards into the sub-module
      if (prefixModules != null) {
        foreach (var tup in prefixModules) {
          if (tup.Item1.Count == 0) {
            tup.Item2.ModuleDef.EnclosingModule =
              litmod.ModuleDef; // change the parent, now that we have found the right parent module for the prefix-named module
            var sm = new LiteralModuleDecl(tup.Item2.ModuleDef,
              litmod.ModuleDef); // this will create a ModuleDecl with the right parent
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

    private bool ResolveQualifiedModuleIdRootRefines(ModuleDefinition context, ModuleBindings bindings, ModuleQualifiedId qid,
      out ModuleDecl result) {
      Contract.Assert(qid != null);
      IToken root = qid.Path[0].StartToken;
      result = null;
      bool res = bindings.TryLookupFilter(root, out result, m => m.EnclosingModuleDefinition != context);
      qid.Root = result;
      return res;
    }

    // Find a matching module for the root of the QualifiedId, ignoring
    // (a) the module (context) itself and (b) any local imports
    // The latter is so that if one writes 'import A`E  import F = A`F' the second A does not
    // resolve to the alias produced by the first import
    private bool ResolveQualifiedModuleIdRootImport(AliasModuleDecl context, ModuleBindings bindings, ModuleQualifiedId qid,
      out ModuleDecl result) {
      Contract.Assert(qid != null);
      IToken root = qid.Path[0].StartToken;
      result = null;
      bool res = bindings.TryLookupFilter(root, out result,
        m => context != m && ((context.EnclosingModuleDefinition == m.EnclosingModuleDefinition && context.Exports.Count == 0) || m is LiteralModuleDecl));
      qid.Root = result;
      return res;
    }

    private bool ResolveQualifiedModuleIdRootAbstract(AbstractModuleDecl context, ModuleBindings bindings, ModuleQualifiedId qid,
      out ModuleDecl result) {
      Contract.Assert(qid != null);
      IToken root = qid.Path[0].StartToken;
      result = null;
      bool res = bindings.TryLookupFilter(root, out result,
        m => context != m && ((context.EnclosingModuleDefinition == m.EnclosingModuleDefinition && context.Exports.Count == 0) || m is LiteralModuleDecl));
      qid.Root = result;
      return res;
    }

    private void ProcessDependenciesDefinition(ModuleDecl decl, ModuleDefinition m, ModuleBindings bindings,
      Graph<ModuleDecl> dependencies) {
      Contract.Assert(decl is LiteralModuleDecl);
      if (m.RefinementQId != null) {
        ModuleDecl other;
        bool res = ResolveQualifiedModuleIdRootRefines(((LiteralModuleDecl)decl).ModuleDef, bindings, m.RefinementQId, out other);
        if (!res) {
          reporter.Error(MessageSource.Resolver, m.RefinementQId.rootToken(),
            $"module {m.RefinementQId.ToString()} named as refinement base does not exist");
        } else if (other is LiteralModuleDecl && ((LiteralModuleDecl)other).ModuleDef == m) {
          reporter.Error(MessageSource.Resolver, m.RefinementQId.rootToken(), "module cannot refine itself: {0}",
            m.RefinementQId.ToString());
        } else {
          Contract.Assert(other != null); // follows from postcondition of TryGetValue
          dependencies.AddEdge(decl, other);
        }
      }

      foreach (var toplevel in m.TopLevelDecls) {
        if (toplevel is ModuleDecl) {
          var d = (ModuleDecl)toplevel;
          dependencies.AddEdge(decl, d);
          var subbindings = bindings.SubBindings(d.Name);
          ProcessDependencies(d, subbindings ?? bindings, dependencies);
          if (!m.IsAbstract && d is AbstractModuleDecl && ((AbstractModuleDecl)d).QId.Root != null) {
            reporter.Error(MessageSource.Resolver, d.tok,
              "The abstract import named {0} (using :) may only be used in an abstract module declaration",
              d.Name);
          }
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
        // TryLookupFilter works outward, looking for a match to the filter for
        // each enclosing module.
        if (!ResolveQualifiedModuleIdRootImport(alias, bindings, alias.TargetQId, out root)) {
          //        if (!bindings.TryLookupFilter(alias.TargetQId.rootToken(), out root, m => alias != m)
          reporter.Error(MessageSource.Resolver, alias.tok, ModuleNotFoundErrorMessage(0, alias.TargetQId.Path));
        } else {
          dependencies.AddEdge(moduleDecl, root);
        }
      } else if (moduleDecl is AbstractModuleDecl) {
        var abs = moduleDecl as AbstractModuleDecl;
        ModuleDecl root;
        if (!ResolveQualifiedModuleIdRootAbstract(abs, bindings, abs.QId, out root)) {
          //if (!bindings.TryLookupFilter(abs.QId.rootToken(), out root,
          //  m => abs != m && (((abs.EnclosingModuleDefinition == m.EnclosingModuleDefinition) && (abs.Exports.Count == 0)) || m is LiteralModuleDecl)))
          reporter.Error(MessageSource.Resolver, abs.tok, ModuleNotFoundErrorMessage(0, abs.QId.Path));
        } else {
          dependencies.AddEdge(moduleDecl, root);
        }
      }
    }

    private static string ModuleNotFoundErrorMessage(int i, List<Name> path, string tail = "") {
      Contract.Requires(path != null);
      Contract.Requires(0 <= i && i < path.Count);
      return "module " + path[i].Value + " does not exist" +
             (1 < path.Count
               ? " (position " + i.ToString() + " in path " + Util.Comma(".", path, x => x.Value) + ")" + tail
               : "");
    }

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
        if (info.TopLevels.TryGetValue(kv.Key, out var infoValue)) {
          if (infoValue != kv.Value) {
            // This only happens if one signature contains the name C as a class C (because it
            // provides C) and the other signature contains the name C as a non-null type decl
            // (because it reveals C and C?). The merge output will contain the non-null type decl
            // for the key (and we expect the mapping "C? -> class C" to be placed in the
            // merge output as well, by the end of this loop).
            if (infoValue is ClassDecl) {
              var cd = (ClassDecl)infoValue;
              Contract.Assert(cd.NonNullTypeDecl == kv.Value);
              info.TopLevels[kv.Key] = kv.Value;
            } else if (kv.Value is ClassDecl) {
              var cd = (ClassDecl)kv.Value;
              Contract.Assert(cd.NonNullTypeDecl == infoValue);
              // info.TopLevel[kv.Key] already has the right value
            } else {
              Contract.Assert(false); // unexpected
            }

            continue;
          }
        }

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

    public static void ResolveOpenedImports(ModuleSignature sig, ModuleDefinition moduleDef, bool useCompileSignatures,
      Resolver resolver) {
      var declarations = sig.TopLevels.Values.ToList<TopLevelDecl>();
      var importedSigs = new HashSet<ModuleSignature>() { sig };

      var topLevelDeclReplacements = new List<TopLevelDecl>();
      foreach (var top in declarations) {
        if (top is ModuleDecl md && md.Opened) {
          ResolveOpenedImportsWorker(sig, moduleDef, (ModuleDecl)top, importedSigs, useCompileSignatures, out var topLevelDeclReplacement);
          if (topLevelDeclReplacement != null) {
            topLevelDeclReplacements.Add(topLevelDeclReplacement);
          }
        }
      }
      foreach (var topLevelDeclReplacement in topLevelDeclReplacements) {
        if (sig.TopLevels.GetValueOrDefault(topLevelDeclReplacement.Name) is ModuleDecl moduleDecl) {
          sig.ShadowedImportedModules[topLevelDeclReplacement.Name] = moduleDecl;
        }
        sig.TopLevels[topLevelDeclReplacement.Name] = topLevelDeclReplacement;
      }

      if (resolver != null) {
        //needed because ResolveOpenedImports is used statically for a refinement check
        if (sig.TopLevels["_default"] is AmbiguousTopLevelDecl) {
          Contract.Assert(sig.TopLevels["_default"].WhatKind == "class");
          var cl = new DefaultClassDecl(moduleDef, sig.StaticMembers.Values.ToList());
          sig.TopLevels["_default"] = cl;
          resolver.classMembers[cl] = cl.Members.ToDictionary(m => m.Name);
        }
      }
    }

    static TopLevelDecl ResolveAlias(TopLevelDecl dd) {
      while (dd is AliasModuleDecl amd) {
        dd = amd.TargetQId.Root;
      }
      return dd;
    }

    /// <summary>
    /// Further populate "sig" with the accessible symbols from "im".
    ///
    /// Symbols declared locally in "moduleDef" take priority over any opened-import symbols, with one
    /// exception:  for an "import opened M" where "M" contains a top-level symbol "M", unambiguously map the
    /// name "M" to that top-level symbol in "sig". To achieve the "unambiguously" part, return the desired mapping
    /// to the caller, and let the caller remap the symbol after all opened imports have been processed.
    /// </summary>
    static void ResolveOpenedImportsWorker(ModuleSignature sig, ModuleDefinition moduleDef, ModuleDecl im, HashSet<ModuleSignature> importedSigs,
      bool useCompileSignatures, out TopLevelDecl topLevelDeclReplacement) {

      topLevelDeclReplacement = null;
      var s = GetSignatureExt(im.AccessibleSignature(useCompileSignatures), useCompileSignatures);

      if (importedSigs.Contains(s)) {
        return; // we've already got these declarations
      }

      importedSigs.Add(s);

      // top-level declarations:
      foreach (var kv in s.TopLevels) {
        if (!kv.Value.CanBeExported()) {
          continue;
        }

        if (!sig.TopLevels.TryGetValue(kv.Key, out var d)) {
          sig.TopLevels.Add(kv.Key, kv.Value);
        } else if (d.EnclosingModuleDefinition == moduleDef) {
          if (kv.Value.EnclosingModuleDefinition.DafnyName != kv.Key) {
            // declarations in the importing module take priority over opened-import declarations
          } else {
            // As an exception to the rule, for an "import opened M" that contains a top-level symbol "M", unambiguously map the
            // name "M" to that top-level symbol in "sig". To achieve the "unambiguously" part, return the desired mapping to
            // the caller, and let the caller remap the symbol after all opened imports have been processed.
            topLevelDeclReplacement = kv.Value;
          }
        } else {
          bool unambiguous = false;
          // keep just one if they normalize to the same entity
          if (d == kv.Value) {
            unambiguous = true;
          } else if (d is ModuleDecl || kv.Value is ModuleDecl) {
            var dd = ResolveAlias(d);
            var dk = ResolveAlias(kv.Value);
            unambiguous = dd == dk;
          } else {
            // It's okay if "d" and "kv.Value" denote the same type. This can happen, for example,
            // if both are type synonyms for "int".
            var scope = Type.GetScope();
            if (d.IsVisibleInScope(scope) && kv.Value.IsVisibleInScope(scope)) {
              var dType = UserDefinedType.FromTopLevelDecl(d.tok, d);
              var vType = UserDefinedType.FromTopLevelDecl(kv.Value.tok, kv.Value);
              unambiguous = dType.Equals(vType, true);
            }
          }
          if (!unambiguous) {
            sig.TopLevels[kv.Key] = AmbiguousTopLevelDecl.Create(moduleDef, d, kv.Value);
          }
        }
      }

      // constructors:
      foreach (var kv in s.Ctors) {
        if (sig.Ctors.TryGetValue(kv.Key, out var pair)) {
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

      // static members:
      foreach (var kv in s.StaticMembers) {
        if (!kv.Value.CanBeExported()) {
          continue;
        }

        if (sig.StaticMembers.TryGetValue(kv.Key, out var md)) {
          sig.StaticMembers[kv.Key] = AmbiguousMemberDecl.Create(moduleDef, md, kv.Value);
        } else {
          // add new
          sig.StaticMembers.Add(kv.Key, kv.Value);
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
      var anonymousImportCount = 0;
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);

        if (d is RevealableTypeDecl) {
          revealableTypes.Add((RevealableTypeDecl)d);
        }

        // register the class/datatype/module name
        {
          TopLevelDecl registerThisDecl = null;
          string registerUnderThisName = null;
          if (d is ModuleExportDecl export) {
            if (sig.ExportSets.ContainsKey(d.Name)) {
              reporter.Error(MessageSource.Resolver, d, "duplicate name of export set: {0}", d.Name);
            } else {
              sig.ExportSets[d.Name] = export;
            }
          } else if (d is AliasModuleDecl importDecl && importDecl.ShadowsLiteralModule) {
            // add under an anonymous name
            registerThisDecl = d;
            registerUnderThisName = string.Format("{0}#{1}", d.Name, anonymousImportCount);
            anonymousImportCount++;
          } else if (toplevels.ContainsKey(d.Name)) {
            reporter.Error(MessageSource.Resolver, d, "duplicate name of top-level declaration: {0}", d.Name);
          } else if (d is ClassDecl cl && cl.NonNullTypeDecl != null) {
            registerThisDecl = cl.NonNullTypeDecl;
            registerUnderThisName = d.Name;
          } else {
            registerThisDecl = d;
            registerUnderThisName = d.Name;
          }

          if (registerThisDecl != null) {
            toplevels[registerUnderThisName] = registerThisDecl;
            sig.TopLevels[registerUnderThisName] = registerThisDecl;
          }
        }
        if (d is ModuleDecl) {
          // nothing to do
        } else if (d is TypeSynonymDecl) {
          // nothing more to register
        } else if (d is NewtypeDecl || d is OpaqueTypeDecl) {
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
              reporter.Error(MessageSource.Resolver, p,
                "Name of in-parameter is used by another member of the iterator: {0}", p.Name);
            } else {
              var field = new SpecialField(p.RangeToken, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, false,
                false, p.Type, null);
              field.EnclosingClass = iter; // resolve here
              field.InheritVisibility(iter);
              members.Add(p.Name, field);
              iter.Members.Add(field);
            }
          }

          var nonDuplicateOuts = new List<Formal>();
          foreach (var p in iter.Outs) {
            if (members.ContainsKey(p.Name)) {
              reporter.Error(MessageSource.Resolver, p,
                "Name of yield-parameter is used by another member of the iterator: {0}", p.Name);
            } else {
              nonDuplicateOuts.Add(p);
              var field = new SpecialField(p.RangeToken, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, true,
                true, p.Type, null);
              field.EnclosingClass = iter; // resolve here
              field.InheritVisibility(iter);
              iter.OutsFields.Add(field);
              members.Add(p.Name, field);
              iter.Members.Add(field);
            }
          }

          foreach (var p in nonDuplicateOuts) {
            var nm = p.Name + "s";
            if (members.ContainsKey(nm)) {
              reporter.Error(MessageSource.Resolver, p.tok,
                "Name of implicit yield-history variable '{0}' is already used by another member of the iterator",
                p.Name);
              nm = p.Name + "*"; // bogus name, but at least it'll be unique
            }

            // we add some field to OutsHistoryFields, even if there was an error; the name of the field, in case of error, is not so important
            var tp = new SeqType(p.Type.NormalizeExpand());
            var field = new SpecialField(p.RangeToken, nm, SpecialField.ID.UseIdParam, nm, true, true, false, tp, null);
            field.EnclosingClass = iter; // resolve here
            field.InheritVisibility(iter);
            iter.OutsHistoryFields
              .Add(field); // for now, just record this field (until all parameters have been added as members)
          }

          Contract.Assert(iter.OutsFields.Count ==
                          iter.OutsHistoryFields
                            .Count); // the code above makes sure this holds, even in the face of errors
          // now that already-used 'ys' names have been checked for, add these yield-history variables
          iter.OutsHistoryFields.ForEach(f => {
            members.Add(f.Name, f);
            iter.Members.Add(f);
          });
          // add the additional special variables as fields
          iter.Member_Reads = new SpecialField(iter.RangeToken, "_reads", SpecialField.ID.Reads, null, true, false, false,
            new SetType(true, builtIns.ObjectQ()), null);
          iter.Member_Modifies = new SpecialField(iter.RangeToken, "_modifies", SpecialField.ID.Modifies, null, true, false,
            false, new SetType(true, builtIns.ObjectQ()), null);
          iter.Member_New = new SpecialField(iter.RangeToken, "_new", SpecialField.ID.New, null, true, true, true,
            new SetType(true, builtIns.ObjectQ()), null);
          foreach (var field in new List<Field>() { iter.Member_Reads, iter.Member_Modifies, iter.Member_New }) {
            field.EnclosingClass = iter; // resolve here
            field.InheritVisibility(iter);
            members.Add(field.Name, field);
            iter.Members.Add(field);
          }

          // finally, add special variables to hold the components of the (explicit or implicit) decreases clause
          new InferDecreasesClause(this).FillInDefaultDecreases(iter, false);
          // create the fields; unfortunately, we don't know their types yet, so we'll just insert type proxies for now
          var i = 0;
          foreach (var p in iter.Decreases.Expressions) {
            var nm = "_decreases" + i;
            var field = new SpecialField(p.RangeToken, nm, SpecialField.ID.UseIdParam, nm, true, false, false,
              new InferredTypeProxy(), null);
            field.EnclosingClass = iter; // resolve here
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
          var init = new Constructor(iter.RangeToken, new Name(iter.NameNode.RangeToken, "_ctor"), false, new List<TypeParameter>(), iter.Ins,
            new List<AttributedExpression>(),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            new List<AttributedExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, null, null);
          // --- here comes predicate Valid()
          var valid = new Predicate(iter.RangeToken, new Name(iter.NameNode.RangeToken, "Valid"), false, true, false, new List<TypeParameter>(),
            new List<Formal>(),
            null,
            new List<AttributedExpression>(),
            new List<FrameExpression>(),
            new List<AttributedExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, Predicate.BodyOriginKind.OriginalOrInherited, null, null, null, null);
          // --- here comes method MoveNext
          var moveNext = new Method(iter.RangeToken, new Name(iter.NameNode.RangeToken, "MoveNext"), false, false, new List<TypeParameter>(),
            new List<Formal>(), new List<Formal>() { new Formal(iter.tok, "more", Type.Bool, false, false, null) },
            new List<AttributedExpression>(),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            new List<AttributedExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, Attributes.Find(iter.Attributes, "print"), null);
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
            reporter.Error(MessageSource.Resolver, member.tok,
              "member name '{0}' is already predefined for this iterator", init.Name);
          } else {
            members.Add(init.Name, init);
            iter.Members.Add(init);
          }

          // If the name of the iterator is "Valid" or "MoveNext", one of the following will produce an error message.  That
          // error message may not be as clear as it could be, but the situation also seems unlikely to ever occur in practice.
          if (members.TryGetValue("Valid", out member)) {
            reporter.Error(MessageSource.Resolver, member.tok,
              "member name 'Valid' is already predefined for iterators");
          } else {
            members.Add(valid.Name, valid);
            iter.Members.Add(valid);
          }

          if (members.TryGetValue("MoveNext", out member)) {
            reporter.Error(MessageSource.Resolver, member.tok,
              "member name 'MoveNext' is already predefined for iterators");
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

          Contract.Assert(preMemberErrs != reporter.Count(ErrorLevel.Error) ||
                          !cl.Members.Except(members.Values).Any());

          if (cl.IsDefaultClass) {
            foreach (MemberDecl m in members.Values) {
              Contract.Assert(!m.HasStaticKeyword || m is ConstantField ||
                              DafnyOptions.O
                                .AllowGlobals); // note, the IsStatic value isn't available yet; when it becomes available, we expect it will have the value 'true'
              if (m is Function || m is Method || m is ConstantField) {
                sig.StaticMembers[m.Name] = m;
              }

              if (toplevels.ContainsKey(m.Name)) {
                reporter.Error(MessageSource.Resolver, m.tok,
                  $"duplicate declaration for name {m.Name}");
              }
            }
          }

        } else if (d is DatatypeDecl) {
          var dt = (DatatypeDecl)d;

          // register the names of the constructors
          dt.ConstructorsByName = new();
          // ... and of the other members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(dt, members);

          foreach (DatatypeCtor ctor in dt.Ctors) {
            if (ctor.Name.EndsWith("?")) {
              reporter.Error(MessageSource.Resolver, ctor,
                "a datatype constructor name is not allowed to end with '?'");
            } else if (dt.ConstructorsByName.ContainsKey(ctor.Name)) {
              reporter.Error(MessageSource.Resolver, ctor, "Duplicate datatype constructor name: {0}", ctor.Name);
            } else {
              dt.ConstructorsByName.Add(ctor.Name, ctor);
              ctor.InheritVisibility(dt);

              // create and add the query "method" (field, really)
              var queryName = ctor.NameNode.Append("?");
              var query = new DatatypeDiscriminator(ctor.RangeToken, queryName, SpecialField.ID.UseIdParam, "is_" + ctor.CompileName,
                ctor.IsGhost, Type.Bool, null);
              query.InheritVisibility(dt);
              query.EnclosingClass = dt; // resolve here
              members.Add(queryName.Value, query);
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
                    reporter.Error(MessageSource.Resolver, ctor,
                      "Duplicate use of deconstructor name in the same constructor: {0}", formal.Name);
                  } else if (previousMember is DatatypeDestructor) {
                    // this is okay, if the destructor has the appropriate type; this will be checked later, after type checking
                  } else {
                    reporter.Error(MessageSource.Resolver, ctor,
                      "Name of deconstructor is used by another member of the datatype: {0}", formal.Name);
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
                dtor = new DatatypeDestructor(formal.RangeToken, ctor, formal, new Name(formal.RangeToken, formal.Name), "dtor_" + formal.CompileName,
                  formal.IsGhost, formal.Type, null);
                dtor.InheritVisibility(dt);
                dtor.EnclosingClass = dt; // resolve here
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
            reporter.Error(MessageSource.Resolver, d,
              "a module that already contains a top-level declaration '{0}' is not allowed to declare a {1} '{2}'",
              name, d.WhatKind, d.Name);
          } else {
            toplevels[name] = d;
            sig.TopLevels[name] = d;
          }
        }
      }

      return sig;
    }

    void RegisterMembers(ModuleDefinition moduleDef, TopLevelDeclWithMembers cl,
      Dictionary<string, MemberDecl> members) {
      Contract.Requires(moduleDef != null);
      Contract.Requires(cl != null);
      Contract.Requires(members != null);

      foreach (MemberDecl m in cl.Members) {
        if (!members.ContainsKey(m.Name)) {
          members.Add(m.Name, m);
          if (m is Constructor) {
            Contract.Assert(cl is ClassDecl); // the parser ensures this condition
            if (cl is TraitDecl) {
              reporter.Error(MessageSource.Resolver, m.tok, "a trait is not allowed to declare a constructor");
            } else {
              ((ClassDecl)cl).HasConstructor = true;
            }
          } else if (m is ExtremePredicate || m is ExtremeLemma) {
            var extraName = m.NameNode.Append("#");
            MemberDecl extraMember;
            var cloner = new Cloner();
            var formals = new List<Formal>();
            Type typeOfK;
            if ((m is ExtremePredicate && ((ExtremePredicate)m).KNat) ||
                (m is ExtremeLemma && ((ExtremeLemma)m).KNat)) {
              typeOfK = new UserDefinedType(m.tok, "nat", (List<Type>)null);
            } else {
              typeOfK = new BigOrdinalType();
            }

            var k = new ImplicitFormal(m.tok, "_k", typeOfK, true, false);
            reporter.Info(MessageSource.Resolver, m.tok, string.Format("_k: {0}", k.Type));
            formals.Add(k);
            if (m is ExtremePredicate extremePredicate) {
              formals.AddRange(extremePredicate.Formals.ConvertAll(f => cloner.CloneFormal(f, false)));

              List<TypeParameter> tyvars = extremePredicate.TypeArgs.ConvertAll(cloner.CloneTypeParam);

              // create prefix predicate
              extremePredicate.PrefixPredicate = new PrefixPredicate(extremePredicate.RangeToken, extraName, extremePredicate.HasStaticKeyword,
                tyvars, k, formals,
                extremePredicate.Req.ConvertAll(cloner.CloneAttributedExpr),
                extremePredicate.Reads.ConvertAll(cloner.CloneFrameExpr),
                extremePredicate.Ens.ConvertAll(cloner.CloneAttributedExpr),
                new Specification<Expression>(new List<Expression>() { new IdentifierExpr(extremePredicate.tok, k.Name) }, null),
                cloner.CloneExpr(extremePredicate.Body),
                null,
                extremePredicate);
              extraMember = extremePredicate.PrefixPredicate;
            } else {
              var extremeLemma = (ExtremeLemma)m;
              // _k has already been added to 'formals', so append the original formals
              formals.AddRange(extremeLemma.Ins.ConvertAll(f => cloner.CloneFormal(f, false)));
              // prepend _k to the given decreases clause
              var decr = new List<Expression>();
              decr.Add(new IdentifierExpr(extremeLemma.tok, k.Name));
              decr.AddRange(extremeLemma.Decreases.Expressions.ConvertAll(cloner.CloneExpr));
              // Create prefix lemma.  Note that the body is not cloned, but simply shared.
              // For a greatest lemma, the postconditions are filled in after the greatest lemma's postconditions have been resolved.
              // For a least lemma, the preconditions are filled in after the least lemma's preconditions have been resolved.
              var req = extremeLemma is GreatestLemma
                ? extremeLemma.Req.ConvertAll(cloner.CloneAttributedExpr)
                : new List<AttributedExpression>();
              var ens = extremeLemma is GreatestLemma
                ? new List<AttributedExpression>()
                : extremeLemma.Ens.ConvertAll(cloner.CloneAttributedExpr);
              extremeLemma.PrefixLemma = new PrefixLemma(extremeLemma.RangeToken, extraName, extremeLemma.HasStaticKeyword,
                extremeLemma.TypeArgs.ConvertAll(cloner.CloneTypeParam), k, formals, extremeLemma.Outs.ConvertAll(f => cloner.CloneFormal(f, false)),
                req, cloner.CloneSpecFrameExpr(extremeLemma.Mod), ens,
                new Specification<Expression>(decr, null),
                null, // Note, the body for the prefix method will be created once the call graph has been computed and the SCC for the greatest lemma is known
                cloner.CloneAttributes(extremeLemma.Attributes), extremeLemma);
              extraMember = extremeLemma.PrefixLemma;
            }

            extraMember.InheritVisibility(m, false);
            members.Add(extraName.Value, extraMember);
          } else if (m is Function f && f.ByMethodBody != null) {
            RegisterByMethod(f, cl);
          }
        } else if (m is Constructor && !((Constructor)m).HasName) {
          reporter.Error(MessageSource.Resolver, m, "More than one anonymous constructor");
        } else {
          reporter.Error(MessageSource.Resolver, m, "Duplicate member name: {0}", m.Name);
        }
      }
    }

    void RegisterByMethod(Function f, TopLevelDeclWithMembers cl) {
      Contract.Requires(f != null && f.ByMethodBody != null);

      var tok = f.ByMethodTok;
      var resultVar = f.Result ?? new Formal(tok, "#result", f.ResultType, false, false, null);
      var r = Expression.CreateIdentExpr(resultVar);
      var receiver = f.IsStatic ? (Expression)new StaticReceiverExpr(tok, cl, true) : new ImplicitThisExpr(tok);
      var fn = new FunctionCallExpr(tok, f.Name, receiver, tok, tok, f.Formals.ConvertAll(Expression.CreateIdentExpr));
      var post = new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, r, fn));
      var method = new Method(f.RangeToken, f.NameNode, f.HasStaticKeyword, false, f.TypeArgs,
        f.Formals, new List<Formal>() { resultVar },
        f.Req, new Specification<FrameExpression>(new List<FrameExpression>(), null), new List<AttributedExpression>() { post }, f.Decreases,
        f.ByMethodBody, f.Attributes, null, true);
      Contract.Assert(f.ByMethodDecl == null);
      method.InheritVisibility(f);
      f.ByMethodDecl = method;
    }

    private ModuleSignature MakeAbstractSignature(ModuleSignature p, string Name, int Height,
      Dictionary<ModuleDefinition, ModuleSignature> mods,
      Dictionary<ModuleDefinition, ModuleDefinition> compilationModuleClones) {
      Contract.Requires(p != null);
      Contract.Requires(Name != null);
      Contract.Requires(mods != null);
      Contract.Requires(compilationModuleClones != null);
      var errCount = reporter.Count(ErrorLevel.Error);

      var mod = new ModuleDefinition(RangeToken.NoToken, new Name(Name + ".Abs"), new List<IToken>(), true, true, null, null, null,
        false,
        p.ModuleDef.IsToBeVerified, p.ModuleDef.IsToBeCompiled);
      mod.Height = Height;
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

    TopLevelDecl CloneDeclaration(VisibilityScope scope, TopLevelDecl d, ModuleDefinition m,
      Dictionary<ModuleDefinition, ModuleSignature> mods, string Name,
      Dictionary<ModuleDefinition, ModuleDefinition> compilationModuleClones) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);
      Contract.Requires(mods != null);
      Contract.Requires(Name != null);
      Contract.Requires(compilationModuleClones != null);

      if (d is AbstractModuleDecl) {
        var abs = (AbstractModuleDecl)d;
        var sig = MakeAbstractSignature(abs.OriginalSignature, Name + "." + abs.Name, abs.Height, mods,
          compilationModuleClones);
        var a = new AbstractModuleDecl(abs.RangeToken, abs.QId, abs.NameNode, m, abs.Opened, abs.Exports);
        a.Signature = sig;
        a.OriginalSignature = abs.OriginalSignature;
        return a;
      } else {
        return new AbstractSignatureCloner(scope).CloneDeclaration(d, m);
      }
    }

    // Returns the resolved Module declaration corresponding to the qualified module id
    // Requires the root to have been resolved
    // Issues an error and returns null if the path is not valid
    public ModuleDecl ResolveModuleQualifiedId(ModuleDecl root, ModuleQualifiedId qid, ErrorReporter reporter) {

      Contract.Requires(qid != null);
      Contract.Requires(qid.Path.Count > 0);

      List<Name> Path = qid.Path;
      ModuleDecl decl = root;
      ModuleSignature p;
      for (int k = 1; k < Path.Count; k++) {
        if (decl is LiteralModuleDecl) {
          p = ((LiteralModuleDecl)decl).DefaultExport;
          if (p == null) {
            reporter.Error(MessageSource.Resolver, Path[k],
              ModuleNotFoundErrorMessage(k, Path, $" because {decl.Name} does not have a default export"));
            return null;
          }
        } else {
          p = decl.Signature;
        }

        var tld = p.TopLevels.GetValueOrDefault(Path[k].Value, null);
        if (!(tld is ModuleDecl dd)) {
          if (decl.Signature.ModuleDef == null) {
            reporter.Error(MessageSource.Resolver, Path[k],
              ModuleNotFoundErrorMessage(k, Path, " because of previous error"));
          } else {
            reporter.Error(MessageSource.Resolver, Path[k], ModuleNotFoundErrorMessage(k, Path));
          }
          return null;
        }

        // Any aliases along the qualified path ought to be already resolved,
        // else the modules are not being resolved in the right order
        if (dd is AliasModuleDecl amd) {
          Contract.Assert(amd.Signature != null);
        }
        decl = dd;
      }

      return decl;
    }


    public bool ResolveExport(ModuleDecl alias, ModuleDefinition parent, ModuleQualifiedId qid,
      List<IToken> Exports, out ModuleSignature p, ErrorReporter reporter) {
      Contract.Requires(qid != null);
      Contract.Requires(qid.Path.Count > 0);
      Contract.Requires(Exports != null);

      ModuleDecl root = qid.Root;
      ModuleDecl decl = ResolveModuleQualifiedId(root, qid, reporter);
      if (decl == null) {
        p = null;
        return false;
      }
      p = decl.Signature;
      if (Exports.Count == 0) {
        if (p.ExportSets.Count == 0) {
          if (decl is LiteralModuleDecl) {
            p = ((LiteralModuleDecl)decl).DefaultExport;
          } else {
            // p is OK
          }
        } else {
          var m = p.ExportSets.GetValueOrDefault(decl.Name, null);
          if (m == null) {
            // no default view is specified.
            reporter.Error(MessageSource.Resolver, qid.rootToken(), "no default export set declared in module: {0}", decl.Name);
            return false;
          }
          p = m.AccessibleSignature();
        }
      } else {
        ModuleExportDecl pp;
        if (decl.Signature.ExportSets.TryGetValue(Exports[0].val, out pp)) {
          p = pp.AccessibleSignature();
        } else {
          reporter.Error(MessageSource.Resolver, Exports[0], "no export set '{0}' in module '{1}'", Exports[0].val, decl.Name);
          p = null;
          return false;
        }

        foreach (IToken export in Exports.Skip(1)) {
          if (decl.Signature.ExportSets.TryGetValue(export.val, out pp)) {
            Contract.Assert(Object.ReferenceEquals(p.ModuleDef, pp.Signature.ModuleDef));
            ModuleSignature merged = MergeSignature(p, pp.Signature);
            merged.ModuleDef = pp.Signature.ModuleDef;
            if (p.CompileSignature != null) {
              Contract.Assert(pp.Signature.CompileSignature != null);
              merged.CompileSignature = MergeSignature(p.CompileSignature, pp.Signature.CompileSignature);
            } else {
              Contract.Assert(pp.Signature.CompileSignature == null);
            }
            p = merged;
          } else {
            reporter.Error(MessageSource.Resolver, export, "no export set {0} in module {1}", export.val, decl.Name);
            p = null;
            return false;
          }
        }
      }
      return true;
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

      var typeRedirectionDependencies = new Graph<RedirectingTypeDecl>();  // this concerns the type directions, not their constraints (which are checked for cyclic dependencies later)
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        if (d is TypeSynonymDecl) {
          var dd = (TypeSynonymDecl)d;
          ResolveType(dd.tok, dd.Rhs, dd, ResolveTypeOptionEnum.AllowPrefix, dd.TypeArgs);
          dd.Rhs.ForeachTypeComponent(ty => {
            var s = ty.AsRedirectingType;
            if (s != null && s != dd) {
              typeRedirectionDependencies.AddEdge(dd, s);
            }
          });
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          ResolveType(dd.tok, dd.BaseType, dd, ResolveTypeOptionEnum.DontInfer, null);
          dd.BaseType.ForeachTypeComponent(ty => {
            var s = ty.AsRedirectingType;
            if (s != null && s != dd) {
              typeRedirectionDependencies.AddEdge(dd, s);
            }
          });
          ResolveClassMemberTypes(dd);
        } else if (d is IteratorDecl) {
          ResolveIteratorSignature((IteratorDecl)d);
        } else if (d is ModuleDecl) {
          var decl = (ModuleDecl)d;
          if (!def.IsAbstract && decl is AliasModuleDecl am && decl.Signature.IsAbstract) {
            reporter.Error(MessageSource.Resolver, am.TargetQId.rootToken(), "a compiled module ({0}) is not allowed to import an abstract module ({1})", def.Name, am.TargetQId.ToString());
          }
        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          ResolveCtorTypes(dd, datatypeDependencies, codatatypeDependencies);
          ResolveClassMemberTypes(dd);
        } else {
          ResolveClassMemberTypes((TopLevelDeclWithMembers)d);
        }
        allTypeParameters.PopMarker();
      }

      // Resolve the parent-trait types and fill in .ParentTraitHeads
      var prevErrorCount = reporter.Count(ErrorLevel.Error);
      var parentRelation = new Graph<TopLevelDeclWithMembers>();
      foreach (TopLevelDecl d in declarations) {
        if (d is TopLevelDeclWithMembers cl) {
          ResolveParentTraitTypes(cl, parentRelation);
        }
      }
      // Check for cycles among parent traits
      foreach (var cycle in parentRelation.AllCycles()) {
        ReportCycleError(cycle, m => m.tok, m => m.Name, "trait definitions contain a cycle");
      }
      if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
        // Register the trait members in the classes that inherit them
        foreach (TopLevelDecl d in declarations) {
          if (d is TopLevelDeclWithMembers cl) {
            RegisterInheritedMembers(cl);
          }
        }
      }
      if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
        // Now that all traits have been resolved, let classes inherit the trait members
        foreach (var d in declarations) {
          if (d is TopLevelDeclWithMembers cl) {
            InheritedTraitMembers(cl);
          }
        }
      }

      // perform acyclicity test on type synonyms
      foreach (var cycle in typeRedirectionDependencies.AllCycles()) {
        ReportCycleError(cycle, rtd => rtd.tok, rtd => rtd.Name, "cycle among redirecting types (newtypes, subset types, type synonyms)");
      }
    }

    public static readonly List<NativeType> NativeTypes = new List<NativeType>() {
      new NativeType("byte", 0, 0x100, 8, NativeType.Selection.Byte),
      new NativeType("sbyte", -0x80, 0x80, 0, NativeType.Selection.SByte),
      new NativeType("ushort", 0, 0x1_0000, 16, NativeType.Selection.UShort),
      new NativeType("short", -0x8000, 0x8000, 0, NativeType.Selection.Short),
      new NativeType("uint", 0, 0x1_0000_0000, 32, NativeType.Selection.UInt),
      new NativeType("int", -0x8000_0000, 0x8000_0000, 0, NativeType.Selection.Int),
      new NativeType("number", -0x1f_ffff_ffff_ffff, 0x20_0000_0000_0000, 0, NativeType.Selection.Number),  // JavaScript integers
      new NativeType("ulong", 0, new BigInteger(0x1_0000_0000) * new BigInteger(0x1_0000_0000), 64, NativeType.Selection.ULong),
      new NativeType("long", Int64.MinValue, 0x8000_0000_0000_0000, 0, NativeType.Selection.Long),
    };

    public void ResolveTopLevelDecls_Core(List<TopLevelDecl/*!*/>/*!*/ declarations, Graph<IndDatatypeDecl/*!*/>/*!*/ datatypeDependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ codatatypeDependencies, bool isAnExport = false) {
      Contract.Requires(declarations != null);
      Contract.Requires(cce.NonNullElements(datatypeDependencies.GetVertices()));
      Contract.Requires(cce.NonNullElements(codatatypeDependencies.GetVertices()));
      Contract.Requires(AllTypeConstraints.Count == 0);

      Contract.Ensures(AllTypeConstraints.Count == 0);

      int prevErrorCount = reporter.Count(ErrorLevel.Error);

      // ---------------------------------- Pass 0 ----------------------------------
      // This pass:
      // * resolves names, introduces (and may solve) type constraints
      // * checks that all types were properly inferred
      // * fills in .ResolvedOp fields
      // * perform substitution for DefaultValueExpression's
      // ----------------------------------------------------------------------------

      // Resolve all names and infer types. These two are done together, because name resolution depends on having type information
      // and type inference depends on having resolved names.
      // The task is first performed for (the constraints of) newtype declarations, (the constraints of) subset type declarations, and
      // (the right-hand sides of) const declarations, because type resolution sometimes needs to know the base type of newtypes and subset types
      // and needs to know the type of const fields. Doing these declarations increases the chances the right information will be provided
      // in time.
      // Once the task is done for these newtype/subset-type/const parts, the task continues with everything else.
      ResolveNamesAndInferTypes(declarations, true);
      ResolveNamesAndInferTypes(declarations, false);

      // Check that all types have been determined. During this process, fill in all .ResolvedOp fields.
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        var checkTypeInferenceVisitor = new CheckTypeInferenceVisitor(this);
        checkTypeInferenceVisitor.VisitDeclarations(declarations);
      }

      // Substitute for DefaultValueExpression's
      FillInDefaultValueExpressions();

      // ---------------------------------- Pass 1 ----------------------------------
      // This pass does the following:
      // * discovers bounds
      // * builds the module's call graph.
      // * compute and checks ghosts (this makes use of bounds discovery, as done above)
      // * for newtypes, figure out native types
      // * for datatypes, check that shared destructors are in agreement in ghost matters
      // * for functions and methods, determine tail recursion
      // ----------------------------------------------------------------------------

      // Discover bounds. These are needed later to determine if certain things are ghost or compiled, and thus this should
      // be done before building the call graph.
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        var boundsDiscoveryVisitor = new BoundsDiscoveryVisitor(reporter);
        boundsDiscoveryVisitor.VisitDeclarations(declarations);
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        CallGraphBuilder.Build(declarations, reporter);
      }

      // Compute ghost interests, figure out native types, check agreement among datatype destructors, and determine tail calls.
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        foreach (TopLevelDecl d in declarations) {
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            iter.SubExpressions.Iter(e => CheckExpression(e, this, iter));
            if (iter.Body != null) {
              ComputeGhostInterest(iter.Body, false, null, iter);
              CheckExpression(iter.Body, this, iter);
            }

          } else if (d is SubsetTypeDecl subsetTypeDecl) {
            Contract.Assert(subsetTypeDecl.Constraint != null);
            CheckExpression(subsetTypeDecl.Constraint, this, new CodeContextWrapper(subsetTypeDecl, true));
            subsetTypeDecl.ConstraintIsCompilable =
              ExpressionTester.CheckIsCompilable(null, subsetTypeDecl.Constraint, new CodeContextWrapper(subsetTypeDecl, true));
            subsetTypeDecl.CheckedIfConstraintIsCompilable = true;

            if (subsetTypeDecl.Witness != null) {
              CheckExpression(subsetTypeDecl.Witness, this, new CodeContextWrapper(subsetTypeDecl, subsetTypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost));
              if (subsetTypeDecl.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
                var codeContext = new CodeContextWrapper(subsetTypeDecl, subsetTypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost);
                ExpressionTester.CheckIsCompilable(this, subsetTypeDecl.Witness, codeContext);
              }
            }

          } else if (d is NewtypeDecl newtypeDecl) {
            if (newtypeDecl.Var != null) {
              Contract.Assert(newtypeDecl.Constraint != null);
              CheckExpression(newtypeDecl.Constraint, this, new CodeContextWrapper(newtypeDecl, true));
              if (newtypeDecl.Witness != null) {
                CheckExpression(newtypeDecl.Witness, this, new CodeContextWrapper(newtypeDecl, newtypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost));
              }
            }
            if (newtypeDecl.Witness != null && newtypeDecl.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
              var codeContext = new CodeContextWrapper(newtypeDecl, newtypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost);
              ExpressionTester.CheckIsCompilable(this, newtypeDecl.Witness, codeContext);
            }

            FigureOutNativeType(newtypeDecl);

          } else if (d is DatatypeDecl) {
            var dd = (DatatypeDecl)d;
            foreach (var member in classMembers[dd].Values) {
              var dtor = member as DatatypeDestructor;
              if (dtor != null) {
                var rolemodel = dtor.CorrespondingFormals[0];
                for (int i = 1; i < dtor.CorrespondingFormals.Count; i++) {
                  var other = dtor.CorrespondingFormals[i];
                  if (rolemodel.IsGhost != other.IsGhost) {
                    reporter.Error(MessageSource.Resolver, other,
                      "shared destructors must agree on whether or not they are ghost, but '{0}' is {1} in constructor '{2}' and {3} in constructor '{4}'",
                      rolemodel.Name,
                      rolemodel.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[0].Name,
                      other.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[i].Name);
                  }
                }
              }
            }
            foreach (var ctor in dd.Ctors) {
              CheckParameterDefaultValuesAreCompilable(ctor.Formals, dd);
            }
          }

          if (d is TopLevelDeclWithMembers cl) {
            ResolveClassMembers_Pass1(cl);
          }
        }
      }

      // ---------------------------------- Pass 2 ----------------------------------
      // This pass fills in various additional information.
      // * Subset type in comprehensions have a compilable constraint 
      // * Postconditions and bodies of prefix lemmas
      // * Compute postconditions and statement body of prefix lemmas
      // * Perform the stratosphere check on inductive datatypes, and compute to what extent the inductive datatypes require equality support
      // * Set the SccRepr field of codatatypes
      // * Perform the guardedness check on co-datatypes
      // * Do datatypes and type synonyms until a fixpoint is reached, same for functions and methods	
      // * Check that functions claiming to be abstemious really are
      // * Check that all == and != operators in non-ghost contexts are applied to equality-supporting types.
      // * Extreme predicate recursivity checks
      // * Verify that subset constraints are compilable if necessary
      // ----------------------------------------------------------------------------

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // fill in the postconditions and bodies of prefix lemmas
        foreach (var com in ModuleDefinition.AllExtremeLemmas(declarations)) {
          var prefixLemma = com.PrefixLemma;
          if (prefixLemma == null) {
            continue;  // something went wrong during registration of the prefix lemma (probably a duplicated extreme lemma name)
          }
          var k = prefixLemma.Ins[0];
          var focalPredicates = new HashSet<ExtremePredicate>();
          if (com is GreatestLemma) {
            // compute the postconditions of the prefix lemma
            Contract.Assume(prefixLemma.Ens.Count == 0);  // these are not supposed to have been filled in before
            foreach (var p in com.Ens) {
              var coConclusions = new HashSet<Expression>();
              CollectFriendlyCallsInExtremeLemmaSpecification(p.E, true, coConclusions, true, com);
              var subst = new ExtremeLemmaSpecificationSubstituter(coConclusions, new IdentifierExpr(k.tok, k.Name), this.reporter, true);
              var post = subst.CloneExpr(p.E);
              prefixLemma.Ens.Add(new AttributedExpression(post));
              foreach (var e in coConclusions) {
                var fce = e as FunctionCallExpr;
                if (fce != null) {  // the other possibility is that "e" is a BinaryExpr
                  GreatestPredicate predicate = (GreatestPredicate)fce.Function;
                  focalPredicates.Add(predicate);
                  // For every focal predicate P in S, add to S all greatest predicates in the same strongly connected
                  // component (in the call graph) as P
                  foreach (var node in predicate.EnclosingClass.EnclosingModuleDefinition.CallGraph.GetSCC(predicate)) {
                    if (node is GreatestPredicate) {
                      focalPredicates.Add((GreatestPredicate)node);
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
              CollectFriendlyCallsInExtremeLemmaSpecification(p.E, true, antecedents, false, com);
              var subst = new ExtremeLemmaSpecificationSubstituter(antecedents, new IdentifierExpr(k.tok, k.Name), this.reporter, false);
              var pre = subst.CloneExpr(p.E);
              prefixLemma.Req.Add(new AttributedExpression(pre, p.Label, null));
              foreach (var e in antecedents) {
                var fce = (FunctionCallExpr)e;  // we expect "antecedents" to contain only FunctionCallExpr's
                LeastPredicate predicate = (LeastPredicate)fce.Function;
                focalPredicates.Add(predicate);
                // For every focal predicate P in S, add to S all least predicates in the same strongly connected
                // component (in the call graph) as P
                foreach (var node in predicate.EnclosingClass.EnclosingModuleDefinition.CallGraph.GetSCC(predicate)) {
                  if (node is LeastPredicate) {
                    focalPredicates.Add((LeastPredicate)node);
                  }
                }
              }
            }
          }
          reporter.Info(MessageSource.Resolver, com.tok,
            focalPredicates.Count == 0 ?
              $"{com.PrefixLemma.Name} has no focal predicates" :
              $"{com.PrefixLemma.Name} with focal predicate{Util.Plural(focalPredicates.Count)} {Util.Comma(focalPredicates, p => p.Name)}");
          // Compute the statement body of the prefix lemma
          Contract.Assume(prefixLemma.Body == null);  // this is not supposed to have been filled in before
          if (com.Body != null) {
            var kMinusOne = new BinaryExpr(com.tok, BinaryExpr.Opcode.Sub, new IdentifierExpr(k.tok, k.Name), new LiteralExpr(com.tok, 1));
            var subst = new ExtremeLemmaBodyCloner(com, kMinusOne, focalPredicates, this.reporter);
            var mainBody = subst.CloneBlockStmt(com.Body);
            Expression kk;
            Statement els;
            if (k.Type.IsBigOrdinalType) {
              kk = new MemberSelectExpr(k.tok, new IdentifierExpr(k.tok, k.Name), "Offset");
              // As an "else" branch, we add recursive calls for the limit case.  When automatic induction is on,
              // this get handled automatically, but we still want it in the case when automatic induction has been
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

              Expression recursiveCallReceiver;
              List<Expression> recursiveCallArgs;
              Translator.RecursiveCallParameters(com.tok, prefixLemma, prefixLemma.TypeArgs, prefixLemma.Ins, null, substMap, out recursiveCallReceiver, out recursiveCallArgs);
              var methodSel = new MemberSelectExpr(com.tok, recursiveCallReceiver, prefixLemma.Name);
              methodSel.Member = prefixLemma;  // resolve here
              methodSel.TypeApplication_AtEnclosingClass = prefixLemma.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.tok, tp));
              methodSel.TypeApplication_JustMember = prefixLemma.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.tok, tp));
              methodSel.Type = new InferredTypeProxy();
              var recursiveCall = new CallStmt(com.RangeToken, new List<Expression>(), methodSel, recursiveCallArgs.ConvertAll(e => new ActualBinding(null, e)));
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
              var forallBody = new BlockStmt(mainBody.RangeToken, new List<Statement>() { recursiveCall });
              var forallStmt = new ForallStmt(mainBody.RangeToken, bvs, attrs, range, new List<AttributedExpression>(), forallBody);
              els = new BlockStmt(mainBody.RangeToken, new List<Statement>() { forallStmt });
            } else {
              kk = new IdentifierExpr(k.tok, k.Name);
              els = null;
            }
            var kPositive = new BinaryExpr(com.tok, BinaryExpr.Opcode.Lt, new LiteralExpr(com.tok, 0), kk);
            var condBody = new IfStmt(mainBody.RangeToken, false, kPositive, mainBody, els);
            prefixLemma.Body = new BlockStmt(mainBody.RangeToken, new List<Statement>() { condBody });
          }
          // The prefix lemma now has all its components, so it's finally time we resolve it
          currentClass = (TopLevelDeclWithMembers)prefixLemma.EnclosingClass;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(currentClass.TypeArgs, false, currentClass);
          ResolveTypeParameters(prefixLemma.TypeArgs, false, prefixLemma);
          ResolveMethod(prefixLemma);
          allTypeParameters.PopMarker();
          currentClass = null;
          new CheckTypeInferenceVisitor(this).VisitMethod(prefixLemma);
          CallGraphBuilder.VisitMethod(prefixLemma, reporter);
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
            var nonnullIter = iter.NonNullTypeDecl;
            Contract.Assert(nonnullIter.TypeArgs.Count == iter.TypeArgs.Count);
            for (var i = 0; i < iter.TypeArgs.Count; i++) {
              var tp = iter.TypeArgs[i];
              var correspondingNonnullIterTypeParameter = nonnullIter.TypeArgs[i];
              if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                // here's our chance to infer the need for equality support
                foreach (var p in iter.Ins) {
                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    correspondingNonnullIterTypeParameter.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    done = true;
                    break;
                  }
                }
                foreach (var p in iter.Outs) {
                  if (done) {
                    break;
                  }

                  if (InferRequiredEqualitySupport(tp, p.Type)) {
                    tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                    correspondingNonnullIterTypeParameter.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
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
                        if (done) {
                          break;
                        }

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
        // Check that functions claiming to be abstemious really are, and check that 'older' parameters are used only when allowed
        foreach (var fn in ModuleDefinition.AllFunctions(declarations)) {
          new Abstemious(reporter).Check(fn);
          CheckOlderParameters(fn);
        }
        // Check that all == and != operators in non-ghost contexts are applied to equality-supporting types.
        // Note that this check can only be done after determining which expressions are ghosts.
        foreach (var d in declarations) {
          for (var attr = d.Attributes; attr != null; attr = attr.Prev) {
            attr.Args.Iter(e => CheckTypeCharacteristics_Expr(e, true));
          }

          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            foreach (var p in iter.Ins) {
              CheckTypeCharacteristics_Type(p.tok, p.Type, p.IsGhost);
            }
            foreach (var p in iter.Outs) {
              CheckTypeCharacteristics_Type(p.tok, p.Type, p.IsGhost);
            }
            if (iter.Body != null) {
              CheckTypeCharacteristics_Stmt(iter.Body, false);
            }
          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            foreach (var parentTrait in cl.ParentTraits) {
              CheckTypeCharacteristics_Type(cl.tok, parentTrait, false);
            }
          } else if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              foreach (var p in ctor.Formals) {
                CheckTypeCharacteristics_Type(p.tok, p.Type, p.IsGhost);
              }
            }
          } else if (d is TypeSynonymDecl) {
            var syn = (TypeSynonymDecl)d;
            CheckTypeCharacteristics_Type(syn.tok, syn.Rhs, false);
            if (!isAnExport) {
              if (syn.SupportsEquality && !syn.Rhs.SupportsEquality) {
                reporter.Error(MessageSource.Resolver, syn.tok, "type '{0}' declared as supporting equality, but the RHS type ({1}) might not",
                  syn.Name, syn.Rhs);
              }
              if (syn.Characteristics.IsNonempty && !syn.Rhs.IsNonempty) {
                reporter.Error(MessageSource.Resolver, syn.tok, "type '{0}' declared as being nonempty, but the RHS type ({1}) may be empty",
                  syn.Name, syn.Rhs);
              } else if (syn.Characteristics.HasCompiledValue && !syn.Rhs.HasCompilableValue) {
                reporter.Error(MessageSource.Resolver, syn.tok,
                  "type '{0}' declared as auto-initialization type, but the RHS type ({1}) does not support auto-initialization", syn.Name, syn.Rhs);
              }
              if (syn.Characteristics.ContainsNoReferenceTypes && syn.Rhs.MayInvolveReferences) {
                reporter.Error(MessageSource.Resolver, syn.tok,
                  "type '{0}' declared as containing no reference types, but the RHS type ({1}) may contain reference types", syn.Name, syn.Rhs);
              }
            }
          }

          if (d is RedirectingTypeDecl) {
            var rtd = (RedirectingTypeDecl)d;
            if (rtd.Constraint != null) {
              CheckTypeCharacteristics_Expr(rtd.Constraint, true);
            }
            if (rtd.Witness != null) {
              CheckTypeCharacteristics_Expr(rtd.Witness, rtd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
            }
          }

          if (d is TopLevelDeclWithMembers) {
            var cl = (TopLevelDeclWithMembers)d;
            foreach (var member in cl.Members) {
              if (member is Field) {
                var f = (Field)member;
                CheckTypeCharacteristics_Type(f.tok, f.Type, f.IsGhost);
                if (f is ConstantField cf && cf.Rhs != null) {
                  CheckTypeCharacteristics_Expr(cf.Rhs, cf.IsGhost);
                }
              } else if (member is Function) {
                var f = (Function)member;
                foreach (var p in f.Formals) {
                  CheckTypeCharacteristics_Type(p.tok, p.Type, f.IsGhost || p.IsGhost);
                }
                if (f.Body != null) {
                  CheckTypeCharacteristics_Expr(f.Body, f.IsGhost);
                }
              } else if (member is Method) {
                var m = (Method)member;
                foreach (var p in m.Ins) {
                  CheckTypeCharacteristics_Type(p.tok, p.Type, m.IsGhost || p.IsGhost);
                }
                foreach (var p in m.Outs) {
                  CheckTypeCharacteristics_Type(p.tok, p.Type, m.IsGhost || p.IsGhost);
                }
                if (m.Body != null) {
                  CheckTypeCharacteristics_Stmt(m.Body, m.IsGhost);
                }
              }
            }
          }
        }
        // Check that extreme predicates are not recursive with non-extreme-predicate functions (and only
        // with extreme predicates of the same polarity), and
        // check that greatest lemmas are not recursive with non-greatest-lemma methods.
        // Also, check that the constraints of newtypes/subset-types do not depend on the type itself.
        // And check that const initializers are not cyclic.
        var cycleErrorHasBeenReported = new HashSet<ICallable>();
        foreach (var d in declarations) {
          if (d is TopLevelDeclWithMembers { Members: var members }) {
            foreach (var member in members) {
              if (member is ExtremePredicate) {
                var fn = (ExtremePredicate)member;
                // Check here for the presence of any 'ensures' clauses, which are not allowed (because we're not sure
                // of their soundness)
                fn.Req.ForEach(e => ExtremePredicateChecks(e.E, fn, CallingPosition.Positive));
                fn.Decreases.Expressions.ForEach(e => ExtremePredicateChecks(e, fn, CallingPosition.Positive));
                fn.Reads.ForEach(e => ExtremePredicateChecks(e.E, fn, CallingPosition.Positive));
                if (fn.Ens.Count != 0) {
                  reporter.Error(MessageSource.Resolver, fn.Ens[0].E.tok, "a {0} is not allowed to declare any ensures clause", member.WhatKind);
                }
                if (fn.Body != null) {
                  ExtremePredicateChecks(fn.Body, fn, CallingPosition.Positive);
                }
              } else if (member is ExtremeLemma) {
                var m = (ExtremeLemma)member;
                m.Req.ForEach(e => ExtremeLemmaChecks(e.E, m));
                m.Ens.ForEach(e => ExtremeLemmaChecks(e.E, m));
                m.Decreases.Expressions.ForEach(e => ExtremeLemmaChecks(e, m));

                if (m.Body != null) {
                  ExtremeLemmaChecks(m.Body, m);
                }
              } else if (member is ConstantField) {
                var cf = (ConstantField)member;
                if (cf.EnclosingModule.CallGraph.GetSCCSize(cf) != 1) {
                  var r = cf.EnclosingModule.CallGraph.GetSCCRepresentative(cf);
                  if (cycleErrorHasBeenReported.Contains(r)) {
                    // An error has already been reported for this cycle, so don't report another.
                    // Note, the representative, "r", may itself not be a const.
                  } else {
                    ReportCallGraphCycleError(cf, "const definition contains a cycle");
                    cycleErrorHasBeenReported.Add(r);
                  }
                }
              }
            }
          }

          if (d is RedirectingTypeDecl dd) {
            if (d.EnclosingModuleDefinition.CallGraph.GetSCCSize(dd) != 1) {
              var r = d.EnclosingModuleDefinition.CallGraph.GetSCCRepresentative(dd);
              if (cycleErrorHasBeenReported.Contains(r)) {
                // An error has already been reported for this cycle, so don't report another.
                // Note, the representative, "r", may itself not be a const.
              } else if (dd is NewtypeDecl || dd is SubsetTypeDecl) {
                ReportCallGraphCycleError(dd, $"recursive constraint dependency involving a {dd.WhatKind}");
                cycleErrorHasBeenReported.Add(r);
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
        foreach (var cl in ModuleDefinition.AllTypesWithMembers(declarations)) {
          if (!(cl is ClassDecl)) {
            if (!isAnExport && !cl.EnclosingModuleDefinition.IsAbstract) {
              // non-reference types (datatype, newtype, opaque) don't have constructors that can initialize fields
              foreach (var member in cl.Members) {
                if (member is ConstantField f && f.Rhs == null && !f.IsExtern(out _, out _)) {
                  CheckIsOkayWithoutRHS(f);
                }
              }
            }
            continue;
          }
          if (cl is TraitDecl) {
            if (!isAnExport && !cl.EnclosingModuleDefinition.IsAbstract) {
              // traits never have constructors, but check for static consts
              foreach (var member in cl.Members) {
                if (member is ConstantField f && f.IsStatic && f.Rhs == null && !f.IsExtern(out _, out _)) {
                  CheckIsOkayWithoutRHS(f);
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
            } else if (member is ConstantField && member.IsStatic) {
              var f = (ConstantField)member;
              if (!isAnExport && !cl.EnclosingModuleDefinition.IsAbstract && f.Rhs == null && !f.IsExtern(out _, out _)) {
                CheckIsOkayWithoutRHS(f);
              }
            } else if (member is Field && fieldWithoutKnownInitializer == null) {
              var f = (Field)member;
              if (f is ConstantField && ((ConstantField)f).Rhs != null) {
                // fine
              } else if (!f.Type.KnownToHaveToAValue(f.IsGhost)) {
                fieldWithoutKnownInitializer = f;
              }
            }
          }
          if (!hasConstructor) {
            if (fieldWithoutKnownInitializer == null) {
              // time to check inherited members
              foreach (var member in cl.InheritedMembers) {
                if (member is Field) {
                  var f = (Field)member;
                  if (f is ConstantField && ((ConstantField)f).Rhs != null) {
                    // fine
                  } else if (!f.Type.Subst(cl.ParentFormalTypeParametersToActuals).KnownToHaveToAValue(f.IsGhost)) {
                    fieldWithoutKnownInitializer = f;
                    break;
                  }
                }
              }
            }
            // go through inherited members...
            if (fieldWithoutKnownInitializer != null) {
              reporter.Error(MessageSource.Resolver, cl.tok, "class '{0}' with fields without known initializers, like '{1}' of type '{2}', must declare a constructor",
                cl.Name, fieldWithoutKnownInitializer.Name, fieldWithoutKnownInitializer.Type.Subst(cl.ParentFormalTypeParametersToActuals));
            }
          }
        }
      }
      // Verifies that, in all compiled places, subset types in comprehensions have a compilable constraint
      new SubsetConstraintGhostChecker(this.Reporter).Traverse(declarations);
    }

    private void CheckIsOkayWithoutRHS(ConstantField f) {
      if (f.IsGhost && !f.Type.IsNonempty) {
        reporter.Error(MessageSource.Resolver, f.tok,
          "{0}ghost const field '{1}' of type '{2}' (which may be empty) must give a defining value",
          f.IsStatic ? "static " : "", f.Name, f.Type);
      } else if (!f.IsGhost && !f.Type.HasCompilableValue) {
        reporter.Error(MessageSource.Resolver, f.tok,
          "{0}non-ghost const field '{1}' of type '{2}' (which does not have a default compiled value) must give a defining value",
          f.IsStatic ? "static " : "", f.Name, f.Type);
      }
    }

    private void ResolveClassMembers_Pass1(TopLevelDeclWithMembers cl) {
      foreach (var member in cl.Members) {
        var prevErrCnt = reporter.Count(ErrorLevel.Error);
        if (prevErrCnt == reporter.Count(ErrorLevel.Error)) {
          if (member is Method method) {
            CheckForUnnecessaryEqualitySupportDeclarations(method, method.TypeArgs);
            CheckParameterDefaultValuesAreCompilable(method.Ins, method);
            if (method.Body != null) {
              ComputeGhostInterest(method.Body, method.IsGhost, method.IsLemmaLike ? "a " + method.WhatKind : null, method);
              CheckExpression(method.Body, this, method);
              new TailRecursion(reporter).DetermineTailRecursion(method);
            }

          } else if (member is Function function) {
            CheckForUnnecessaryEqualitySupportDeclarations(function, function.TypeArgs);
            CheckParameterDefaultValuesAreCompilable(function.Formals, function);
            if (function.ByMethodBody == null) {
              if (!function.IsGhost && function.Body != null) {
                ExpressionTester.CheckIsCompilable(this, function.Body, function);
              }
              if (function.Body != null) {
                new TailRecursion(reporter).DetermineTailRecursion(function);
              }
            } else {
              var m = function.ByMethodDecl;
              if (m != null) {
                Contract.Assert(!m.IsGhost);
                ComputeGhostInterest(m.Body, false, null, m);
                CheckExpression(m.Body, this, m);
                new TailRecursion(reporter).DetermineTailRecursion(m);
              } else {
                // m should not be null, unless an error has been reported
                // (e.g. function-by-method and method with the same name) 
                Contract.Assert(reporter.ErrorCount > 0);
              }
            }

          } else if (member is ConstantField field && field.Rhs != null && !field.IsGhost) {
            ExpressionTester.CheckIsCompilable(this, field.Rhs, field);
          }

          if (prevErrCnt == reporter.Count(ErrorLevel.Error) && member is ICodeContext) {
            member.SubExpressions.Iter(e => CheckExpression(e, this, (ICodeContext)member));
          }
        }
      }
    }

    void CheckForUnnecessaryEqualitySupportDeclarations(MemberDecl member, List<TypeParameter> typeParameters) {
      if (member.IsGhost) {
        foreach (var p in typeParameters.Where(p => p.SupportsEquality)) {
          reporter.Warning(MessageSource.Resolver, ErrorID.None, p.tok,
            $"type parameter {p.Name} of ghost {member.WhatKind} {member.Name} is declared (==), which is unnecessary because the {member.WhatKind} doesn't contain any compiled code");
        }
      }
    }

    /// <summary>
    /// Check that default-value expressions are compilable, for non-ghost formals.
    /// </summary>
    void CheckParameterDefaultValuesAreCompilable(List<Formal> formals, ICodeContext codeContext) {
      Contract.Requires(formals != null);

      foreach (var formal in formals.Where(f => f.DefaultValue != null)) {
        if ((!codeContext.IsGhost || codeContext is DatatypeDecl) && !formal.IsGhost) {
          ExpressionTester.CheckIsCompilable(this, formal.DefaultValue, codeContext);
        }
        CheckExpression(formal.DefaultValue, this, codeContext);
      }
    }

    void ReportCallGraphCycleError(ICallable start, string msg) {
      Contract.Requires(start != null);
      Contract.Requires(msg != null);
      var scc = start.EnclosingModule.CallGraph.GetSCC(start);
      scc.Reverse();
      var startIndex = scc.IndexOf(start);
      Contract.Assert(0 <= startIndex);
      scc = Util.Concat(scc.GetRange(startIndex, scc.Count - startIndex), scc.GetRange(0, startIndex));
      ReportCycleError(scc, c => c.Tok, c => c.NameRelativeToModule, msg);
    }

    void ReportCycleError<X>(List<X> cycle, Func<X, IToken> toTok, Func<X, string> toString, string msg) {
      Contract.Requires(cycle != null);
      Contract.Requires(cycle.Count != 0);
      Contract.Requires(toTok != null);
      Contract.Requires(toString != null);
      Contract.Requires(msg != null);

      var start = cycle[0];
      var cy = Util.Comma(" -> ", cycle, toString);
      reporter.Error(MessageSource.Resolver, toTok(start), $"{msg}: {cy} -> {toString(start)}");
    }

    public BigInteger MaxBV(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(t.IsBitVectorType);
      return MaxBV(t.AsBitVectorType.Width);
    }

    public BigInteger MaxBV(int bits) {
      Contract.Requires(0 <= bits);
      return BigInteger.Pow(new BigInteger(2), bits) - BigInteger.One;
    }

    private void FigureOutNativeType(NewtypeDecl dd) {
      Contract.Requires(dd != null);

      // Look at the :nativeType attribute, if any
      bool mustUseNativeType;
      List<NativeType> nativeTypeChoices = null;  // null means "no preference"
      var args = Attributes.FindExpressions(dd.Attributes, "nativeType");
      if (args != null && !dd.BaseType.IsNumericBased(Type.NumericPersuasion.Int)) {
        reporter.Error(MessageSource.Resolver, dd, ":nativeType can only be used on integral types");
        return;
      } else if (args == null) {
        // There was no :nativeType attribute
        mustUseNativeType = false;
      } else if (args.Count == 0) {
        mustUseNativeType = true;
      } else {
        var arg0Lit = args[0] as LiteralExpr;
        if (arg0Lit != null && arg0Lit.Value is bool) {
          if (!(bool)arg0Lit.Value) {
            // {:nativeType false} says "don't use native type", so our work here is done
            return;
          }
          mustUseNativeType = true;
        } else {
          mustUseNativeType = true;
          nativeTypeChoices = new List<NativeType>();
          foreach (var arg in args) {
            if (arg is LiteralExpr lit && lit.Value is string s) {
              // Get the NativeType for "s"
              foreach (var nativeT in NativeTypes) {
                if (nativeT.Name == s) {
                  nativeTypeChoices.Add(nativeT);
                  goto FoundNativeType;
                }
              }
              reporter.Error(MessageSource.Resolver, dd, ":nativeType '{0}' not known", s);
              return;
            FoundNativeType:;
            } else {
              reporter.Error(MessageSource.Resolver, arg, "unexpected :nativeType argument");
              return;
            }
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
      List<ComprehensionExpr.BoundedPool> bounds;
      if (ddVar == null) {
        // There are no bounds at all
        bounds = new List<ComprehensionExpr.BoundedPool>();
      } else {
        bounds = DiscoverAllBounds_SingleVar(ddVar, ddConstraint);
      }

      // Returns null if the argument is a constrained newtype (recursively)
      // Returns the transitive base type if the argument is recusively unconstrained
      Type AsUnconstrainedType(Type t) {
        while (true) {
          if (t.AsNewtype == null) {
            return t;
          }

          if (t.AsNewtype.Constraint != null) {
            return null;
          }

          t = t.AsNewtype.BaseType;
        }
      }

      // Find which among the allowable native types can hold "dd". Give an
      // error for any user-specified native type that's not big enough.
      var bigEnoughNativeTypes = new List<NativeType>();
      // But first, define a local, recursive function GetConst/GetAnyConst:
      // These fold any constant computations, including symbolic constants,
      // returning null if folding is not possible. If an operation is undefined
      // (divide by zero, conversion out of range, etc.), then null is returned.
      Func<Expression, BigInteger?> GetConst = null;
      Func<Expression, Stack<ConstantField>, Object> GetAnyConst = null;
      GetAnyConst = (Expression e, Stack<ConstantField> consts) => {
        if (e is LiteralExpr l) {
          return l.Value;
        } else if (e is UnaryOpExpr un) {
          if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot && GetAnyConst(un.E, consts) is bool b) {
            return !b;
          }
          if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BVNot && GetAnyConst(un.E, consts) is BigInteger i) {
            return ((BigInteger.One << un.Type.AsBitVectorType.Width) - 1) ^ i;
          }
          // TODO: This only handles strings; generalize to other collections?
          if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.SeqLength && GetAnyConst(un.E, consts) is string ss) {
            return (BigInteger)(ss.Length);
          }
        } else if (e is MemberSelectExpr m) {
          if (m.Member is ConstantField c && c.IsStatic && c.Rhs != null) {
            // This aspect of type resolution happens before the check for cyclic references
            // so we have to do a check here as well. If cyclic, null is silently returned,
            // counting on the later error message to alert the user.
            if (consts.Contains(c)) { return null; }
            consts.Push(c);
            Object o = GetAnyConst(c.Rhs, consts);
            consts.Pop();
            return o;
          } else if (m.Member is SpecialField sf) {
            string nm = sf.Name;
            if (nm == "Floor") {
              Object ee = GetAnyConst(m.Obj, consts);
              if (ee != null && m.Obj.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
                ((BaseTypes.BigDec)ee).FloorCeiling(out var f, out _);
                return f;
              }
            }
          }
        } else if (e is BinaryExpr bin) {
          Object e0 = GetAnyConst(bin.E0, consts);
          Object e1 = GetAnyConst(bin.E1, consts);
          bool isBool = bin.E0.Type == Type.Bool && bin.E1.Type == Type.Bool;
          bool shortCircuit = isBool && (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And
                                         || bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or
                                         || bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp);

          if (e0 == null || (!shortCircuit && e1 == null)) { return null; }
          bool isAnyReal = bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Real)
                        && bin.E1.Type.IsNumericBased(Type.NumericPersuasion.Real);
          bool isAnyInt = bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Int)
                       && bin.E1.Type.IsNumericBased(Type.NumericPersuasion.Int);
          bool isReal = bin.Type.IsRealType;
          bool isInt = bin.Type.IsIntegerType;
          bool isBV = bin.E0.Type.IsBitVectorType;
          int width = isBV ? bin.E0.Type.AsBitVectorType.Width : 0;
          bool isString = e0 is string && e1 is string;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Add:
              if (isInt) {
                return (BigInteger)e0 + (BigInteger)e1;
              }

              if (isBV) {
                return ((BigInteger)e0 + (BigInteger)e1) & MaxBV(bin.Type);
              }

              if (isReal) {
                return (BaseTypes.BigDec)e0 + (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.Concat:
              if (isString) {
                return (string)e0 + (string)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.Sub:
              if (isInt) {
                return (BigInteger)e0 - (BigInteger)e1;
              }

              if (isBV) {
                return ((BigInteger)e0 - (BigInteger)e1) & MaxBV(bin.Type);
              }

              if (isReal) {
                return (BaseTypes.BigDec)e0 - (BaseTypes.BigDec)e1;
              }
              // Allow a special case: If the result type is a newtype that is integer-based (i.e., isInt && !isInteger)
              // then we generally do not fold the operations, because we do not determine whether the
              // result of the operation satisfies the new type constraint. However, on the occasion that
              // a newtype aliases int without a constraint, it occurs that a value of the newtype is initialized
              // with a negative value, which is represented as "0 - N", that is, it comes to this case. It
              // is a nuisance not to constant-fold the result, as not doing so can alter the determination
              // of the representation type.
              if (isAnyInt && AsUnconstrainedType(bin.Type) != null) {
                return ((BigInteger)e0) - ((BigInteger)e1);
              }
              break;
            case BinaryExpr.ResolvedOpcode.Mul:
              if (isInt) {
                return (BigInteger)e0 * (BigInteger)e1;
              }

              if (isBV) {
                return ((BigInteger)e0 * (BigInteger)e1) & MaxBV(bin.Type);
              }

              if (isReal) {
                return (BaseTypes.BigDec)e0 * (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.BitwiseAnd:
              Contract.Assert(isBV);
              return (BigInteger)e0 & (BigInteger)e1;
            case BinaryExpr.ResolvedOpcode.BitwiseOr:
              Contract.Assert(isBV);
              return (BigInteger)e0 | (BigInteger)e1;
            case BinaryExpr.ResolvedOpcode.BitwiseXor:
              Contract.Assert(isBV);
              return (BigInteger)e0 ^ (BigInteger)e1;
            case BinaryExpr.ResolvedOpcode.Div:
              if (isInt) {
                if ((BigInteger)e1 == 0) {
                  return null; // Divide by zero
                } else {
                  BigInteger a0 = (BigInteger)e0;
                  BigInteger a1 = (BigInteger)e1;
                  BigInteger d = a0 / a1;
                  return a0 >= 0 || a0 == d * a1 ? d : a1 > 0 ? d - 1 : d + 1;
                }
              }
              if (isBV) {
                if ((BigInteger)e1 == 0) {
                  return null; // Divide by zero
                } else {
                  return ((BigInteger)e0) / ((BigInteger)e1);
                }
              }
              if (isReal) {
                if ((BaseTypes.BigDec)e1 == BaseTypes.BigDec.ZERO) {
                  return null; // Divide by zero
                } else {
                  // BigDec does not have divide and is not a representation of rationals, so we don't do constant folding
                  return null;
                }
              }

              break;
            case BinaryExpr.ResolvedOpcode.Mod:
              if (isInt) {
                if ((BigInteger)e1 == 0) {
                  return null; // Mod by zero
                } else {
                  BigInteger a = BigInteger.Abs((BigInteger)e1);
                  BigInteger d = (BigInteger)e0 % a;
                  return (BigInteger)e0 >= 0 ? d : d + a;
                }
              }
              if (isBV) {
                if ((BigInteger)e1 == 0) {
                  return null; // Mod by zero
                } else {
                  return (BigInteger)e0 % (BigInteger)e1;
                }
              }
              break;
            case BinaryExpr.ResolvedOpcode.LeftShift: {
                if ((BigInteger)e1 < 0) {
                  return null; // Negative shift
                }
                if ((BigInteger)e1 > bin.Type.AsBitVectorType.Width) {
                  return null; // Shift is too large
                }
                return ((BigInteger)e0 << (int)(BigInteger)e1) & MaxBV(bin.E0.Type);
              }
            case BinaryExpr.ResolvedOpcode.RightShift: {
                if ((BigInteger)e1 < 0) {
                  return null; // Negative shift
                }
                if ((BigInteger)e1 > bin.Type.AsBitVectorType.Width) {
                  return null; // Shift too large
                }
                return (BigInteger)e0 >> (int)(BigInteger)e1;
              }
            case BinaryExpr.ResolvedOpcode.And: {
                if ((bool)e0 && e1 == null) {
                  return null;
                }

                return (bool)e0 && (bool)e1;
              }
            case BinaryExpr.ResolvedOpcode.Or: {
                if (!(bool)e0 && e1 == null) {
                  return null;
                }

                return (bool)e0 || (bool)e1;
              }
            case BinaryExpr.ResolvedOpcode.Imp: { // ==> and <==
                if ((bool)e0 && e1 == null) {
                  return null;
                }

                return !(bool)e0 || (bool)e1;
              }
            case BinaryExpr.ResolvedOpcode.Iff: return (bool)e0 == (bool)e1; // <==>
            case BinaryExpr.ResolvedOpcode.Gt:
              if (isAnyInt) {
                return (BigInteger)e0 > (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 > (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 > (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.GtChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] > ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.Ge:
              if (isAnyInt) {
                return (BigInteger)e0 >= (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 >= (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 >= (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.GeChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] >= ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.Lt:
              if (isAnyInt) {
                return (BigInteger)e0 < (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 < (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 < (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.LtChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] < ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.ProperPrefix:
              if (isString) {
                return ((string)e1).StartsWith((string)e0) && !((string)e1).Equals((string)e0);
              }

              break;
            case BinaryExpr.ResolvedOpcode.Le:
              if (isAnyInt) {
                return (BigInteger)e0 <= (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 <= (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 <= (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.LeChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] <= ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.Prefix:
              if (isString) {
                return ((string)e1).StartsWith((string)e0);
              }

              break;
            case BinaryExpr.ResolvedOpcode.EqCommon: {
                if (isBool) {
                  return (bool)e0 == (bool)e1;
                } else if (isAnyInt || isBV) {
                  return (BigInteger)e0 == (BigInteger)e1;
                } else if (isAnyReal) {
                  return (BaseTypes.BigDec)e0 == (BaseTypes.BigDec)e1;
                } else if (bin.E0.Type.IsCharType) {
                  return ((string)e0)[0] == ((string)e1)[0];
                }
                break;
              }
            case BinaryExpr.ResolvedOpcode.SeqEq:
              if (isString) {
                return (string)e0 == (string)e1;
              }
              break;
            case BinaryExpr.ResolvedOpcode.SeqNeq:
              if (isString) {
                return (string)e0 != (string)e1;
              }
              break;
            case BinaryExpr.ResolvedOpcode.NeqCommon: {
                if (isBool) {
                  return (bool)e0 != (bool)e1;
                } else if (isAnyInt || isBV) {
                  return (BigInteger)e0 != (BigInteger)e1;
                } else if (isAnyReal) {
                  return (BaseTypes.BigDec)e0 != (BaseTypes.BigDec)e1;
                } else if (bin.E0.Type.IsCharType) {
                  return ((string)e0)[0] != ((string)e1)[0];
                } else if (isString) {
                  return (string)e0 != (string)e1;
                }
                break;
              }
          }
        } else if (e is ConversionExpr ce) {
          object o = GetAnyConst(ce.E, consts);
          if (o == null || ce.E.Type == ce.Type) {
            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsBitVectorType) {
            ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
            if (ff < 0 || ff > MaxBV(ce.Type)) {
              return null; // Out of range
            }
            if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
              return null; // Out of range
            }
            return ff;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
              return null; // Argument not an integer
            }
            return ff;
          }

          if (ce.E.Type.IsBitVectorType &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return o;
          }

          if (ce.E.Type.IsBitVectorType &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return BaseTypes.BigDec.FromBigInt((BigInteger)o);
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) &&
                ce.Type.IsBitVectorType) {
            BigInteger b = (BigInteger)o;
            if (b < 0 || b > MaxBV(ce.Type)) {
              return null; // Argument out of range
            }
            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            // This case includes int-based newtypes to int-based new types
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            // This case includes real-based newtypes to real-based new types
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return o;
          }

          if (ce.E.Type.IsBitVectorType && ce.Type.IsBitVectorType) {
            BigInteger b = (BigInteger)o;
            if (b < 0 || b > MaxBV(ce.Type)) {
              return null; // Argument out of range
            }
            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return BaseTypes.BigDec.FromBigInt((BigInteger)o);
          }

          if (ce.E.Type.IsCharType && ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            char c = ((String)o)[0];
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return new BigInteger(((string)o)[0]);
          }

          if (ce.E.Type.IsCharType && ce.Type.IsBitVectorType) {
            char c = ((String)o)[0];
            if ((int)c > MaxBV(ce.Type)) {
              return null; // Argument out of range
            }
            return new BigInteger(((string)o)[0]);
          }

          if ((ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || ce.E.Type.IsBitVectorType) &&
                ce.Type.IsCharType) {
            BigInteger b = (BigInteger)o;
            if (b < BigInteger.Zero || b > new BigInteger(65535)) {
              return null; // Argument out of range
            }
            return ((char)(int)b).ToString();
          }

          if (ce.E.Type.IsCharType &&
              ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return BaseTypes.BigDec.FromInt(((string)o)[0]);
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsCharType) {
            ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
            if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
              return null; // Argument not an integer
            }
            if (ff < BigInteger.Zero || ff > new BigInteger(65535)) {
              return null; // Argument out of range
            }
            return ((char)(int)ff).ToString();
          }

        } else if (e is SeqSelectExpr sse) {
          var b = GetAnyConst(sse.Seq, consts) as string;
          BigInteger index = (BigInteger)GetAnyConst(sse.E0, consts);
          if (b == null) {
            return null;
          }

          if (index < 0 || index >= b.Length || index > Int32.MaxValue) {
            return null; // Index out of range
          }
          return b[(int)index].ToString();
        } else if (e is ITEExpr ite) {
          Object b = GetAnyConst(ite.Test, consts);
          if (b == null) {
            return null;
          }

          return ((bool)b) ? GetAnyConst(ite.Thn, consts) : GetAnyConst(ite.Els, consts);
        } else if (e is ConcreteSyntaxExpression n) {
          return GetAnyConst(n.ResolvedExpression, consts);
        } else {
          return null;
        }
        return null;
      };
      GetConst = (Expression e) => {
        Object ee = GetAnyConst(e.Resolved ?? e, new Stack<ConstantField>());
        return ee as BigInteger?;
      };
      // Now, then, let's go through them types.
      // FIXME - should first go through the bounds to find the most constraining values
      // then check those values against the possible types. Note that also presumes the types are in order.
      BigInteger? lowest = null;
      BigInteger? highest = null;
      foreach (var bound in bounds) {
        if (bound is ComprehensionExpr.IntBoundedPool) {
          var bnd = (ComprehensionExpr.IntBoundedPool)bound;
          if (bnd.LowerBound != null) {
            BigInteger? lower = GetConst(bnd.LowerBound);
            if (lower != null && (lowest == null || lower < lowest)) {
              lowest = lower;
            }
          }
          if (bnd.UpperBound != null) {
            BigInteger? upper = GetConst(bnd.UpperBound);
            if (upper != null && (highest == null || upper > highest)) {
              highest = upper;
            }
          }
        }
      }
      foreach (var nativeT in nativeTypeChoices ?? NativeTypes) {
        bool lowerOk = (lowest != null && nativeT.LowerBound <= lowest);
        bool upperOk = (highest != null && nativeT.UpperBound >= highest);
        if (lowerOk && upperOk) {
          bigEnoughNativeTypes.Add(nativeT);
        } else if (nativeTypeChoices != null) {
          reporter.Error(MessageSource.Resolver, dd,
            "Dafny's heuristics failed to confirm '{0}' to be a compatible native type.  " +
            "Hint: try writing a newtype constraint of the form 'i:int | lowerBound <= i < upperBound && (...any additional constraints...)'",
            nativeT.Name);
          return;
        }
      }

      // Finally, of the big-enough native types, pick the first one that is
      // supported by the selected target compiler.
      foreach (var nativeT in bigEnoughNativeTypes) {
        if (DafnyOptions.O.Backend.SupportedNativeTypes.Contains(nativeT.Name)) {
          dd.NativeType = nativeT;
          break;
        }
      }
      if (dd.NativeType != null) {
        // Give an info message saying which type was selected--unless the user requested
        // one particular native type, in which case that must have been the one picked.
        if (nativeTypeChoices != null && nativeTypeChoices.Count == 1) {
          Contract.Assert(dd.NativeType == nativeTypeChoices[0]);
        } else {
          reporter.Info(MessageSource.Resolver, dd.tok, "newtype " + dd.Name + " resolves as {:nativeType \"" + dd.NativeType.Name + "\"} (Detected Range: " + lowest + " .. " + highest + ")");
        }
      } else if (nativeTypeChoices != null) {
        reporter.Error(MessageSource.Resolver, dd,
          "None of the types given in :nativeType arguments is supported by the current compilation target. Try supplying others.");
      } else if (mustUseNativeType) {
        reporter.Error(MessageSource.Resolver, dd,
          "Dafny's heuristics cannot find a compatible native type.  " +
          "Hint: try writing a newtype constraint of the form 'i:int | lowerBound <= i < upperBound && (...any additional constraints...)'");
      }
    }

    /// <summary>
    /// Check that the 'older' modifier on parameters is used correctly and report any errors of the contrary.
    /// </summary>
    void CheckOlderParameters(Function f) {
      Contract.Requires(f != null);

      if (!f.ResultType.IsBoolType || f is PrefixPredicate || f is ExtremePredicate) {
        // parameters are not allowed to be marked 'older'
        foreach (var formal in f.Formals) {
          if (formal.IsOlder) {
            reporter.Error(MessageSource.Resolver, formal.tok, "only predicates and two-state predicates are allowed 'older' parameters");
          }
        }
      }
    }

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
    /// checks for hint restrictions in any CalcStmt. In any ghost context, it also
    /// changes the bound variables of all let- and let-such-that expressions to ghost.
    /// It also performs substitutions in DefaultValueExpression's.
    /// </summary>
    void CheckExpression(Statement stmt, Resolver resolver, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolver != null);
      Contract.Requires(codeContext != null);
      var v = new CheckExpression_Visitor(resolver, codeContext);
      v.Visit(stmt);
    }
    class CheckExpression_Visitor : ResolverBottomUpVisitor {
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
          resolver.ComputeGhostInterest(e.S, true, "a statement expression", CodeContext);
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          if (CodeContext.IsGhost) {
            foreach (var bv in e.BoundVars) {
              bv.MakeGhost();
            }
          }
        }
      }

      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is CalcStmt calc) {
          foreach (var h in calc.Hints) {
            resolver.CheckLocalityUpdates(h, new HashSet<LocalVariable>(), "a hint");
          }
        } else if (stmt is AssertStmt astmt && astmt.Proof != null) {
          resolver.CheckLocalityUpdates(astmt.Proof, new HashSet<LocalVariable>(), "an assert-by body");
        } else if (stmt is ForallStmt forall && forall.Body != null) {
          resolver.CheckLocalityUpdates(forall.Body, new HashSet<LocalVariable>(), "a forall statement");
        }
      }
    }
    #endregion

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

    public class FuelAdjustment_Context {
      public ModuleDefinition currentModule;
      public FuelAdjustment_Context(ModuleDefinition currentModule) {
        this.currentModule = currentModule;
      }
    }

    class FuelAdjustment_Visitor : ResolverTopDownVisitor<FuelAdjustment_Context> {
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
    // ----- ExtremePredicateChecks -------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region ExtremePredicateChecks
    enum CallingPosition { Positive, Negative, Neither }
    static CallingPosition Invert(CallingPosition cp) {
      switch (cp) {
        case CallingPosition.Positive: return CallingPosition.Negative;
        case CallingPosition.Negative: return CallingPosition.Positive;
        default: return CallingPosition.Neither;
      }
    }

    class FindFriendlyCalls_Visitor : ResolverTopDownVisitor<CallingPosition> {
      public readonly bool IsCoContext;
      public readonly bool ContinuityIsImportant;
      public FindFriendlyCalls_Visitor(Resolver resolver, bool co, bool continuityIsImportant)
        : base(resolver) {
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
        } else if (expr is NestedMatchExpr) {
          var e = (NestedMatchExpr)expr;
          Visit(e.Source, CallingPosition.Neither);
          var theCp = cp;
          e.Cases.Iter(kase => Visit(kase.Body, theCp));
          return false;
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
            // a let-such-that expression introduces an existential that may depend on the _k in a least/greatest predicate, so we disallow recursive calls in the body of the let-such-that
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
                // To ensure continuity of extreme predicates, don't allow calls under an existential (resp. universal) quantifier
                // for greatest (resp. least) predicates).
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

    void KNatMismatchError(IToken tok, string contextName, ExtremePredicate.KType contextK, ExtremePredicate.KType calleeK) {
      var hint = contextK == ExtremePredicate.KType.Unspecified ? string.Format(" (perhaps try declaring '{0}' as '{0}[nat]')", contextName) : "";
      reporter.Error(MessageSource.Resolver, tok,
        "this call does not type check, because the context uses a _k parameter of type {0} whereas the callee uses a _k parameter of type {1}{2}",
        contextK == ExtremePredicate.KType.Nat ? "nat" : "ORDINAL",
        calleeK == ExtremePredicate.KType.Nat ? "nat" : "ORDINAL",
        hint);
    }

    class ExtremePredicateChecks_Visitor : FindFriendlyCalls_Visitor {
      readonly ExtremePredicate context;
      public ExtremePredicateChecks_Visitor(Resolver resolver, ExtremePredicate context)
        : base(resolver, context is GreatestPredicate, context.KNat) {
        Contract.Requires(resolver != null);
        Contract.Requires(context != null);
        this.context = context;
      }
      protected override bool VisitOneExpr(Expression expr, ref CallingPosition cp) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          if (ModuleDefinition.InSameSCC(context, e.Function)) {
            // we're looking at a recursive call
            if (!(context is LeastPredicate ? e.Function is LeastPredicate : e.Function is GreatestPredicate)) {
              resolver.reporter.Error(MessageSource.Resolver, e, "a recursive call from a {0} can go only to other {0}s", context.WhatKind);
            } else if (context.KNat != ((ExtremePredicate)e.Function).KNat) {
              resolver.KNatMismatchError(e.tok, context.Name, context.TypeOfK, ((ExtremePredicate)e.Function).TypeOfK);
            } else if (cp != CallingPosition.Positive) {
              var msg = string.Format("a {0} can be called recursively only in positive positions", context.WhatKind);
              if (ContinuityIsImportant && cp == CallingPosition.Neither) {
                // this may be inside an non-friendly quantifier
                msg += string.Format(" and cannot sit inside an unbounded {0} quantifier", context is LeastPredicate ? "universal" : "existential");
              } else {
                // we don't care about the continuity restriction or
                // the extreme-call is not inside an quantifier, so don't bother mentioning the part of existentials/universals in the error message
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
            resolver.reporter.Error(MessageSource.Resolver, stmt.Tok, "a recursive call from a {0} can go only to other {0}s", context.WhatKind);
          }
          // do the sub-parts with the same "cp"
          return true;
        } else {
          return base.VisitOneStmt(stmt, ref st);
        }
      }
    }

    void ExtremePredicateChecks(Expression expr, ExtremePredicate context, CallingPosition cp) {
      Contract.Requires(expr != null);
      Contract.Requires(context != null);
      var v = new ExtremePredicateChecks_Visitor(this, context);
      v.Visit(expr, cp);
    }
    #endregion ExtremePredicateChecks

    // ------------------------------------------------------------------------------------------------------
    // ----- ExtremeLemmaChecks -----------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region ExtremeLemmaChecks
    class ExtremeLemmaChecks_Visitor : ResolverBottomUpVisitor {
      ExtremeLemma context;
      public ExtremeLemmaChecks_Visitor(Resolver resolver, ExtremeLemma context)
        : base(resolver) {
        Contract.Requires(resolver != null);
        Contract.Requires(context != null);
        this.context = context;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          if (s.Method is ExtremeLemma || s.Method is PrefixLemma) {
            // all is cool
          } else {
            // the call goes from an extreme lemma context to a non-extreme-lemma callee
            if (ModuleDefinition.InSameSCC(context, s.Method)) {
              // we're looking at a recursive call (to a non-extreme-lemma)
              resolver.reporter.Error(MessageSource.Resolver, s.Tok, "a recursive call from a {0} can go only to other {0}s and prefix lemmas", context.WhatKind);
            }
          }
        }
      }
      protected override void VisitOneExpr(Expression expr) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          // the call goes from a greatest lemma context to a non-greatest-lemma callee
          if (ModuleDefinition.InSameSCC(context, e.Function)) {
            // we're looking at a recursive call (to a non-greatest-lemma)
            resolver.reporter.Error(MessageSource.Resolver, e.tok, "a recursive call from a greatest lemma can go only to other greatest lemmas and prefix lemmas");
          }
        }
      }
    }
    void ExtremeLemmaChecks(Statement stmt, ExtremeLemma context) {
      Contract.Requires(stmt != null);
      Contract.Requires(context != null);
      var v = new ExtremeLemmaChecks_Visitor(this, context);
      v.Visit(stmt);
    }
    void ExtremeLemmaChecks(Expression expr, ExtremeLemma context) {
      Contract.Requires(context != null);
      if (expr == null) {
        return;
      }

      var v = new ExtremeLemmaChecks_Visitor(this, context);
      v.Visit(expr);
    }
    #endregion ExtremeLemmaChecks

    // ------------------------------------------------------------------------------------------------------
    // ----- CheckTypeCharacteristics -----------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region CheckTypeCharacteristics
    void CheckTypeCharacteristics_Stmt(Statement stmt, bool isGhost) {
      Contract.Requires(stmt != null);
      var v = new CheckTypeCharacteristics_Visitor(this);
      v.Visit(stmt, isGhost);
    }
    void CheckTypeCharacteristics_Expr(Expression expr, bool isGhost) {
      Contract.Requires(expr != null);
      var v = new CheckTypeCharacteristics_Visitor(this);
      v.Visit(expr, isGhost);
    }
    public void CheckTypeCharacteristics_Type(IToken tok, Type type, bool isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      var v = new CheckTypeCharacteristics_Visitor(this);
      v.VisitType(tok, type, isGhost);
    }

    /// <summary>
    /// This visitor checks that type characteristics are respected in all (implicitly or explicitly)
    /// declared types. Note that equality-support is checked only in compiled contexts.
    /// In addition, this visitor checks that operations that require equality are applied to
    /// types that really do support equality; this, too, is checked only in compiled contexts.
    /// </summary>
    class CheckTypeCharacteristics_Visitor : ResolverTopDownVisitor<bool> {
      public CheckTypeCharacteristics_Visitor(Resolver resolver)
        : base(resolver) {
        Contract.Requires(resolver != null);
      }
      protected override bool VisitOneStmt(Statement stmt, ref bool inGhostContext) {
        if (stmt.IsGhost) {
          inGhostContext = true;
        }
        // In the sequel, do two things:
        //  * Call VisitType on any type that occurs in the statement
        //  * If the statement introduces ghost components, handle those components here
        //    rather than letting the default visitor handle them
        if (stmt is VarDeclStmt) {
          var s = (VarDeclStmt)stmt;
          foreach (var v in s.Locals) {
            VisitType(v.Tok, v.Type, inGhostContext || v.IsGhost);
          }
        } else if (stmt is VarDeclPattern) {
          var s = (VarDeclPattern)stmt;
          foreach (var v in s.LocalVars) {
            VisitType(v.Tok, v.Type, inGhostContext || v.IsGhost);
          }
        } else if (stmt is AssignStmt) {
          var s = (AssignStmt)stmt;
          if (s.Rhs is TypeRhs tRhs) {
            VisitType(tRhs.Tok, tRhs.Type, inGhostContext);
          }
        } else if (stmt is AssignSuchThatStmt) {
          var s = (AssignSuchThatStmt)stmt;
          Visit(Attributes.SubExpressions(s.Attributes), true);
          Visit(s.Expr, inGhostContext);
          foreach (var lhs in s.Lhss) {
            Visit(lhs, inGhostContext);
          }
          return false;
        } else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          // all subexpressions are ghost, except the guard
          Visit(s.LoopSpecificationExpressions, true);
          if (s.Guard != null) {
            Visit(s.Guard, inGhostContext);
          }
          Visit(s.SubStatements, inGhostContext);
          return false;
        } else if (stmt is AlternativeLoopStmt) {
          var s = (AlternativeLoopStmt)stmt;
          // all subexpressions are ghost, except the guards
          Visit(s.LoopSpecificationExpressions, true);
          foreach (var alt in s.Alternatives) {
            Visit(alt.Guard, inGhostContext);
          }
          Visit(s.SubStatements, inGhostContext);
          return false;
        } else if (stmt is ForLoopStmt) {
          var s = (ForLoopStmt)stmt;
          // all subexpressions are ghost, except the bounds
          Visit(s.LoopSpecificationExpressions, true);
          Visit(s.Start, inGhostContext);
          if (s.End != null) {
            Visit(s.End, inGhostContext);
          }
          Visit(s.SubStatements, inGhostContext);
          return false;
        } else if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          CheckTypeInstantiation(s.Tok, s.Method.WhatKind, s.Method.Name, s.Method.TypeArgs, s.MethodSelect.TypeApplication_JustMember, inGhostContext);
          // recursively visit all subexpressions, noting that some of them may correspond to ghost formal parameters
          Contract.Assert(s.Lhs.Count == s.Method.Outs.Count);
          for (var i = 0; i < s.Method.Outs.Count; i++) {
            Visit(s.Lhs[i], inGhostContext || s.Method.Outs[i].IsGhost);
          }
          Visit(s.Receiver, inGhostContext);
          Contract.Assert(s.Args.Count == s.Method.Ins.Count);
          for (var i = 0; i < s.Method.Ins.Count; i++) {
            Visit(s.Args[i], inGhostContext || s.Method.Ins[i].IsGhost);
          }
          return false;
        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          foreach (var v in s.BoundVars) {
            VisitType(v.Tok, v.Type, inGhostContext);
          }
          // do substatements and subexpressions, noting that ensures clauses are ghost
          Visit(Attributes.SubExpressions(s.Attributes), true);
          if (s.Range != null) {
            Visit(s.Range, inGhostContext);
          }
          foreach (var ee in s.Ens) {
            Visit(Attributes.SubExpressions(ee.Attributes), true);
            Visit(ee.E, true);
          }
          Visit(s.SubStatements, inGhostContext);
          return false;
        } else if (stmt is ExpectStmt) {
          var s = (ExpectStmt)stmt;
          Visit(Attributes.SubExpressions(s.Attributes), true);
          Visit(s.Expr, inGhostContext);
          if (s.Message != null) {
            Visit(s.Message, inGhostContext);
          }
          return false;
        }
        return true;
      }

      protected override bool VisitOneExpr(Expression expr, ref bool inGhostContext) {
        // Do two things:
        //  * Call VisitType on any type that occurs in the statement
        //  * If the expression introduces ghost components, handle those components here
        //    rather than letting the default visitor handle them
        if (expr is BinaryExpr && !inGhostContext) {
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
              } else if (!t0.PartiallySupportsEquality) {
                resolver.reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
              } else if (!t1.PartiallySupportsEquality) {
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
            VisitType(bv.tok, bv.Type, inGhostContext);
          }
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          Visit(Attributes.SubExpressions(e.Attributes), true);
          if (e.Exact) {
            Contract.Assert(e.LHSs.Count == e.RHSs.Count);
            for (var i = 0; i < e.LHSs.Count; i++) {
              // The VisitPattern function visits all BoundVar's in a pattern and returns
              // "true" if all variables are ghost.
              bool VisitPattern(CasePattern<BoundVar> pat, bool patternGhostContext) {
                if (pat.Var != null) {
                  VisitType(pat.tok, pat.Var.Type, patternGhostContext || pat.Var.IsGhost);
                  return pat.Var.IsGhost;
                } else {
                  var allGhost = true;
                  Contract.Assert(pat.Ctor != null);
                  Contract.Assert(pat.Ctor.Formals.Count == pat.Arguments.Count);
                  for (var i = 0; i < pat.Ctor.Formals.Count; i++) {
                    var formal = pat.Ctor.Formals[i];
                    var arg = pat.Arguments[i];
                    // don't use short-circuit booleans in the following line, because we want to visit all nested patterns
                    allGhost &= VisitPattern(arg, patternGhostContext || formal.IsGhost);
                  }
                  return allGhost;
                }
              }

              var allGhosts = VisitPattern(e.LHSs[i], inGhostContext);
              Visit(e.RHSs[i], inGhostContext || allGhosts);
            }
          } else {
            Contract.Assert(e.RHSs.Count == 1);
            var allGhost = true;
            foreach (var bv in e.BoundVars) {
              if (!bv.IsGhost) {
                allGhost = false;
              }
              VisitType(bv.tok, bv.Type, inGhostContext || bv.IsGhost);
            }
            Visit(e.RHSs[0], inGhostContext || allGhost);
          }
          Visit(e.Body, inGhostContext);
          return false;
        } else if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          if (e.Member is Function || e.Member is Method) {
            CheckTypeInstantiation(e.tok, e.Member.WhatKind, e.Member.Name, ((ICallable)e.Member).TypeArgs, e.TypeApplication_JustMember, inGhostContext);
          }
        } else if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          CheckTypeInstantiation(e.tok, e.Function.WhatKind, e.Function.Name, e.Function.TypeArgs, e.TypeApplication_JustFunction, inGhostContext);
          // recursively visit all subexpressions (all actual parameters), noting which ones correspond to ghost formal parameters
          Visit(e.Receiver, inGhostContext);
          Contract.Assert(e.Args.Count == e.Function.Formals.Count);
          for (var i = 0; i < e.Args.Count; i++) {
            Visit(e.Args[i], inGhostContext || e.Function.Formals[i].IsGhost);
          }
          return false;  // we've done what there is to be done
        } else if (expr is DatatypeValue) {
          var e = (DatatypeValue)expr;
          // recursively visit all subexpressions (all actual parameters), noting which ones correspond to ghost formal parameters
          Contract.Assert(e.Arguments.Count == e.Ctor.Formals.Count);
          for (var i = 0; i < e.Arguments.Count; i++) {
            Visit(e.Arguments[i], inGhostContext || e.Ctor.Formals[i].IsGhost);
          }
          return false;  // we've done what there is to be done
        } else if (expr is SetDisplayExpr || expr is MultiSetDisplayExpr || expr is MapDisplayExpr || expr is SeqConstructionExpr ||
                   expr is MultiSetFormingExpr || expr is StaticReceiverExpr) {
          // This catches other expressions whose type may potentially be illegal
          VisitType(expr.tok, expr.Type, inGhostContext);
        } else if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          Visit(e.S, true);
          Visit(e.E, inGhostContext);
          return false;
        }
        return true;
      }

      public void VisitType(IToken tok, Type type, bool inGhostContext) {
        Contract.Requires(tok != null);
        Contract.Requires(type != null);
        type = type.Normalize();  // we only do a .Normalize() here, because we want to keep stop at any type synonym or subset type
        if (type is BasicType) {
          // fine
        } else if (type is SetType) {
          var st = (SetType)type;
          var argType = st.Arg;
          if (!inGhostContext && !argType.SupportsEquality) {
            resolver.reporter.Error(MessageSource.Resolver, tok, "{2}set argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType), st.Finite ? "" : "i");
          }
          VisitType(tok, argType, inGhostContext);

        } else if (type is MultiSetType) {
          var argType = ((MultiSetType)type).Arg;
          if (!inGhostContext && !argType.SupportsEquality) {
            resolver.reporter.Error(MessageSource.Resolver, tok, "multiset argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType));

          }
          VisitType(tok, argType, inGhostContext);
        } else if (type is MapType) {
          var mt = (MapType)type;
          if (!inGhostContext && !mt.Domain.SupportsEquality) {
            resolver.reporter.Error(MessageSource.Resolver, tok, "{2}map domain type must support equality (got {0}){1}", mt.Domain, TypeEqualityErrorMessageHint(mt.Domain), mt.Finite ? "" : "i");
          }
          VisitType(tok, mt.Domain, inGhostContext);
          VisitType(tok, mt.Range, inGhostContext);

        } else if (type is SeqType) {
          Type argType = ((SeqType)type).Arg;
          VisitType(tok, argType, inGhostContext);

        } else if (type is UserDefinedType) {
          var udt = (UserDefinedType)type;
          Contract.Assert(udt.ResolvedClass != null);
          var formalTypeArgs = udt.ResolvedClass.TypeArgs;
          Contract.Assert(formalTypeArgs != null);
          CheckTypeInstantiation(udt.tok, "type", udt.ResolvedClass.Name, formalTypeArgs, udt.TypeArgs, inGhostContext);

        } else if (type is TypeProxy) {
          // the type was underconstrained; this is checked elsewhere, but it is not in violation of the equality-type test
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
        }
      }

      void CheckTypeInstantiation(IToken tok, string what, string className, List<TypeParameter> formalTypeArgs, List<Type> actualTypeArgs, bool inGhostContext) {
        Contract.Requires(tok != null);
        Contract.Requires(what != null);
        Contract.Requires(className != null);
        Contract.Requires(formalTypeArgs != null);
        Contract.Requires(actualTypeArgs != null);
        Contract.Requires(formalTypeArgs.Count == actualTypeArgs.Count);

        for (var i = 0; i < formalTypeArgs.Count; i++) {
          var formal = formalTypeArgs[i];
          var actual = actualTypeArgs[i];
          if (!CheckCharacteristics(formal.Characteristics, actual, inGhostContext, out var whatIsWrong, out var hint)) {
            resolver.reporter.Error(MessageSource.Resolver, tok, "type parameter{0} ({1}) passed to {2} {3} must support {4} (got {5}){6}",
              actualTypeArgs.Count == 1 ? "" : " " + i, formal.Name, what, className, whatIsWrong, actual, hint);
          }
          VisitType(tok, actual, inGhostContext);
        }
      }

      bool CheckCharacteristics(TypeParameter.TypeParameterCharacteristics formal, Type actual, bool inGhostContext, out string whatIsWrong, out string hint) {
        Contract.Ensures(Contract.Result<bool>() || (Contract.ValueAtReturn(out whatIsWrong) != null && Contract.ValueAtReturn(out hint) != null));
        if (!inGhostContext && formal.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified && !actual.SupportsEquality) {
          whatIsWrong = "equality";
          hint = TypeEqualityErrorMessageHint(actual);
          return false;
        }
        var cl = (actual.Normalize() as UserDefinedType)?.ResolvedClass;
        var tp = (TopLevelDecl)(cl as TypeParameter) ?? cl as OpaqueTypeDecl;
        if (formal.HasCompiledValue && (inGhostContext ? !actual.IsNonempty : !actual.HasCompilableValue)) {
          whatIsWrong = "auto-initialization";
          hint = tp == null ? "" :
            string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(0)', which says it can only be instantiated with a type that supports auto-initialization)", tp.Name, tp.tok.line, tp.WhatKind);
          return false;
        }
        if (formal.IsNonempty && !actual.IsNonempty) {
          whatIsWrong = "nonempty";
          hint = tp == null ? "" :
            string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(00)', which says it can only be instantiated with a nonempty type)", tp.Name, tp.tok.line, tp.WhatKind);
          return false;
        }
        if (formal.ContainsNoReferenceTypes && actual.MayInvolveReferences) {
          whatIsWrong = "no references";
          hint = tp == null ? "" :
            string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(!new)', which says it can only be instantiated with a type that contains no references)", tp.Name, tp.tok.line, tp.WhatKind);
          return false;
        }
        whatIsWrong = null;
        hint = null;
        return true;
      }

      string TypeEqualityErrorMessageHint(Type argType) {
        Contract.Requires(argType != null);
        var cl = (argType.Normalize() as UserDefinedType)?.ResolvedClass;
        var tp = (TopLevelDecl)(cl as TypeParameter) ?? cl as OpaqueTypeDecl;
        if (tp != null) {
          return string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(==)', which says it can only be instantiated with a type that supports equality)", tp.Name, tp.tok.line, tp.WhatKind);
        }
        return "";
      }
    }

    public static bool CanCompareWith(Expression expr) {
      Contract.Requires(expr != null);
      if (expr.Type.SupportsEquality) {
        return true;
      }
      expr = expr.Resolved;
      if (expr is DatatypeValue datatypeValue && !datatypeValue.Ctor.EnclosingDatatype.HasGhostVariant) {
        for (var i = 0; i < datatypeValue.Ctor.Formals.Count; i++) {
          if (datatypeValue.Ctor.Formals[i].IsGhost) {
            return false;
          } else if (!CanCompareWith(datatypeValue.Arguments[i])) {
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

    #endregion CheckTypeCharacteristics

    // ------------------------------------------------------------------------------------------------------
    // ----- ComputeGhostInterest ---------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region ComputeGhostInterest
    public void ComputeGhostInterest(Statement stmt, bool mustBeErasable, [CanBeNull] string proofContext, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      var visitor = new GhostInterestVisitor(codeContext, this, reporter, false);
      visitor.Visit(stmt, mustBeErasable, proofContext);
    }

    #endregion

    // ------------------------------------------------------------------------------------------------------
    // ----- FillInDefaultLoopDecreases ---------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region FillInDefaultLoopDecreases
    class FillInDefaultLoopDecreases_Visitor : ResolverBottomUpVisitor {
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
    class ReportOtherAdditionalInformation_Visitor : ResolverBottomUpVisitor {
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
            var substituter = new AlphaConvertingSubstituter(cs.Receiver, argsSubstMap, new Dictionary<TypeParameter, Type>());
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
    class CheckDividedConstructorInit_Visitor : ResolverTopDownVisitor<int> {
      public CheckDividedConstructorInit_Visitor(Resolver resolver)
        : base(resolver) {
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
          // maps: +, -
          case BinaryExpr.ResolvedOpcode.MapMerge:
          case BinaryExpr.ResolvedOpcode.MapSubtraction:
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
        List<TypeParameter> formalTypeArgs = udt.ResolvedClass.TypeArgs;
        Contract.Assert(formalTypeArgs != null);
        Contract.Assert(formalTypeArgs.Count == udt.TypeArgs.Count);
        var i = 0;
        foreach (var argType in udt.TypeArgs) {
          var formalTypeArg = formalTypeArgs[i];
          if ((formalTypeArg.SupportsEquality && argType.AsTypeParameter == tp) || InferRequiredEqualitySupport(tp, argType)) {
            return true;
          }
          i++;
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
    readonly Scope<TypeParameter>/*!*/ allTypeParameters = new Scope<TypeParameter>();
    public readonly Scope<IVariable>/*!*/ scope = new Scope<IVariable>();
    Scope<Statement>/*!*/ enclosingStatementLabels = new Scope<Statement>();
    public readonly Scope<Label>/*!*/ DominatingStatementLabels = new Scope<Label>();
    List<Statement> loopStack = new List<Statement>();  // the enclosing loops (from which it is possible to break out)

    /// <summary>
    /// Resolves the types along .ParentTraits and fills in .ParentTraitHeads
    /// </summary>
    void ResolveParentTraitTypes(TopLevelDeclWithMembers cl, Graph<TopLevelDeclWithMembers> parentRelation) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      currentClass = cl;
      allTypeParameters.PushMarker();
      ResolveTypeParameters(cl.TypeArgs, false, cl);
      foreach (var tt in cl.ParentTraits) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(cl.tok, tt, new NoContext(cl.EnclosingModuleDefinition), ResolveTypeOptionEnum.DontInfer, null);
        if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
          var udt = tt as UserDefinedType;
          if (udt != null && udt.ResolvedClass is NonNullTypeDecl nntd && nntd.ViewAsClass is TraitDecl trait) {
            // disallowing inheritance in multi module case
            bool termination = true;
            if (cl.EnclosingModuleDefinition == trait.EnclosingModuleDefinition || trait.IsObjectTrait || (Attributes.ContainsBool(trait.Attributes, "termination", ref termination) && !termination)) {
              // all is good (or the user takes responsibility for the lack of termination checking)
              if (!cl.ParentTraitHeads.Contains(trait)) {
                cl.ParentTraitHeads.Add(trait);
                parentRelation.AddEdge(cl, trait);
              }
            } else {
              reporter.Error(MessageSource.Resolver, udt.tok, "{0} '{1}' is in a different module than trait '{2}'. A {0} may only extend a trait in the same module, unless the parent trait is annotated with {{:termination false}}.", cl.WhatKind, cl.Name, trait.FullName);
            }
          } else {
            reporter.Error(MessageSource.Resolver, udt != null ? udt.tok : cl.tok, "a {0} can only extend traits (found '{1}')", cl.WhatKind, tt);
          }
        }
      }
      allTypeParameters.PopMarker();
      currentClass = null;
    }

    /// <summary>
    /// This method idempotently fills in .InheritanceInformation, .ParentFormalTypeParametersToActuals, and the
    /// name->MemberDecl table for "cl" and the transitive parent traits of "cl". It also checks that every (transitive)
    /// parent trait is instantiated with the same type parameters
    /// The method assumes that all types along .ParentTraits have been successfully resolved and .ParentTraitHeads been filled in.
    /// </summary>
    void RegisterInheritedMembers(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);

      if (cl.ParentTypeInformation != null) {
        return;
      }
      cl.ParentTypeInformation = new TopLevelDeclWithMembers.InheritanceInformationClass();

      // populate .ParentTypeInformation and .ParentFormalTypeParametersToActuals for the immediate parent traits
      foreach (var tt in cl.ParentTraits) {
        var udt = (UserDefinedType)tt;
        var nntd = (NonNullTypeDecl)udt.ResolvedClass;
        var trait = (TraitDecl)nntd.ViewAsClass;
        cl.ParentTypeInformation.Record(trait, udt);
        Contract.Assert(trait.TypeArgs.Count == udt.TypeArgs.Count);
        for (var i = 0; i < trait.TypeArgs.Count; i++) {
          // there may be duplciate parent traits, which haven't been checked for yet, so add mapping only for the first occurrence of each type parameter
          if (!cl.ParentFormalTypeParametersToActuals.ContainsKey(trait.TypeArgs[i])) {
            cl.ParentFormalTypeParametersToActuals.Add(trait.TypeArgs[i], udt.TypeArgs[i]);
          }
        }
      }

      // populate .ParentTypeInformation and .ParentFormalTypeParametersToActuals for the transitive parent traits
      foreach (var trait in cl.ParentTraitHeads) {
        // make sure the parent trait has been processed; then, incorporate its inheritance information
        RegisterInheritedMembers(trait);
        cl.ParentTypeInformation.Extend(trait, trait.ParentTypeInformation, cl.ParentFormalTypeParametersToActuals);
        foreach (var entry in trait.ParentFormalTypeParametersToActuals) {
          var v = entry.Value.Subst(cl.ParentFormalTypeParametersToActuals);
          if (!cl.ParentFormalTypeParametersToActuals.ContainsKey(entry.Key)) {
            cl.ParentFormalTypeParametersToActuals.Add(entry.Key, v);
          }
        }
      }

      // Check that every (transitive) parent trait is instantiated with the same type parameters
      foreach (var group in cl.ParentTypeInformation.GetTypeInstantiationGroups()) {
        Contract.Assert(1 <= group.Count);
        var ty = group[0].Item1;
        for (var i = 1; i < group.Count; i++) {
          if (!group.GetRange(0, i).Exists(pair => pair.Item1.Equals(group[i].Item1))) {
            var via0 = group[0].Item2.Count == 0 ? "" : " (via " + Util.Comma(group[0].Item2, traitDecl => traitDecl.Name) + ")";
            var via1 = group[i].Item2.Count == 0 ? "" : " (via " + Util.Comma(group[i].Item2, traitDecl => traitDecl.Name) + ")";
            reporter.Error(MessageSource.Resolver, cl.tok,
              "duplicate trait parents with the same head type must also have the same type arguments; got {0}{1} and {2}{3}",
              ty, via0, group[i].Item1, via1);
          }
        }
      }

      // Update the name->MemberDecl table for the class. Report an error if the same name refers to more than one member,
      // except when such duplication is purely that one member, say X, is inherited and the other is an override of X.
      var inheritedMembers = new Dictionary<string, MemberDecl>();
      foreach (var trait in cl.ParentTraitHeads) {
        foreach (var traitMember in classMembers[trait].Values) {  // TODO: rather than using .Values, it would be nice to use something that gave a deterministic order
          if (!inheritedMembers.TryGetValue(traitMember.Name, out var prevMember)) {
            // record "traitMember" as an inherited member
            inheritedMembers.Add(traitMember.Name, traitMember);
          } else if (traitMember == prevMember) {
            // same member, inherited two different ways
          } else if (traitMember.Overrides(prevMember)) {
            // we're inheriting "prevMember" and "traitMember" from different parent traits, where "traitMember" is an override of "prevMember"
            Contract.Assert(traitMember.EnclosingClass != cl && prevMember.EnclosingClass != cl && traitMember.EnclosingClass != prevMember.EnclosingClass); // sanity checks
            // re-map "traitMember.Name" to point to the overriding member
            inheritedMembers[traitMember.Name] = traitMember;
          } else if (prevMember.Overrides(traitMember)) {
            // we're inheriting "prevMember" and "traitMember" from different parent traits, where "prevMember" is an override of "traitMember"
            Contract.Assert(traitMember.EnclosingClass != cl && prevMember.EnclosingClass != cl && traitMember.EnclosingClass != prevMember.EnclosingClass); // sanity checks
            // keep the mapping to "prevMember"
          } else {
            // "prevMember" and "traitMember" refer to different members (with the same name)
            reporter.Error(MessageSource.Resolver, cl.tok, "{0} '{1}' inherits a member named '{2}' from both traits '{3}' and '{4}'",
              cl.WhatKind, cl.Name, traitMember.Name, prevMember.EnclosingClass.Name, traitMember.EnclosingClass.Name);
          }
        }
      }
      // Incorporate the inherited members into the name->MemberDecl mapping of "cl"
      var members = classMembers[cl];
      foreach (var entry in inheritedMembers) {
        var name = entry.Key;
        var traitMember = entry.Value;
        if (!members.TryGetValue(name, out var clMember)) {
          members.Add(name, traitMember);
        } else {
          Contract.Assert(clMember.EnclosingClass == cl);  // sanity check
          Contract.Assert(clMember.OverriddenMember == null);  // sanity check
          clMember.OverriddenMember = traitMember;
        }
      }
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
            ResolveType(member.tok, ((Field)member).Type, new NoContext(cl.EnclosingModuleDefinition), ResolveTypeOptionEnum.DontInfer, null);
          }
        } else if (member is Function) {
          var f = (Function)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, true, f);
          ResolveFunctionSignature(f);
          allTypeParameters.PopMarker();
          if (f is ExtremePredicate && ec == reporter.Count(ErrorLevel.Error)) {
            var ff = ((ExtremePredicate)f).PrefixPredicate;  // note, may be null if there was an error before the prefix predicate was generated
            if (ff != null) {
              ff.EnclosingClass = cl;
              allTypeParameters.PushMarker();
              ResolveTypeParameters(ff.TypeArgs, true, ff);
              ResolveFunctionSignature(ff);
              allTypeParameters.PopMarker();
            }
          }
          if (f.ByMethodDecl != null) {
            f.ByMethodDecl.EnclosingClass = cl;
          }

        } else if (member is Method) {
          var m = (Method)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, true, m);
          ResolveMethodSignature(m);
          allTypeParameters.PopMarker();
          if (m is ExtremeLemma com && com.PrefixLemma != null && ec == reporter.Count(ErrorLevel.Error)) {
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

    /// <summary>
    /// This method checks the rules for inherited and overridden members. It also populates .InheritedMembers with the
    /// non-static members that are inherited from parent traits.
    /// </summary>
    void InheritedTraitMembers(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      Contract.Requires(cl.ParentTypeInformation != null);

      foreach (var member in classMembers[cl].Values) {
        if (member is PrefixPredicate || member is PrefixLemma) {
          // these are handled with the corresponding extreme predicate/lemma
          continue;
        }
        if (member.EnclosingClass != cl) {
          // The member is the one inherited from a trait (and the class does not itself define a member with this name).  This
          // is fine for fields and for functions and methods with bodies. However, if "cl" is not itself a trait, then for a body-less function
          // or method, "cl" is required to at least redeclare the member with its signature.  (It should also provide a stronger specification,
          // but that will be checked by the verifier.  And it should also have a body, but that will be checked by the compiler.)
          if (member.IsStatic) {
            // nothing to do
          } else {
            cl.InheritedMembers.Add(member);
            if (member is Field || (member as Function)?.Body != null || (member as Method)?.Body != null) {
              // member is a field or a fully defined function or method
            } else if (cl is TraitDecl) {
              // there are no expectations that a field needs to repeat the signature of inherited body-less members
            } else if (Attributes.Contains(member.Attributes, "extern")) {
              // Extern functions do not need to be reimplemented.
              // TODO: When `:extern` is separated from `:compile false`, this should become `:compile false`.
            } else if (member is Lemma && Attributes.Contains(member.Attributes, "opaque_reveal")) {
              // reveal lemmas do not need to be reimplemented
            } else {
              reporter.Error(MessageSource.Resolver, cl.tok, "{0} '{1}' does not implement trait {2} '{3}.{4}'", cl.WhatKind, cl.Name, member.WhatKind, member.EnclosingClass.Name, member.Name);
            }
          }
          continue;
        }
        if (member.OverriddenMember == null) {
          // this member has nothing to do with the parent traits
          continue;
        }

        var traitMember = member.OverriddenMember;
        var trait = traitMember.EnclosingClass;
        if (traitMember.IsStatic) {
          reporter.Error(MessageSource.Resolver, member.tok, "static {0} '{1}' is inherited from trait '{2}' and is not allowed to be re-declared",
            traitMember.WhatKind, traitMember.Name, trait.Name);
        } else if (member.IsStatic) {
          reporter.Error(MessageSource.Resolver, member.tok, "static member '{0}' overrides non-static member in trait '{1}'", member.Name, trait.Name);
        } else if (traitMember is Field) {
          // The class is not allowed to do anything with the field other than silently inherit it.
          reporter.Error(MessageSource.Resolver, member.tok, "{0} '{1}' is inherited from trait '{2}' and is not allowed to be re-declared", traitMember.WhatKind, traitMember.Name, trait.Name);
        } else if ((traitMember as Function)?.Body != null || (traitMember as Method)?.Body != null) {
          // the overridden member is a fully defined function or method, so the class is not allowed to do anything with it other than silently inherit it
          reporter.Error(MessageSource.Resolver, member.tok, "fully defined {0} '{1}' is inherited from trait '{2}' and is not allowed to be re-declared",
            traitMember.WhatKind, traitMember.Name, trait.Name);
        } else if (member is Method != traitMember is Method ||
                   member is Lemma != traitMember is Lemma ||
                   member is TwoStateLemma != traitMember is TwoStateLemma ||
                   member is LeastLemma != traitMember is LeastLemma ||
                   member is GreatestLemma != traitMember is GreatestLemma ||
                   member is Function != traitMember is Function ||
                   member is TwoStateFunction != traitMember is TwoStateFunction ||
                   member is LeastPredicate != traitMember is LeastPredicate ||
                   member is GreatestPredicate != traitMember is GreatestPredicate) {
          reporter.Error(MessageSource.Resolver, member.tok, "{0} '{1}' in '{2}' can only be overridden by a {0} (got {3})", traitMember.WhatKind, traitMember.Name, trait.Name, member.WhatKind);
        } else if (member.IsGhost != traitMember.IsGhost) {
          reporter.Error(MessageSource.Resolver, member.tok, "overridden {0} '{1}' in '{2}' has different ghost/compiled status than in trait '{3}'",
            traitMember.WhatKind, traitMember.Name, cl.Name, trait.Name);
        } else {
          // Copy trait member's extern attribute onto class member if class does not provide one
          if (!Attributes.Contains(member.Attributes, "extern") && Attributes.Contains(traitMember.Attributes, "extern")) {
            var traitExternArgs = Attributes.FindExpressions(traitMember.Attributes, "extern");
            member.Attributes = new Attributes("extern", traitExternArgs, member.Attributes);
          }

          if (traitMember is Method) {
            var classMethod = (Method)member;
            var traitMethod = (Method)traitMember;
            classMethod.OverriddenMethod = traitMethod;

            CheckOverride_MethodParameters(classMethod, traitMethod, cl.ParentFormalTypeParametersToActuals);

            var traitMethodAllowsNonTermination = Contract.Exists(traitMethod.Decreases.Expressions, e => e is WildcardExpr);
            var classMethodAllowsNonTermination = Contract.Exists(classMethod.Decreases.Expressions, e => e is WildcardExpr);
            if (classMethodAllowsNonTermination && !traitMethodAllowsNonTermination) {
              reporter.Error(MessageSource.Resolver, classMethod.tok, "not allowed to override a terminating method with a possibly non-terminating method ('{0}')", classMethod.Name);
            }

          } else if (traitMember is Function) {
            var classFunction = (Function)member;
            var traitFunction = (Function)traitMember;
            classFunction.OverriddenFunction = traitFunction;

            CheckOverride_FunctionParameters(classFunction, traitFunction, cl.ParentFormalTypeParametersToActuals);

          } else {
            Contract.Assert(false); // unexpected member
          }
        }
      }
    }

    public void CheckOverride_FunctionParameters(Function nw, Function old, Dictionary<TypeParameter, Type> classTypeMap) {
      Contract.Requires(nw != null);
      Contract.Requires(old != null);
      Contract.Requires(classTypeMap != null);

      var typeMap = CheckOverride_TypeParameters(nw.tok, old.TypeArgs, nw.TypeArgs, nw.Name, "function", classTypeMap);
      if (nw is ExtremePredicate nwFix && old is ExtremePredicate oldFix && nwFix.KNat != oldFix.KNat) {
        reporter.Error(MessageSource.Resolver, nw,
          "the type of special parameter '_k' of {0} '{1}' ({2}) must be the same as in the overridden {0} ({3})",
          nw.WhatKind, nw.Name, nwFix.KNat ? "nat" : "ORDINAL", oldFix.KNat ? "nat" : "ORDINAL");
      }
      CheckOverride_ResolvedParameters(nw.tok, old.Formals, nw.Formals, nw.Name, "function", "parameter", typeMap);
      var oldResultType = old.ResultType.Subst(typeMap);
      if (!nw.ResultType.Equals(oldResultType, true)) {
        reporter.Error(MessageSource.Resolver, nw, "the result type of function '{0}' ({1}) differs from that in the overridden function ({2})",
          nw.Name, nw.ResultType, oldResultType);
      }
    }

    public void CheckOverride_MethodParameters(Method nw, Method old, Dictionary<TypeParameter, Type> classTypeMap) {
      Contract.Requires(nw != null);
      Contract.Requires(old != null);
      Contract.Requires(classTypeMap != null);
      var typeMap = CheckOverride_TypeParameters(nw.tok, old.TypeArgs, nw.TypeArgs, nw.Name, "method", classTypeMap);
      if (nw is ExtremeLemma nwFix && old is ExtremeLemma oldFix && nwFix.KNat != oldFix.KNat) {
        reporter.Error(MessageSource.Resolver, nw,
          "the type of special parameter '_k' of {0} '{1}' ({2}) must be the same as in the overridden {0} ({3})",
          nw.WhatKind, nw.Name, nwFix.KNat ? "nat" : "ORDINAL", oldFix.KNat ? "nat" : "ORDINAL");
      }
      CheckOverride_ResolvedParameters(nw.tok, old.Ins, nw.Ins, nw.Name, "method", "in-parameter", typeMap);
      CheckOverride_ResolvedParameters(nw.tok, old.Outs, nw.Outs, nw.Name, "method", "out-parameter", typeMap);
    }

    private Dictionary<TypeParameter, Type> CheckOverride_TypeParameters(IToken tok, List<TypeParameter> old, List<TypeParameter> nw, string name, string thing, Dictionary<TypeParameter, Type> classTypeMap) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      var typeMap = old.Count == 0 ? classTypeMap : new Dictionary<TypeParameter, Type>(classTypeMap);
      if (old.Count != nw.Count) {
        reporter.Error(MessageSource.Resolver, tok,
          "{0} '{1}' is declared with a different number of type parameters ({2} instead of {3}) than in the overridden {0}", thing, name, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          typeMap.Add(o, new UserDefinedType(tok, n));
          // Check type characteristics
          if (o.Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.InferredRequired && o.Characteristics.EqualitySupport != n.Characteristics.EqualitySupport) {
            reporter.Error(MessageSource.Resolver, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting equality", n.Name);
          }
          if (o.Characteristics.HasCompiledValue != n.Characteristics.HasCompiledValue) {
            reporter.Error(MessageSource.Resolver, n.tok, "type parameter '{0}' is not allowed to change the requirement of supporting auto-initialization", n.Name);
          } else if (o.Characteristics.IsNonempty != n.Characteristics.IsNonempty) {
            reporter.Error(MessageSource.Resolver, n.tok, "type parameter '{0}' is not allowed to change the requirement of being nonempty", n.Name);
          }
          if (o.Characteristics.ContainsNoReferenceTypes != n.Characteristics.ContainsNoReferenceTypes) {
            reporter.Error(MessageSource.Resolver, n.tok, "type parameter '{0}' is not allowed to change the no-reference-type requirement", n.Name);
          }

        }
      }
      return typeMap;
    }

    private void CheckOverride_ResolvedParameters(IToken tok, List<Formal> old, List<Formal> nw, string name, string thing, string parameterKind, Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      Contract.Requires(parameterKind != null);
      Contract.Requires(typeMap != null);
      if (old.Count != nw.Count) {
        reporter.Error(MessageSource.Resolver, tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than in the overridden {0}",
          thing, name, parameterKind, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (!o.IsGhost && n.IsGhost) {
            reporter.Error(MessageSource.Resolver, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from non-ghost to ghost",
              parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            reporter.Error(MessageSource.Resolver, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from ghost to non-ghost",
              parameterKind, n.Name, thing, name);
          } else if (!o.IsOld && n.IsOld) {
            reporter.Error(MessageSource.Resolver, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from new to non-new",
              parameterKind, n.Name, thing, name);
          } else if (o.IsOld && !n.IsOld) {
            reporter.Error(MessageSource.Resolver, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from non-new to new",
              parameterKind, n.Name, thing, name);
          } else if (!o.IsOlder && n.IsOlder) {
            reporter.Error(MessageSource.Resolver, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from non-older to older",
              parameterKind, n.Name, thing, name);
          } else if (o.IsOlder && !n.IsOlder) {
            reporter.Error(MessageSource.Resolver, n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from older to non-older",
              parameterKind, n.Name, thing, name);
          } else {
            var oo = o.Type.Subst(typeMap);
            if (!n.Type.Equals(oo, true)) {
              reporter.Error(MessageSource.Resolver, n.tok,
                "the type of {0} '{1}' is different from the type of the corresponding {0} in trait {2} ('{3}' instead of '{4}')",
                parameterKind, n.Name, thing, n.Type, oo);
            }
          }
        }
      }
    }

    /// <summary>
    /// Check that the SCC of 'startingPoint' can be carved up into stratospheres in such a way that each
    /// datatype has some value that can be constructed from datatypes in lower stratospheres only.
    /// The algorithm used here is quadratic in the number of datatypes in the SCC.  Since that number is
    /// deemed to be rather small, this seems okay.
    ///
    /// As a side effect of this checking, the GroundingCtor field is filled in (for every inductive datatype
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
          if (dt.GroundingCtor != null) {
            // previously cleared
          } else if (ComputeGroundingCtor(dt)) {
            Contract.Assert(dt.GroundingCtor != null);  // should have been set by the successful call to StratosphereCheck)
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
            if (dt.GroundingCtor == null) {
              reporter.Error(MessageSource.Resolver, dt, "because of cyclic dependencies among constructor argument types, no instances of datatype '{0}' can be constructed", dt.Name);
            }
          }
          return;
        }
      }
    }

    /// <summary>
    /// Check that the datatype has some constructor all whose argument types can be constructed.
    /// Returns 'true' and sets dt.GroundingCtor if that is the case.
    /// </summary>
    bool ComputeGroundingCtor(IndDatatypeDecl dt) {
      Contract.Requires(dt != null);
      Contract.Requires(dt.GroundingCtor == null);  // the intention is that this method be called only when GroundingCtor hasn't already been set
      Contract.Ensures(!Contract.Result<bool>() || dt.GroundingCtor != null);

      // Stated differently, check that there is some constuctor where no argument type goes to the same stratum.
      DatatypeCtor groundingCtor = null;
      ISet<TypeParameter> lastTypeParametersUsed = null;
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var typeParametersUsed = new HashSet<TypeParameter>();
        foreach (Formal p in ctor.Formals) {
          if (!CheckCanBeConstructed(p.Type, typeParametersUsed)) {
            // the argument type (has a component which) is not yet known to be constructable
            goto NEXT_OUTER_ITERATION;
          }
        }
        // this constructor satisfies the requirements, check to see if it is a better fit than the
        // one found so far. Here, "better" means
        //   * a ghost constructor is better than a non-ghost constructor
        //   * among those, a constructor with fewer type arguments is better
        //   * among those, the first one is preferred.
        if (groundingCtor == null || (!groundingCtor.IsGhost && ctor.IsGhost) || typeParametersUsed.Count < lastTypeParametersUsed.Count) {
          groundingCtor = ctor;
          lastTypeParametersUsed = typeParametersUsed;
        }

      NEXT_OUTER_ITERATION: { }
      }

      if (groundingCtor != null) {
        dt.GroundingCtor = groundingCtor;
        dt.TypeParametersUsedInConstructionByGroundingCtor = new bool[dt.TypeArgs.Count];
        for (int i = 0; i < dt.TypeArgs.Count; i++) {
          dt.TypeParametersUsedInConstructionByGroundingCtor[i] = lastTypeParametersUsed.Contains(dt.TypeArgs[i]);
        }
        return true;
      }

      // no constructor satisfied the requirements, so this is an illegal datatype declaration
      return false;
    }

    bool CheckCanBeConstructed(Type type, ISet<TypeParameter> typeParametersUsed) {
      type = type.NormalizeExpandKeepConstraints();
      if (type is BasicType) {
        // values of primitive types can always be constructed
        return true;
      } else if (type is CollectionType) {
        // values of collection types can always be constructed
        return true;
      }

      var udt = (UserDefinedType)type;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TypeParameter) {
        // treat a type parameter like a ground type
        typeParametersUsed.Add((TypeParameter)cl);
        return true;
      } else if (cl is OpaqueTypeDecl) {
        // an opaque is like a ground type
        return true;
      } else if (cl is InternalTypeSynonymDecl) {
        // a type exported as opaque from another module is like a ground type
        return true;
      } else if (cl is NewtypeDecl) {
        // values of a newtype can be constructed
        return true;
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          // a witness exists, but may depend on type parameters
          type.AddFreeTypeParameters(typeParametersUsed);
          return true;
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            return CheckCanBeConstructed(udt.TypeArgs.Last(), typeParametersUsed);
          } else {
            return true;
          }
        } else {
          return CheckCanBeConstructed(td.RhsWithArgument(udt.TypeArgs), typeParametersUsed);
        }
      } else if (cl is ClassDecl) {
        // null is a value for this possibly-null type
        return true;
      } else if (cl is CoDatatypeDecl) {
        // may depend on type parameters
        type.AddFreeTypeParameters(typeParametersUsed);
        return true;
      }

      var dependee = type.AsIndDatatype;
      Contract.Assert(dependee != null);
      if (dependee.GroundingCtor == null) {
        // the type is an inductive datatype that we don't yet know how to construct
        return false;
      }
      // also check the type arguments of the inductive datatype
      Contract.Assert(udt.TypeArgs.Count == dependee.TypeParametersUsedInConstructionByGroundingCtor.Length);
      var i = 0;
      foreach (var ta in udt.TypeArgs) {
        if (dependee.TypeParametersUsedInConstructionByGroundingCtor[i] && !CheckCanBeConstructed(ta, typeParametersUsed)) {
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

      void MarkSCCAsNotSupportingEquality() {
        foreach (var ddtt in scc) {
          ddtt.EqualitySupport = IndDatatypeDecl.ES.Never;
        }
      }

      // Look for conditions that make the whole SCC incapable of providing the equality operation:
      //   * a datatype in the SCC has a ghost constructor
      //   * a parameter of an inductive datatype in the SCC is ghost
      //   * the type of a parameter of an inductive datatype in the SCC does not support equality
      foreach (var dt in scc) {
        Contract.Assume(dt.EqualitySupport == IndDatatypeDecl.ES.NotYetComputed);
        foreach (var ctor in dt.Ctors) {
          if (ctor.IsGhost) {
            MarkSCCAsNotSupportingEquality();
            return;  // we are done
          }
          foreach (var arg in ctor.Formals) {
            var anotherIndDt = arg.Type.AsIndDatatype;
            if (arg.IsGhost ||
                (anotherIndDt != null && anotherIndDt.EqualitySupport == IndDatatypeDecl.ES.Never) ||
                arg.Type.IsCoDatatype ||
                arg.Type.IsArrowType) {
              // arg.Type is known never to support equality
              MarkSCCAsNotSupportingEquality();
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
          return host is Function && !(host is ExtremePredicate);
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
        case "options":
          return host is ModuleDefinition;
        default:
          return false;
      }
    }

    public void ScopePushAndReport(Scope<IVariable> scope, IVariable v, string kind) {
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
          reporter.Error(MessageSource.Resolver, ErrorID.None, tok, "Duplicate {0} name: {1}", kind, name);
          break;
        case Scope<Thing>.PushResult.Shadow:
          reporter.Warning(MessageSource.Resolver, ErrorID.None, tok, "Shadowed {0} name: {1}", kind, name);
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
      }
      if (f.Result != null) {
        ScopePushAndReport(scope, f.Result, "parameter/return");
        ResolveType(f.Result.tok, f.Result.Type, f, option, f.TypeArgs);
      } else {
        ResolveType(f.tok, f.ResultType, f, option, f.TypeArgs);
      }
      scope.PopMarker();
    }

    public enum FrameExpressionUse { Reads, Modifies, Unchanged }

    /// <summary>
    /// This method can be called even if the resolution of "fe" failed; in that case, this method will
    /// not issue any error message.
    /// </summary>
    public void DisallowNonGhostFieldSpecifiers(FrameExpression fe) {
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
      }
      // resolve out-parameters
      foreach (Formal p in m.Outs) {
        ScopePushAndReport(scope, p, "parameter");
        ResolveType(p.tok, p.Type, m, option, m.TypeArgs);
      }
      scope.PopMarker();
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
      foreach (var p in iter.Ins) {
        ResolveType(p.tok, p.Type, iter, option, iter.TypeArgs);
      }
      foreach (var p in iter.Outs) {
        ResolveType(p.tok, p.Type, iter, option, iter.TypeArgs);
        if (!p.Type.KnownToHaveToAValue(p.IsGhost)) {
          reporter.Error(MessageSource.Resolver, p.tok, "type of yield-parameter must support auto-initialization (got '{0}')", p.Type);
        }
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
        nnt.TypeArgs.AddRange(iter.TypeArgs.ConvertAll(tp => new TypeParameter(tp.RangeToken, tp.NameNode, tp.VarianceSyntax, tp.Characteristics)));
        var varUdt = (UserDefinedType)nnt.Var.Type;
        Contract.Assert(varUdt.TypeArgs.Count == 0);
        varUdt.TypeArgs = nnt.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      }
      scope.PopMarker();
    }

    /// <summary>
    /// Assumes the specification of the iterator itself has been successfully resolved.
    /// </summary>
    void CreateIteratorMethodSpecs(IteratorDecl iter) {
      Contract.Requires(iter != null);

      var tok = new AutoGeneratedToken(iter.tok);

      // ---------- here comes the constructor ----------
      // same requires clause as the iterator itself
      iter.Member_Init.Req.AddRange(iter.Requires);
      var ens = iter.Member_Init.Ens;
      foreach (var p in iter.Ins) {
        // ensures this.x == x;
        ens.Add(new AttributedExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new IdentifierExpr(p.tok, p.Name))));
      }
      foreach (var p in iter.OutsHistoryFields) {
        // ensures this.ys == [];
        ens.Add(new AttributedExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new SeqDisplayExpr(p.tok, new List<Expression>()))));
      }
      // ensures this.Valid();
      var valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, iter.tok, new List<ActualBinding>());
      ens.Add(new AttributedExpression(valid_call));
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
      ens.Add(new AttributedExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"),
        new OldExpr(tok, frameSet))));
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
      ens.Add(new AttributedExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"),
        new OldExpr(tok, frameSet))));
      // ensures this._new == {};
      ens.Add(new AttributedExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
        new SetDisplayExpr(iter.tok, true, new List<Expression>()))));
      // ensures this._decreases0 == old(DecreasesClause[0]) && ...;
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var p = iter.Decreases.Expressions[i];
        ens.Add(new AttributedExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq,
          new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), iter.DecreasesFields[i].Name),
          new OldExpr(tok, p))));
      }

      // ---------- here comes predicate Valid() ----------
      var reads = iter.Member_Valid.Reads;
      reads.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));  // reads this;
      reads.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_reads"), null));  // reads this._reads;
      reads.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));  // reads this._new;

      // ---------- here comes method MoveNext() ----------
      // requires this.Valid();
      var req = iter.Member_MoveNext.Req;
      valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, iter.tok, new List<ActualBinding>());
      req.Add(new AttributedExpression(valid_call));
      // requires YieldRequires;
      req.AddRange(iter.YieldRequires);
      // modifies this, this._modifies, this._new;
      var mod = iter.Member_MoveNext.Mod.Expressions;
      mod.Add(new FrameExpression(iter.tok, new ThisExpr(iter.tok), null));
      mod.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_modifies"), null));
      mod.Add(new FrameExpression(iter.tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"), null));
      // ensures fresh(_new - old(_new));
      ens = iter.Member_MoveNext.Ens;
      ens.Add(new AttributedExpression(new FreshExpr(iter.tok,
        new BinaryExpr(iter.tok, BinaryExpr.Opcode.Sub,
          new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"),
          new OldExpr(tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"))))));
      // ensures null !in _new
      ens.Add(new AttributedExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.NotIn,
        new LiteralExpr(iter.tok),
        new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), "_new"))));
      // ensures more ==> this.Valid();
      valid_call = new FunctionCallExpr(iter.tok, "Valid", new ThisExpr(iter.tok), iter.tok, iter.tok, new List<ActualBinding>());
      ens.Add(new AttributedExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp,
        new IdentifierExpr(iter.tok, "more"),
        valid_call)));
      // ensures this.ys == if more then old(this.ys) + [this.y] else old(this.ys);
      Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
      for (int i = 0; i < iter.OutsFields.Count; i++) {
        var y = iter.OutsFields[i];
        var ys = iter.OutsHistoryFields[i];
        var ite = new ITEExpr(iter.tok, false, new IdentifierExpr(iter.tok, "more"),
          new BinaryExpr(iter.tok, BinaryExpr.Opcode.Add,
            new OldExpr(tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)),
            new SeqDisplayExpr(iter.tok, new List<Expression>() { new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), y.Name) })),
          new OldExpr(tok, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name)));
        var eq = new BinaryExpr(iter.tok, BinaryExpr.Opcode.Eq, new MemberSelectExpr(iter.tok, new ThisExpr(iter.tok), ys.Name), ite);
        ens.Add(new AttributedExpression(eq));
      }
      // ensures more ==> YieldEnsures;
      foreach (var ye in iter.YieldEnsures) {
        ens.Add(new AttributedExpression(
          new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp, new IdentifierExpr(iter.tok, "more"), ye.E)
          ));
      }
      // ensures !more ==> Ensures;
      foreach (var e in iter.Ensures) {
        ens.Add(new AttributedExpression(new BinaryExpr(iter.tok, BinaryExpr.Opcode.Imp,
          new UnaryOpExpr(iter.tok, UnaryOpExpr.Opcode.Not, new IdentifierExpr(iter.tok, "more")),
          e.E)
        ));
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
    public class ResolveTypeOption {
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
    /// Returns a resolved type denoting an array type with dimension "dims" and element type "arg".
    /// Callers are expected to provide "arg" as an already resolved type.  (Note, a proxy type is resolved--
    /// only types that contain identifiers stand the possibility of not being resolved.)
    /// </summary>
    Type ResolvedArrayType(IToken tok, int dims, Type arg, ResolutionContext resolutionContext, bool useClassNameType) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      var at = builtIns.ArrayType(tok, dims, new List<Type> { arg }, false, useClassNameType);
      ResolveType(tok, at, resolutionContext, ResolveTypeOptionEnum.DontInfer, null);
      return at;
    }

    /// <summary>
    /// Resolves a NestedMatchStmt by
    /// 1 - checking that all of its patterns are linear
    /// 2 - desugaring it into a decision tree of MatchStmt and IfStmt (for constant matching)
    /// 3 - resolving the generated (sub)statement.
    /// </summary>
    void ResolveNestedMatchStmt(NestedMatchStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);

      var errorCount = reporter.Count(ErrorLevel.Error);
      s.Resolve(this, resolutionContext);
      this.SolveAllTypeConstraints();
    }



    void FillInDefaultLoopDecreases(LoopStmt loopStmt, Expression guard, List<Expression> theDecreases, ICallable enclosingMethod) {
      Contract.Requires(loopStmt != null);
      Contract.Requires(theDecreases != null);

      if (theDecreases.Count == 0 && guard != null) {
        loopStmt.InferredDecreases = true;
        Expression prefix = null;
        foreach (Expression guardConjunct in Expression.Conjuncts(guard)) {
          Expression guess = null;
          var neutralValue = Expression.CreateIntLiteral(guardConjunct.tok, -1);
          if (guardConjunct is BinaryExpr bin) {
            switch (bin.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.Lt:
              case BinaryExpr.ResolvedOpcode.Le:
              case BinaryExpr.ResolvedOpcode.LtChar:
              case BinaryExpr.ResolvedOpcode.LeChar:
                if (bin.E0.Type.IsBigOrdinalType) {
                  // we can't rely on subtracting ORDINALs, so let's just pick the upper bound and hope that works
                  guess = bin.E1;
                } else {
                  // for A < B and A <= B, use the decreases B - A
                  guess = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
                }
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
              case BinaryExpr.ResolvedOpcode.Gt:
              case BinaryExpr.ResolvedOpcode.GeChar:
              case BinaryExpr.ResolvedOpcode.GtChar:
                if (bin.E0.Type.IsBigOrdinalType) {
                  // we can't rely on subtracting ORDINALs, so let's just pick the upper bound and hope that works
                  guess = bin.E0;
                } else {
                  // for A >= B and A > B, use the decreases A - B
                  guess = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
                }
                break;
              case BinaryExpr.ResolvedOpcode.ProperSubset:
              case BinaryExpr.ResolvedOpcode.Subset:
                if (bin.E0.Type.AsSetType.Finite) {
                  // for A < B and A <= B, use the decreases |B - A|
                  guess = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E1, bin.E0), builtIns);
                }
                break;
              case BinaryExpr.ResolvedOpcode.Superset:
              case BinaryExpr.ResolvedOpcode.ProperSuperset:
                if (bin.E0.Type.AsSetType.Finite) {
                  // for A >= B and A > B, use the decreases |A - B|
                  guess = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E0, bin.E1), builtIns);
                }
                break;
              case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
              case BinaryExpr.ResolvedOpcode.MultiSubset:
                // for A < B and A <= B, use the decreases |B - A|
                guess = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E1, bin.E0), builtIns);
                break;
              case BinaryExpr.ResolvedOpcode.MultiSuperset:
              case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
                // for A >= B and A > B, use the decreases |A - B|
                guess = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E0, bin.E1), builtIns);
                break;
              case BinaryExpr.ResolvedOpcode.Prefix:
              case BinaryExpr.ResolvedOpcode.ProperPrefix:
                // for "[] < B" and "[] <= B", use B
                if (LiteralExpr.IsEmptySequence(bin.E0)) {
                  guess = bin.E1;
                }
                break;
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                if (bin.E0.Type.IsNumericBased() || bin.E0.Type.IsBitVectorType || bin.E0.Type.IsCharType) {
                  // for A != B where A and B are numeric, use the absolute difference between A and B (that is: if A <= B then B-A else A-B)
                  var AminusB = Expression.CreateSubtract_TypeConvert(bin.E0, bin.E1);
                  var BminusA = Expression.CreateSubtract_TypeConvert(bin.E1, bin.E0);
                  var test = Expression.CreateAtMost(bin.E0, bin.E1);
                  guess = Expression.CreateITE(test, BminusA, AminusB);
                } else if (bin.E0.Type.IsBigOrdinalType) {
                  // if either of the operands is a literal, pick the other; otherwise, don't make any guess
                  if (Expression.StripParens(bin.E0) is LiteralExpr) {
                    guess = bin.E1;
                  } else if (Expression.StripParens(bin.E1) is LiteralExpr) {
                    guess = bin.E0;
                  }
                }
                break;
              case BinaryExpr.ResolvedOpcode.SetNeq:
                if (bin.E0.Type.AsSetType.Finite) {
                  // use |A - B| + |B - A|, but specialize it for the case where A or B is the empty set
                  if (LiteralExpr.IsEmptySet(bin.E0)) {
                    guess = bin.E1;
                  } else if (LiteralExpr.IsEmptySet(bin.E1)) {
                    guess = bin.E0;
                  } else {
                    var x = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E0, bin.E1), builtIns);
                    var y = Expression.CreateCardinality(Expression.CreateSetDifference(bin.E1, bin.E0), builtIns);
                    guess = Expression.CreateAdd(x, y);
                  }
                }
                break;
              case BinaryExpr.ResolvedOpcode.MultiSetNeq:
                // use |A - B| + |B - A|, but specialize it for the case where A or B is the empty multiset
                if (LiteralExpr.IsEmptyMultiset(bin.E0)) {
                  guess = bin.E1;
                } else if (LiteralExpr.IsEmptyMultiset(bin.E1)) {
                  guess = bin.E0;
                } else {
                  var x = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E0, bin.E1), builtIns);
                  var y = Expression.CreateCardinality(Expression.CreateMultisetDifference(bin.E1, bin.E0), builtIns);
                  guess = Expression.CreateAdd(x, y);
                }
                break;
              case BinaryExpr.ResolvedOpcode.SeqNeq:
                // if either operand is [], then use the other
                if (LiteralExpr.IsEmptySequence(bin.E0)) {
                  guess = bin.E1;
                } else if (LiteralExpr.IsEmptySequence(bin.E1)) {
                  guess = bin.E0;
                }
                break;
              default:
                break;
            }
            if (bin.E0.Type.AsSetType != null) {
              neutralValue = new SetDisplayExpr(bin.tok, bin.E0.Type.AsSetType.Finite, new List<Expression>()) {
                Type = bin.E0.Type.NormalizeExpand()
              };
            } else if (bin.E0.Type.AsMultiSetType != null) {
              neutralValue = new MultiSetDisplayExpr(bin.tok, new List<Expression>()) {
                Type = bin.E0.Type.NormalizeExpand()
              };
            } else if (bin.E0.Type.AsSeqType != null) {
              neutralValue = new SeqDisplayExpr(bin.tok, new List<Expression>()) {
                Type = bin.E0.Type.NormalizeExpand()
              };
            } else if (bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
              neutralValue = Expression.CreateRealLiteral(bin.tok, BaseTypes.BigDec.FromInt(-1));
            }
          }
          if (guess != null) {
            if (prefix != null) {
              // Make the following guess:  if prefix then guess else neutralValue
              guess = Expression.CreateITE(prefix, guess, neutralValue);
            }
            theDecreases.Add(AutoGeneratedExpression.Create(guess));
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
      if (loopStmt.InferredDecreases && theDecreases.Count != 0) {
        string s = "decreases " + Util.Comma(theDecreases, Printer.ExprToString);
        reporter.Info(MessageSource.Resolver, loopStmt.Tok, s);
      }
    }
    private Expression VarDotMethod(IToken tok, string varname, string methodname) {
      return new ApplySuffix(tok, null, new ExprDotName(tok, new IdentifierExpr(tok, varname), methodname, null), new List<ActualBinding>(), tok);
    }

    private Expression makeTemp(String prefix, AssignOrReturnStmt s, ResolutionContext resolutionContext, Expression ex) {
      var temp = FreshTempVarName(prefix, resolutionContext.CodeContext);
      var locvar = new LocalVariable(s.RangeToken, temp, ex.Type, false);
      var id = new IdentifierExpr(s.Tok, temp);
      var idlist = new List<Expression>() { id };
      var lhss = new List<LocalVariable>() { locvar };
      var rhss = new List<AssignmentRhs>() { new ExprRhs(ex) };
      var up = new UpdateStmt(s.RangeToken, idlist, rhss);
      s.ResolvedStatements.Add(new VarDeclStmt(s.RangeToken, lhss, up));
      return id;
    }

    /// <summary>
    /// Desugars "y, ... :- MethodOrExpression" into
    /// var temp;
    /// temp, ... := MethodOrExpression;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    /// y := temp.Extract();
    ///
    /// If the type of MethodExpression does not have an Extract, then the desugaring is
    /// var temp;
    /// temp, y, ... := MethodOrExpression;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    ///
    /// If there are multiple RHSs then "y, ... :- Expression, ..." becomes
    /// var temp;
    /// temp, ... := Expression, ...;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    /// y := temp.Extract();
    /// OR
    /// var temp;
    /// temp, y, ... := Expression, ...;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    ///
    /// and "y, ... :- expect MethodOrExpression, ..." into
    /// var temp, [y, ] ... := MethodOrExpression, ...;
    /// expect !temp.IsFailure(), temp.PropagateFailure();
    /// [y := temp.Extract();]
    ///
    /// and saves the result into s.ResolvedStatements.
    /// This is also known as the "elephant operator"
    /// </summary>
    private void ResolveAssignOrReturnStmt(AssignOrReturnStmt s, ResolutionContext resolutionContext) {
      // TODO Do I have any responsibilities regarding the use of resolutionContext? Is it mutable?

      // We need to figure out whether we are using a status type that has Extract or not,
      // as that determines how the AssignOrReturnStmt is desugared. Thus if the Rhs is a
      // method call we need to know which one (to inspect its first output); if RHs is a
      // list of expressions, we need to know the type of the first one. For all of this we have
      // to do some partial type resolution.

      bool expectExtract = s.Lhss.Count != 0; // default value if we cannot determine and inspect the type
      Type firstType = null;
      Method call = null;
      if ((s.Rhss == null || s.Rhss.Count == 0) && s.Rhs.Expr is ApplySuffix asx) {
        ResolveApplySuffix(asx, resolutionContext, true);
        call = (asx.Lhs.Resolved as MemberSelectExpr)?.Member as Method;
        if (call != null) {
          // We're looking at a method call
          var typeMap = (asx.Lhs.Resolved as MemberSelectExpr)?.TypeArgumentSubstitutionsWithParents();
          if (call.Outs.Count != 0) {
            firstType = call.Outs[0].Type.Subst(typeMap);
          } else {
            reporter.Error(MessageSource.Resolver, s.Rhs.tok, "Expected {0} to have a Success/Failure output value, but the method returns nothing.", call.Name);
          }
        } else {
          // We're looking at a call to a function. Treat it like any other expression.
          firstType = asx.Type;
        }
      } else {
        ResolveExpression(s.Rhs.Expr, resolutionContext);
        firstType = s.Rhs.Expr.Type;
      }

      var method = (Method)resolutionContext.CodeContext;
      if (method.Outs.Count == 0 && s.KeywordToken == null) {
        reporter.Error(MessageSource.Resolver, s.Tok, "A method containing a :- statement must have an out-parameter ({0})", method.Name);
        return;
      }
      if (firstType != null) {
        firstType = PartiallyResolveTypeForMemberSelection(s.Rhs.tok, firstType);
        if (firstType.AsTopLevelTypeWithMembers != null) {
          if (firstType.AsTopLevelTypeWithMembers.Members.Find(x => x.Name == "IsFailure") == null) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "member IsFailure does not exist in {0}, in :- statement", firstType);
            return;
          }
          expectExtract = firstType.AsTopLevelTypeWithMembers.Members.Find(x => x.Name == "Extract") != null;
          if (expectExtract && call == null && s.Lhss.Count != 1 + s.Rhss.Count) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "number of lhs ({0}) must match number of rhs ({1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, 1 + s.Rhss.Count, firstType);
            return;
          } else if (expectExtract && call != null && s.Lhss.Count != call.Outs.Count) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, call.Outs.Count, firstType);
            return;

          } else if (!expectExtract && call == null && s.Lhss.Count != s.Rhss.Count) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "number of lhs ({0}) must be one less than number of rhs ({1}) for a rhs type ({2}) without member Extract", s.Lhss.Count, 1 + s.Rhss.Count, firstType);
            return;

          } else if (!expectExtract && call != null && s.Lhss.Count != call.Outs.Count - 1) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) without member Extract", s.Lhss.Count, call.Outs.Count - 1, firstType);
            return;
          }
        } else {
          reporter.Error(MessageSource.Resolver, s.Tok,
            $"The type of the first expression to the right of ':-' could not be determined to be a failure type (got '{firstType}')");
          return;
        }
      } else {
        reporter.Error(MessageSource.Resolver, s.Tok,
          "Internal Error: Unknown failure type in :- statement");
        return;
      }

      Expression lhsExtract = null;
      if (expectExtract) {
        if (resolutionContext.CodeContext is Method caller && caller.Outs.Count == 0 && s.KeywordToken == null) {
          reporter.Error(MessageSource.Resolver, s.Rhs.tok, "Expected {0} to have a Success/Failure output value", caller.Name);
          return;
        }

        lhsExtract = s.Lhss[0];
        var lhsResolved = s.Lhss[0].Resolved;
        // Make a new unresolved expression
        if (lhsResolved is MemberSelectExpr lexr) {
          Expression id = Expression.AsThis(lexr.Obj) != null ? lexr.Obj : makeTemp("recv", s, resolutionContext, lexr.Obj);
          var lex = lhsExtract as ExprDotName; // might be just a NameSegment
          lhsExtract = new ExprDotName(lexr.tok, id, lexr.MemberName, lex == null ? null : lex.OptTypeArguments);
        } else if (lhsResolved is SeqSelectExpr lseq) {
          if (!lseq.SelectOne || lseq.E0 == null) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "Element ranges not allowed as l-values");
            return;
          }
          Expression id = makeTemp("recv", s, resolutionContext, lseq.Seq);
          Expression id0 = id0 = makeTemp("idx", s, resolutionContext, lseq.E0);
          lhsExtract = new SeqSelectExpr(lseq.tok, lseq.SelectOne, id, id0, null, lseq.CloseParen);
          lhsExtract.Type = lseq.Type;
        } else if (lhsResolved is MultiSelectExpr lmulti) {
          Expression id = makeTemp("recv", s, resolutionContext, lmulti.Array);
          var idxs = new List<Expression>();
          foreach (var i in lmulti.Indices) {
            Expression idx = makeTemp("idx", s, resolutionContext, i);
            idxs.Add(idx);
          }
          lhsExtract = new MultiSelectExpr(lmulti.tok, id, idxs);
          lhsExtract.Type = lmulti.Type;
        } else if (lhsResolved is IdentifierExpr) {
          // do nothing
        } else {
          Contract.Assert(false, "Internal error: unexpected option in ResolveAssignOrReturnStmt");
        }
      }
      var temp = FreshTempVarName("valueOrError", resolutionContext.CodeContext);
      var lhss = new List<LocalVariable>() { new LocalVariable(s.RangeToken, temp, new InferredTypeProxy(), false) };
      // "var temp ;"
      s.ResolvedStatements.Add(new VarDeclStmt(s.RangeToken, lhss, null));
      var lhss2 = new List<Expression>() { new IdentifierExpr(s.Tok, temp) };
      for (int k = (expectExtract ? 1 : 0); k < s.Lhss.Count; ++k) {
        lhss2.Add(s.Lhss[k]);
      }
      List<AssignmentRhs> rhss2 = new List<AssignmentRhs>() { s.Rhs };
      if (s.Rhss != null) {
        s.Rhss.ForEach(e => rhss2.Add(e));
      }
      if (s.Rhss != null && s.Rhss.Count > 0) {
        if (lhss2.Count != rhss2.Count) {
          reporter.Error(MessageSource.Resolver, s.Tok,
            "Mismatch in expected number of LHSs and RHSs");
          if (lhss2.Count < rhss2.Count) {
            rhss2.RemoveRange(lhss2.Count, rhss2.Count - lhss2.Count);
          } else {
            lhss2.RemoveRange(rhss2.Count, lhss2.Count - rhss2.Count);
          }
        }
      }
      // " temp, ... := MethodOrExpression, ...;"
      UpdateStmt up = new UpdateStmt(s.RangeToken, lhss2, rhss2);
      if (expectExtract) {
        up.OriginalInitialLhs = s.Lhss.Count == 0 ? null : s.Lhss[0];
      }
      s.ResolvedStatements.Add(up);

      if (s.KeywordToken != null) {
        var notFailureExpr = new UnaryOpExpr(s.Tok, UnaryOpExpr.Opcode.Not, VarDotMethod(s.Tok, temp, "IsFailure"));
        Statement ss = null;
        if (s.KeywordToken.Token.val == "expect") {
          // "expect !temp.IsFailure(), temp"
          ss = new ExpectStmt(new RangeToken(s.Tok, s.EndToken), notFailureExpr, new IdentifierExpr(s.Tok, temp), s.KeywordToken.Attrs);
        } else if (s.KeywordToken.Token.val == "assume") {
          ss = new AssumeStmt(new RangeToken(s.Tok, s.EndToken), notFailureExpr, s.KeywordToken.Attrs);
        } else if (s.KeywordToken.Token.val == "assert") {
          ss = new AssertStmt(new RangeToken(s.Tok, s.EndToken), notFailureExpr, null, null, s.KeywordToken.Attrs);
        } else {
          Contract.Assert(false, $"Invalid token in :- statement: {s.KeywordToken.Token.val}");
        }
        s.ResolvedStatements.Add(ss);
      } else {
        var enclosingOutParameter = ((Method)resolutionContext.CodeContext).Outs[0];
        var ident = new IdentifierExpr(s.Tok, enclosingOutParameter.Name);
        // resolve it here to avoid capture into more closely declared local variables
        Contract.Assert(enclosingOutParameter.Type != null);  // this confirms our belief that the out-parameter has already been resolved
        ident.Var = enclosingOutParameter;
        ident.Type = ident.Var.Type;

        s.ResolvedStatements.Add(
          // "if temp.IsFailure()"
          new IfStmt(s.RangeToken, false, VarDotMethod(s.Tok, temp, "IsFailure"),
            // THEN: { out := temp.PropagateFailure(); return; }
            new BlockStmt(s.RangeToken, new List<Statement>() {
              new UpdateStmt(s.RangeToken,
                new List<Expression>() { ident },
                new List<AssignmentRhs>() {new ExprRhs(VarDotMethod(s.Tok, temp, "PropagateFailure"))}
                ),
              new ReturnStmt(s.RangeToken, null),
            }),
            // ELSE: no else block
            null
          ));
      }

      if (expectExtract) {
        // "y := temp.Extract();"
        var lhs = s.Lhss[0];
        s.ResolvedStatements.Add(
          new UpdateStmt(s.RangeToken,
            new List<Expression>() { lhsExtract },
            new List<AssignmentRhs>() { new ExprRhs(VarDotMethod(s.Tok, temp, "Extract")) }
          ));
        // The following check is not necessary, because the ghost mismatch is caught later.
        // However the error message here is much clearer.
        var m = ResolveMember(s.Tok, firstType, "Extract", out _);
        if (m != null && m.IsGhost && !AssignStmt.LhsIsToGhostOrAutoGhost(lhs)) {
          reporter.Error(MessageSource.Resolver, lhs.tok,
            "The Extract member may not be ghost unless the initial LHS is ghost");
        }
      }

      s.ResolvedStatements.ForEach(a => ResolveStatement(a, resolutionContext));
      EnsureSupportsErrorHandling(s.Tok, firstType, expectExtract, s.KeywordToken != null);
    }

    private void EnsureSupportsErrorHandling(IToken tok, Type tp, bool expectExtract, bool hasKeywordToken) {
      // The "method not found" errors which will be generated here were already reported while
      // resolving the statement, so we don't want them to reappear and redirect them into a sink.
      var origReporter = this.reporter;
      this.reporter = new ErrorReporterSink();

      if (hasKeywordToken) {
        if (ResolveMember(tok, tp, "IsFailure", out _) == null ||
            (ResolveMember(tok, tp, "Extract", out _) != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          origReporter.Error(MessageSource.Resolver, tok,
            "The right-hand side of ':-', which is of type '{0}', with a keyword token must have members 'IsFailure()', {1} 'Extract()'",
            tp, expectExtract ? "and" : "but not");
        }
      } else {
        if (ResolveMember(tok, tp, "IsFailure", out _) == null ||
            ResolveMember(tok, tp, "PropagateFailure", out _) == null ||
            (ResolveMember(tok, tp, "Extract", out _) != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          origReporter.Error(MessageSource.Resolver, tok,
            "The right-hand side of ':-', which is of type '{0}', must have members 'IsFailure()', 'PropagateFailure()', {1} 'Extract()'",
            tp, expectExtract ? "and" : "but not");
        }
      }


      // The following checks are not necessary, because the ghost mismatch is caught later.
      // However the error messages here are much clearer.
      var m = ResolveMember(tok, tp, "IsFailure", out _);
      if (m != null && m.IsGhost) {
        origReporter.Error(MessageSource.Resolver, tok,
          $"The IsFailure member may not be ghost (type {tp} used in :- statement)");
      }
      m = ResolveMember(tok, tp, "PropagateFailure", out _);
      if (!hasKeywordToken && m != null && m.IsGhost) {
        origReporter.Error(MessageSource.Resolver, tok,
          $"The PropagateFailure member may not be ghost (type {tp} used in :- statement)");
      }

      this.reporter = origReporter;
    }

    /// <summary>
    /// Check that "stmt" is a valid statment for the body of an assert-by, forall,
    /// or calc-hint statement. In particular, check that the local variables assigned in
    /// the bodies of these statements are declared in the statements, not in some enclosing
    /// context. 
    /// </summary>
    public void CheckLocalityUpdates(Statement stmt, ISet<LocalVariable> localsAllowedInUpdates, string where) {
      Contract.Requires(stmt != null);
      Contract.Requires(localsAllowedInUpdates != null);
      Contract.Requires(where != null);

      if (stmt is AssertStmt || stmt is ForallStmt || stmt is CalcStmt || stmt is ModifyStmt) {
        // don't recurse, since CheckHintRestrictions will be called on that assert-by separately
        return;
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          CheckLocalityUpdatesLhs(lhs, localsAllowedInUpdates, @where);
        }
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        CheckLocalityUpdatesLhs(s.Lhs, localsAllowedInUpdates, @where);
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        foreach (var lhs in s.Lhs) {
          CheckLocalityUpdatesLhs(lhs, localsAllowedInUpdates, @where);
        }
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        s.Locals.Iter(local => localsAllowedInUpdates.Add(local));
      } else if (stmt is ModifyStmt) {
        // no further complaints (note, ghost interests have already checked for 'modify' statements)
      } else if (stmt is BlockStmt) {
        localsAllowedInUpdates = new HashSet<LocalVariable>(localsAllowedInUpdates);
        // use this new set for the recursive calls
      }

      foreach (var ss in stmt.SubStatements) {
        CheckLocalityUpdates(ss, localsAllowedInUpdates, where);
      }
    }

    void CheckLocalityUpdatesLhs(Expression lhs, ISet<LocalVariable> localsAllowedInUpdates, string @where) {
      Contract.Requires(lhs != null);
      Contract.Requires(localsAllowedInUpdates != null);
      Contract.Requires(where != null);

      lhs = lhs.Resolved;
      if (lhs is IdentifierExpr idExpr && !localsAllowedInUpdates.Contains(idExpr.Var)) {
        reporter.Error(MessageSource.Resolver, lhs.tok, "{0} is not allowed to update a variable it doesn't declare", where);
      }
    }

    class LazyString_OnTypeEquals {
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

    void FindAllMembers(ClassDecl cl, string memberName, ISet<MemberDecl> foundSoFar) {
      Contract.Requires(cl != null);
      Contract.Requires(memberName != null);
      Contract.Requires(foundSoFar != null);
      MemberDecl member;
      if (classMembers[cl].TryGetValue(memberName, out member)) {
        foundSoFar.Add(member);
      }
      cl.ParentTraitHeads.ForEach(trait => FindAllMembers(trait, memberName, foundSoFar));
    }

    // TODO move
    public static UserDefinedType GetThisType(IToken tok, TopLevelDeclWithMembers cl) {
      Contract.Requires(tok != null);
      Contract.Requires(cl != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      if (cl is ClassDecl cls && cls.NonNullTypeDecl != null) {
        return UserDefinedType.FromTopLevelDecl(tok, cls.NonNullTypeDecl, cls.TypeArgs);
      } else {
        return UserDefinedType.FromTopLevelDecl(tok, cl, cl.TypeArgs);
      }
    }

    // TODO move
    public static UserDefinedType GetReceiverType(IToken tok, MemberDecl member) {
      Contract.Requires(tok != null);
      Contract.Requires(member != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      return GetThisType(tok, (TopLevelDeclWithMembers)member.EnclosingClass);
    }

    Label/*?*/ ResolveDominatingLabelInExpr(IToken tok, string/*?*/ labelName, string expressionDescription, ResolutionContext resolutionContext) {
      Contract.Requires(tok != null);
      Contract.Requires(expressionDescription != null);
      Contract.Requires(resolutionContext != null);

      Label label = null;
      if (!resolutionContext.IsTwoState) {
        reporter.Error(MessageSource.Resolver, tok, $"{expressionDescription} expressions are not allowed in this context");
      } else if (labelName != null) {
        label = DominatingStatementLabels.Find(labelName);
        if (label == null) {
          reporter.Error(MessageSource.Resolver, tok, $"no label '{labelName}' in scope at this time");
        }
      }
      return label;
    }

    private Expression VarDotFunction(IToken tok, string varname, string functionname) {
      return new ApplySuffix(tok, null, new ExprDotName(tok, new IdentifierExpr(tok, varname), functionname, null), new List<ActualBinding>(), tok);
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
    public void ResolveLetOrFailExpr(LetOrFailExpr expr, ResolutionContext resolutionContext) {
      var temp = FreshTempVarName("valueOrError", resolutionContext.CodeContext);
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

      ResolveExpression(expr.ResolvedExpression, resolutionContext);
      expr.Type = expr.ResolvedExpression.Type;
      bool expectExtract = (expr.Lhs != null);
      EnsureSupportsErrorHandling(expr.tok, PartiallyResolveTypeForMemberSelection(expr.tok, tempType), expectExtract, false);
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
    /// Adds appropriate type constraints that says "expr" evaluates to an integer or (if "allowBitVector" is true) a
    /// a bitvector.  The "errFormat" string can contain a "{0}", referring to the name of the type of "expr".
    /// </summary>
    void ConstrainToIntegerType(Expression expr, bool allowBitVector, string errFormat) {
      Contract.Requires(expr != null);
      Contract.Requires(errFormat != null);
      var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, errFormat, expr.Type);
      ConstrainToIntegerType(expr.tok, expr.Type, allowBitVector, err);
    }

    /// <summary>
    /// Resolves a NestedMatchExpr by
    /// 1 - checking that all of its patterns are linear
    /// 2 - desugaring it into a decision tree of MatchExpr and ITEEXpr (for constant matching)
    /// 3 - resolving the generated (sub)expression.
    /// </summary>
    void ResolveNestedMatchExpr(NestedMatchExpr nestedMatchExpr, ResolutionContext resolutionContext) {
      Contract.Requires(nestedMatchExpr != null);
      Contract.Requires(resolutionContext != null);

      nestedMatchExpr.Resolve(this, resolutionContext);
    }

    void ResolveMatchExpr(MatchExpr me, ResolutionContext resolutionContext) {
      Contract.Requires(me != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(me.OrigUnresolved == null);

      // first, clone the original match expression
      me.OrigUnresolved = (MatchExpr)new ClonerKeepParensExpressions().CloneExpr(me);
      ResolveExpression(me.Source, resolutionContext);

      Contract.Assert(me.Source.Type != null);  // follows from postcondition of ResolveExpression

      var sourceType = PartiallyResolveTypeForMemberSelection(me.Source.tok, me.Source.Type).NormalizeExpand();

      var dtd = sourceType.AsDatatype;
      var subst = new Dictionary<TypeParameter, Type>();
      Dictionary<string, DatatypeCtor> ctors;
      if (dtd == null) {
        reporter.Error(MessageSource.Resolver, me.Source, "the type of the match source expression must be a datatype (instead found {0})", me.Source.Type);
        ctors = null;
      } else {
        Contract.Assert(sourceType != null);  // dtd and sourceType are set together above
        ctors = dtd.ConstructorsByName;
        Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage

        // build the type-parameter substitution map for this use of the datatype
        subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs);
      }

      ISet<string> memberNamesUsed = new HashSet<string>();
      me.Type = new InferredTypeProxy();
      foreach (MatchCaseExpr mc in me.Cases) {
        if (ctors != null) {
          Contract.Assert(dtd != null);
          var ctorId = mc.Ctor.Name;
          if (me.Source.Type.AsDatatype is TupleTypeDecl) {
            var tuple = (TupleTypeDecl)me.Source.Type.AsDatatype;
            ctorId = BuiltIns.TupleTypeCtorName(tuple.Dims);
          }
          if (!ctors.ContainsKey(ctorId)) {
            reporter.Error(MessageSource.Resolver, mc.tok, "member '{0}' does not exist in datatype '{1}'", ctorId, dtd.Name);
          } else {
            if (mc.Ctor.Formals.Count != mc.Arguments.Count) {
              if (me.Source.Type.AsDatatype is TupleTypeDecl) {
                reporter.Error(MessageSource.Resolver, mc.tok, "case arguments count does not match source arguments count");
              } else {
                reporter.Error(MessageSource.Resolver, mc.tok, "member {0} has wrong number of formals (found {1}, expected {2})", ctorId, mc.Arguments.Count, mc.Ctor.Formals.Count);
              }
            }
            if (memberNamesUsed.Contains(ctorId)) {
              reporter.Error(MessageSource.Resolver, mc.tok, "member {0} appears in more than one case", mc.Ctor.Name);
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
            ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            if (i < mc.Ctor.Formals.Count) {
              Formal formal = mc.Ctor.Formals[i];
              Type st = formal.Type.Subst(subst);
              ConstrainSubtypeRelation(v.Type, st, me,
                "the declared type of the formal ({0}) does not agree with the corresponding type in the constructor's signature ({1})", v.Type, st);
              v.IsGhost = formal.IsGhost;
            }
            i++;
          }
        }

        ResolveExpression(mc.Body, resolutionContext);

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

    void ResolveCasePattern<VT>(CasePattern<VT> pat, Type sourceType, ResolutionContext resolutionContext)
      where VT : class, IVariable {
      Contract.Requires(pat != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(resolutionContext != null);

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
          if (dtd.ConstructorsByName.TryGetValue(pat.Id, out ctor)) {
            if (pat.Arguments == null) {
              if (ctor.Formals.Count != 0) {
                // Leave this as a variable
              } else {
                // Convert to a constructor
                pat.MakeAConstructor();
                pat.Ctor = ctor;
                pat.Var = default(VT);
              }
            } else {
              pat.Ctor = ctor;
              pat.Var = default(VT);
            }
          }
        }
      }

      if (pat.Var != null) {
        // this is a simple resolution
        var v = pat.Var;
        if (resolutionContext.IsGhost) {
          v.MakeGhost();
        }
        ResolveType(v.Tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        // Note, the following type constraint checks that the RHS type can be assigned to the new variable on the left. In particular, it
        // does not check that the entire RHS can be assigned to something of the type of the pattern on the left.  For example, consider
        // a type declared as "datatype Atom<T> = MakeAtom(T)", where T is a non-variant type argument.  Suppose the RHS has type Atom<nat>
        // and that the LHS is the pattern MakeAtom(x: int).  This is okay, despite the fact that Atom<nat> is not assignable to Atom<int>.
        // The reason is that the purpose of the pattern on the left is really just to provide a skeleton to introduce bound variables in.
        EagerAddAssignableConstraint(v.Tok, v.Type, sourceType, "type of corresponding source/RHS ({1}) does not match type of bound variable ({0})");
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
        if (pat.Arguments == null) {
          if (ctor.Formals.Count == 0) {
            // The Id matches a constructor of the correct type and 0 arguments,
            // so make it a nullary constructor, not a variable
            pat.MakeAConstructor();
          }
        } else {
          if (ctor.Formals.Count != pat.Arguments.Count) {
            reporter.Error(MessageSource.Resolver, pat.tok, "pattern for constructor {0} has wrong number of formals (found {1}, expected {2})", pat.Id, pat.Arguments.Count, ctor.Formals.Count);
          }
        }
        // build the type-parameter substitution map for this use of the datatype
        Contract.Assert(dtd.TypeArgs.Count == udt.TypeArgs.Count);  // follows from the type previously having been successfully resolved
        var subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, udt.TypeArgs);
        // recursively call ResolveCasePattern on each of the arguments
        var j = 0;
        if (pat.Arguments != null) {
          foreach (var arg in pat.Arguments) {
            if (j < ctor.Formals.Count) {
              var formal = ctor.Formals[j];
              Type st = formal.Type.Subst(subst);
              ResolveCasePattern(arg, st, resolutionContext.WithGhost(resolutionContext.IsGhost || formal.IsGhost));
            }
            j++;
          }
        }
        if (j == ctor.Formals.Count) {
          pat.AssembleExpr(udt.TypeArgs);
        }
      }
    }

    private List<DefaultValueExpression> allDefaultValueExpressions = new List<DefaultValueExpression>();

    /// <summary>
    /// This method is called at the tail end of Pass1 of the Resolver.
    /// </summary>
    void FillInDefaultValueExpressions() {
      var visited = new Dictionary<DefaultValueExpression, WorkProgress>();
      foreach (var e in allDefaultValueExpressions) {
        FillInDefaultValueExpression(e, visited);
      }
      allDefaultValueExpressions.Clear();
    }

    enum WorkProgress { BeingVisited, Done }

    void FillInDefaultValueExpression(DefaultValueExpression expr, Dictionary<DefaultValueExpression, WorkProgress> visited) {
      Contract.Requires(expr != null);
      Contract.Requires(visited != null);
      Contract.Ensures(expr.ResolvedExpression != null);

      if (visited.TryGetValue(expr, out var p)) {
        if (p == WorkProgress.Done) {
          Contract.Assert(expr.ResolvedExpression != null);
        } else {
          // there is a cycle
          reporter.Error(MessageSource.Resolver, expr, "default-valued expressions are cyclicly dependent; this is not allowed, since it would cause infinite expansion");
          // nevertheless, to avoid any issues in the resolver, fill in the .ResolvedExpression field with something
          expr.ResolvedExpression = Expression.CreateBoolLiteral(expr.tok, false);
        }
        return;
      }
      Contract.Assert(expr.ResolvedExpression == null);

      visited.Add(expr, WorkProgress.BeingVisited);
      var s = new DefaultValueSubstituter(this, visited, expr.Receiver, expr.SubstMap, expr.TypeMap);
      expr.ResolvedExpression = s.Substitute(expr.Formal.DefaultValue);
      visited[expr] = WorkProgress.Done;
    }

    class DefaultValueSubstituter : Substituter {
      private readonly Resolver resolver;
      private readonly Dictionary<DefaultValueExpression, WorkProgress> visited;
      public DefaultValueSubstituter(Resolver resolver, Dictionary<DefaultValueExpression, WorkProgress> visited,
        Expression /*?*/ receiverReplacement, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
        : base(receiverReplacement, substMap, typeMap) {
        Contract.Requires(resolver != null);
        Contract.Requires(visited != null);
        this.resolver = resolver;
        this.visited = visited;
      }

      public override Expression Substitute(Expression expr) {
        if (expr is DefaultValueExpression dve) {
          resolver.FillInDefaultValueExpression(dve, visited);
          Contract.Assert(dve.ResolvedExpression != null); // postcondition of FillInDefaultValueExpression
        }
        return base.Substitute(expr);
      }
    }

    private Dictionary<TypeParameter, Type> BuildTypeArgumentSubstitute(Dictionary<TypeParameter, Type> typeArgumentSubstitutions, Type/*?*/ receiverTypeBound = null) {
      Contract.Requires(typeArgumentSubstitutions != null);

      var subst = new Dictionary<TypeParameter, Type>();
      foreach (var entry in typeArgumentSubstitutions) {
        subst.Add(entry.Key, entry.Value);
      }

      if (SelfTypeSubstitution != null) {
        foreach (var entry in SelfTypeSubstitution) {
          subst.Add(entry.Key, entry.Value);
        }
      }

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
            var v = entry.Value.Subst(subst);
            subst.Add(entry.Key, v);
          }
        }
      }

      return subst;
    }

    public static string GhostPrefix(bool isGhost) {
      return isGhost ? "ghost " : "";
    }

    private static ModuleSignature GetSignatureExt(ModuleSignature sig, bool useCompileSignatures) {
      Contract.Requires(sig != null);
      Contract.Ensures(Contract.Result<ModuleSignature>() != null);
      if (useCompileSignatures) {
        while (sig.CompileSignature != null) {
          sig = sig.CompileSignature;
        }
      }
      return sig;
    }

    private ModuleSignature GetSignature(ModuleSignature sig) {
      return GetSignatureExt(sig, useCompileSignatures);
    }

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
            Substituter sub = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
            c = Expression.CreateAnd(c, sub.Substitute(dd.Constraint));
          }
          return c;
        } else if (udt.ResolvedClass is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)udt.ResolvedClass;
          var c = GetImpliedTypeConstraint(e, dd.RhsWithArgument(udt.TypeArgs));
          Dictionary<IVariable, Expression/*!*/> substMap = new Dictionary<IVariable, Expression>();
          substMap.Add(dd.Var, e);
          Substituter sub = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
          c = Expression.CreateAnd(c, sub.Substitute(dd.Constraint));
          return c;
        }
      }
      return Expression.CreateBoolLiteral(e.tok, true);
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
      } else if (expr is NestedMatchExpr) {
        var e = (NestedMatchExpr)expr;
        var s = FreeVariables(e.Source);
        foreach (NestedMatchCaseExpr mc in e.Cases) {
          var t = FreeVariables(mc.Body);
          foreach (var bv in mc.Pat.Children.OfType<IdPattern>()) {
            if (bv.BoundVar != null) {
              t.Remove(bv.BoundVar);
            }
          }
          s.UnionWith(t);
        }
        return s;
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var s = FreeVariables(e.Source);
        foreach (MatchCaseExpr mc in e.Cases) {
          var t = FreeVariables(mc.Body);
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

    /// <summary>
    /// An error message for the type constraint for between a sequence select expression's actual and expected types.
    /// If resolution successfully determines the sequences' element types, then this derived class mentions those
    /// element types as clarifying context to the user.
    /// </summary>
    private class SeqSelectOneErrorMsg : TypeConstraint.ErrorMsgWithToken {
      private static readonly string BASE_MESSAGE_FORMAT = "sequence has type {0} which is incompatible with expected type {1}";
      private static readonly string ELEMENT_DETAIL_MESSAGE_FORMAT = " (element type {0} is incompatible with {1})";

      private readonly Type exprSeqType;
      private readonly Type expectedSeqType;

      public override string Msg {
        get {
          // Resolution might resolve exprSeqType/expectedSeqType to not be sequences at all.
          // In that case, it isn't possible to get the corresponding element types.
          var rawExprElementType = exprSeqType.AsSeqType?.Arg;
          var rawExpectedElementType = expectedSeqType.AsSeqType?.Arg;
          if (rawExprElementType == null || rawExpectedElementType == null) {
            return base.Msg;
          }

          var elementTypes = RemoveAmbiguity(new object[] { rawExprElementType, rawExpectedElementType });
          Contract.Assert(elementTypes.Length == 2);
          var exprElementType = elementTypes[0].ToString();
          var expectedElementType = elementTypes[1].ToString();

          string detail = string.Format(ELEMENT_DETAIL_MESSAGE_FORMAT, exprElementType, expectedElementType);
          return base.Msg + detail;
        }
      }

      public SeqSelectOneErrorMsg(IToken tok, Type exprSeqType, Type expectedSeqType)
        : base(tok, BASE_MESSAGE_FORMAT, exprSeqType, expectedSeqType) {
        Contract.Requires(exprSeqType != null);
        Contract.Requires(expectedSeqType != null);
        this.exprSeqType = exprSeqType;
        this.expectedSeqType = expectedSeqType;
      }
    }

    /// <summary>
    /// Note: this method is allowed to be called even if "type" does not make sense for "op", as might be the case if
    /// resolution of the binary expression failed.  If so, an arbitrary resolved opcode is returned.
    /// Usually, the type of the right-hand operand is used to determine the resolved operator (hence, the shorter
    /// name "operandType" instead of, say, "rightOperandType").
    /// </summary>
    public static BinaryExpr.ResolvedOpcode ResolveOp(BinaryExpr.Opcode op, Type leftOperandType, Type operandType) {
      Contract.Requires(leftOperandType != null);
      Contract.Requires(operandType != null);
      leftOperandType = leftOperandType.NormalizeExpand();
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
            return BinaryExpr.ResolvedOpcode.MapMerge;
          } else if (operandType is SeqType) {
            return BinaryExpr.ResolvedOpcode.Concat;
          } else {
            return BinaryExpr.ResolvedOpcode.Add;
          }
        case BinaryExpr.Opcode.Sub:
          if (leftOperandType is MapType) {
            return BinaryExpr.ResolvedOpcode.MapSubtraction;
          } else if (operandType is SetType) {
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
    /// This method adds to "friendlyCalls" all
    ///     inductive calls                                     if !co
    ///     greatest predicate calls and codatatype equalities  if co
    /// that occur in positive positions and not under
    ///     universal quantification                            if !co
    ///     existential quantification.                         if co
    /// If "expr" is the
    ///     precondition of a least lemma                       if !co
    ///     postcondition of a greatest lemma,                  if co
    /// then the "friendlyCalls" are the subexpressions that need to be replaced in order
    /// to create the
    ///     precondition                                        if !co
    ///     postcondition                                       if co
    /// of the corresponding prefix lemma.
    /// </summary>
    void CollectFriendlyCallsInExtremeLemmaSpecification(Expression expr, bool position, ISet<Expression> friendlyCalls, bool co, ExtremeLemma context) {
      Contract.Requires(expr != null);
      Contract.Requires(friendlyCalls != null);
      var visitor = new CollectFriendlyCallsInSpec_Visitor(this, friendlyCalls, co, context);
      visitor.Visit(expr, position ? CallingPosition.Positive : CallingPosition.Negative);
    }

    class CollectFriendlyCallsInSpec_Visitor : FindFriendlyCalls_Visitor {
      readonly ISet<Expression> friendlyCalls;
      readonly ExtremeLemma Context;
      public CollectFriendlyCallsInSpec_Visitor(Resolver resolver, ISet<Expression> friendlyCalls, bool co, ExtremeLemma context)
        : base(resolver, co, context.KNat) {
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
            if (IsCoContext ? fexp.Function is GreatestPredicate : fexp.Function is LeastPredicate) {
              if (Context.KNat != ((ExtremePredicate)fexp.Function).KNat) {
                resolver.KNatMismatchError(expr.tok, Context.Name, Context.TypeOfK, ((ExtremePredicate)fexp.Function).TypeOfK);
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

  abstract class ResolverTopDownVisitor<T> : TopDownVisitor<T> {
    protected Resolver resolver;
    public ResolverTopDownVisitor(Resolver resolver) {
      Contract.Requires(resolver != null);
      this.resolver = resolver;
    }
  }

  class CoCallResolution {
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

    public struct CoCallInfo {
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
      } else if (expr is NestedMatchExpr) {
        var e = (NestedMatchExpr)expr;
        foreach (var child in e.SubExpressions) {
          CheckCoCalls(child, destructionLevel, coContext, coCandidates);
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
        CheckCoCalls(e.Term, destructionLevel, coContext, coCandidates);
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
      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        var childValues = nestedMatchExpr.Cases.Select(child => GuaranteedCoCtorsAux(child.Body)).ToList();
        return childValues.Any() ? childValues.Min() : 0;
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



  // Looks for every non-ghost comprehensions, and if they are using a subset type,
  // check that the subset constraint is compilable. If it is not compilable, raises an error.
  public class SubsetConstraintGhostChecker : ProgramTraverser {
    public class FirstErrorCollector : ErrorReporter {
      public string FirstCollectedMessage = "";
      public IToken FirstCollectedToken = Token.NoToken;
      public bool Collected = false;

      public bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
        return Message(source, level, ErrorID.None, tok, msg);
      }
      public override bool Message(MessageSource source, ErrorLevel level, ErrorID errorID, IToken tok, string msg) {
        if (!Collected && level == ErrorLevel.Error) {
          FirstCollectedMessage = msg;
          FirstCollectedToken = tok;
          Collected = true;
        }
        return true;
      }

      public override int Count(ErrorLevel level) {
        return level == ErrorLevel.Error && Collected ? 1 : 0;
      }

      public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
        return Count(level);
      }
    }

    public ErrorReporter reporter;

    public SubsetConstraintGhostChecker(ErrorReporter reporter) {
      this.reporter = reporter;
    }

    protected override ContinuationStatus OnEnter(Statement stmt, string field, object parent) {
      return stmt != null && stmt.IsGhost ? skip : ok;
    }

    protected override ContinuationStatus OnEnter(MemberDecl memberDecl, string field, object parent) {
      // Includes functions and methods as well.
      // Ghost functions can have a compiled implementation.
      // We want to recurse only on the by method, not on the sub expressions of the function
      if (memberDecl == null || !memberDecl.IsGhost) { return ok; }
      if (memberDecl is Function f) {
        if (f.ByMethodDecl != null && Traverse(f.ByMethodDecl, "ByMethodDecl", f)) { return stop; }
        if (f.ByMethodDecl == null || f.ByMethodDecl.Body != f.ByMethodBody) {
          if (f.ByMethodBody != null && Traverse(f.ByMethodBody, "ByMethodBody", f)) { return stop; }
        }
      }
      return skip;
    }

    private bool IsFieldSpecification(string field, object parent) {
      return field != null && parent != null && (
        (parent is Statement && field == "SpecificationSubExpressions") ||
        (parent is Function && (field is "Req.E" or "Reads.E" or "Ens.E" or "Decreases.Expressions")) ||
        (parent is Method && (field is "Req.E" or "Mod.E" or "Ens.E" or "Decreases.Expressions"))
      );
    }

    public override bool Traverse(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
      if (expr == null) {
        return false;
      }
      if (IsFieldSpecification(field, parent)) {
        return false;
      }
      // Since we skipped ghost code, the code has to be compiled here. 
      if (expr is not ComprehensionExpr e) {
        return base.Traverse(expr, field, parent);
      }

      string what = e.WhatKind;

      if (e is ForallExpr || e is ExistsExpr || e is SetComprehension || e is MapComprehension) {
        foreach (var boundVar in e.BoundVars) {
          if (boundVar.Type.AsSubsetType is
          {
            Constraint: var constraint,
            ConstraintIsCompilable: false and var constraintIsCompilable
          } and var subsetTypeDecl
          ) {
            if (!subsetTypeDecl.CheckedIfConstraintIsCompilable) {
              // Builtin types were never resolved.
              constraintIsCompilable =
                ExpressionTester.CheckIsCompilable(null, constraint, new CodeContextWrapper(subsetTypeDecl, true));
              subsetTypeDecl.CheckedIfConstraintIsCompilable = true;
              subsetTypeDecl.ConstraintIsCompilable = constraintIsCompilable;
            }

            if (!constraintIsCompilable) {
              IToken finalToken = boundVar.tok;
              if (constraint.tok.line != 0) {
                var errorCollector = new FirstErrorCollector();
                ExpressionTester.CheckIsCompilable(null, errorCollector, constraint, new CodeContextWrapper(subsetTypeDecl, true));
                if (errorCollector.Collected) {
                  finalToken = new NestedToken(finalToken, errorCollector.FirstCollectedToken,
                    "The constraint is not compilable because " + errorCollector.FirstCollectedMessage
                  );
                }
              }
              this.reporter.Error(MessageSource.Resolver, finalToken,
                $"{boundVar.Type} is a subset type and its constraint is not compilable, hence it cannot yet be used as the type of a bound variable in {what}.");
            }
          }
        }
      }
      return base.Traverse(e, field, parent);
    }
  }
}
