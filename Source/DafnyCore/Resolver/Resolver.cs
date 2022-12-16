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

namespace Microsoft.Dafny {
  public partial class Resolver {
    readonly BuiltIns builtIns;

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

    FreshIdGenerator defaultTempVarIdGenerator = new FreshIdGenerator();

    string FreshTempVarName(string prefix, ICodeContext context) {
      var gen = context is Declaration decl ? decl.IdGenerator : defaultTempVarIdGenerator;
      return gen.FreshId(prefix);
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
        : base(pool.First().tok, name, m, new List<TypeParameter>(), null, false) {
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
        : base(pool.First().tok, name, true, pool.First().IsGhost, null, false) {
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

    readonly Dictionary<DatatypeDecl, Dictionary<string, DatatypeCtor>> datatypeCtors =
      new Dictionary<DatatypeDecl, Dictionary<string, DatatypeCtor>>();

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
      var floor = new SpecialField(Token.NoToken, "Floor", SpecialField.ID.Floor, null, false, false, false, Type.Int, null);
      floor.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Real].Members.Add(floor.Name, floor);

      var isLimit = new SpecialField(Token.NoToken, "IsLimit", SpecialField.ID.IsLimit, null, false, false, false,
        Type.Bool, null);
      isLimit.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isLimit.Name, isLimit);

      var isSucc = new SpecialField(Token.NoToken, "IsSucc", SpecialField.ID.IsSucc, null, false, false, false,
        Type.Bool, null);
      isSucc.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isSucc.Name, isSucc);

      var limitOffset = new SpecialField(Token.NoToken, "Offset", SpecialField.ID.Offset, null, false, false, false,
        Type.Int, null);
      limitOffset.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(limitOffset.Name, limitOffset);
      builtIns.ORDINAL_Offset = limitOffset;

      var isNat = new SpecialField(Token.NoToken, "IsNat", SpecialField.ID.IsNat, null, false, false, false, Type.Bool, null);
      isNat.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.BigOrdinal].Members.Add(isNat.Name, isNat);

      // Add "Keys", "Values", and "Items" to map, imap
      foreach (var typeVariety in new[] { ValuetypeVariety.Map, ValuetypeVariety.IMap }) {
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
      List<Formal> formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, null, false) };
      var rotateLeft = new SpecialFunction(Token.NoToken, "RotateLeft", prog.BuiltIns.SystemModule, false, false,
        new List<TypeParameter>(), formals, new SelfType(),
        new List<AttributedExpression>(), new List<FrameExpression>(), new List<AttributedExpression>(),
        new Specification<Expression>(new List<Expression>(), null), null, null, null);
      rotateLeft.EnclosingClass = valuetypeDecls[(int)ValuetypeVariety.Bitvector];
      rotateLeft.AddVisibilityScope(prog.BuiltIns.SystemModule.VisibilityScope, false);
      valuetypeDecls[(int)ValuetypeVariety.Bitvector].Members.Add(rotateLeft.Name, rotateLeft);

      formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, null, false) };
      var rotateRight = new SpecialFunction(Token.NoToken, "RotateRight", prog.BuiltIns.SystemModule, false, false,
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
      Contract.Invariant(cce.NonNullDictionaryAndValues(datatypeCtors) && Contract.ForAll(datatypeCtors.Values, v => cce.NonNullDictionaryAndValues(v)));
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
        rewriters.Add(new Auditor.Auditor(reporter,
          DafnyOptions.O.AuditorReportFile,
          DafnyOptions.O.AuditReportFormat,
          DafnyOptions.O.CompareAuditReport));
      }

      refinementTransformer = new RefinementTransformer(prog);
      rewriters.Add(refinementTransformer);
      rewriters.Add(new AutoContractsRewriter(reporter, builtIns));
      rewriters.Add(new OpaqueMemberRewriter(this.reporter));
      rewriters.Add(new AutoReqFunctionRewriter(this.reporter));
      rewriters.Add(new TimeLimitRewriter(reporter));
      rewriters.Add(new ForallStmtRewriter(reporter));
      rewriters.Add(new ProvideRevealAllRewriter(this.reporter));

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
      var systemModuleClassesWithNonNullTypes = new List<TopLevelDecl>(
        prog.BuiltIns.SystemModule.TopLevelDecls.Where(d => d is ClassDecl && ((ClassDecl)d).NonNullTypeDecl != null));
      foreach (var cl in systemModuleClassesWithNonNullTypes) {
        var d = ((ClassDecl)cl).NonNullTypeDecl;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, true, d);
        ResolveType(d.tok, d.Rhs, d, ResolveTypeOptionEnum.AllowPrefix, d.TypeArgs);
        allTypeParameters.PopMarker();
      }

      ResolveTopLevelDecls_Core(systemModuleClassesWithNonNullTypes, new Graph<IndDatatypeDecl>(), new Graph<CoDatatypeDecl>());

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
            var nw = cloner.CloneModuleDefinition(m, m.CompileName + "_Compile");
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
                m.IsRecursive = true;
              }
            }
          }
        }

        foreach (var rewriter in rewriters) {
          rewriter.PostCyclicityResolve(module);
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

    void FillInDefaultDecreasesClauses(Program prog) {
      Contract.Requires(prog != null);

      foreach (var module in prog.Modules()) {
        Contract.Assert(Type.GetScope() != null);
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls)) {
          ICallable m;
          string s;
          if (clbl is ExtremeLemma) {
            var prefixLemma = ((ExtremeLemma)clbl).PrefixLemma;
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
              s += "decreases " + Util.Comma(m.Decreases.Expressions, Printer.ExprToString);
              // Note, in the following line, we use the location information for "clbl", not "m".  These
              // are the same, except in the case where "clbl" is a GreatestLemma and "m" is a prefix lemma.
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

      if (clbl is ExtremePredicate) {
        // extreme predicates don't have decreases clauses
        return false;
      }

      var anyChangeToDecreases = false;
      var decr = clbl.Decreases.Expressions;
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
        if (clbl is Function || clbl is Method) {
          TopLevelDeclWithMembers enclosingType;
          if (clbl is Function fc && !fc.IsStatic) {
            enclosingType = (TopLevelDeclWithMembers)fc.EnclosingClass;
          } else if (clbl is Method mc && !mc.IsStatic) {
            enclosingType = (TopLevelDeclWithMembers)mc.EnclosingClass;
          } else {
            enclosingType = null;
          }

          if (enclosingType != null) {
            var receiverType = GetThisType(clbl.Tok, enclosingType);
            if (receiverType.IsOrdered && !receiverType.IsRefType) {
              var th = new ThisExpr(clbl.Tok) { Type = receiverType }; // resolve here
              decr.Add(AutoGeneratedExpression.Create(th));
              anyChangeToDecreases = true;
            }
          }
        }

        foreach (var p in clbl.Ins) {
          if (!(p is ImplicitFormal) && p.Type.IsOrdered) {
            var ie = new IdentifierExpr(new AutoGeneratedToken(p.tok), p.Name);
            ie.Var = p;
            ie.Type = p.Type; // resolve it here
            decr.Add(AutoGeneratedExpression.Create(ie));
            anyChangeToDecreases = true;
          }
        }

        clbl.InferredDecreases = true; // this indicates that finding a default decreases clause was attempted
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
            Contract.Assume(false); // unexpected case
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
          new SetComprehension(e.tok, e.tok, true, bvars,
            new BinaryExpr(e.tok, BinaryExpr.Opcode.In, obj,
              new ApplyExpr(e.tok, e, bexprs, e.tok) {
                Type = new SetType(true, builtIns.ObjectQ())
              }) {
              ResolvedOp =
                arrTy.Result.AsMultiSetType != null ? BinaryExpr.ResolvedOpcode.InMultiSet :
                arrTy.Result.AsSeqType != null ? BinaryExpr.ResolvedOpcode.InSeq :
                BinaryExpr.ResolvedOpcode.InSet,
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
          Expression e = FrameArrowToObjectSet(fe.E, idGen); // keep only fe.E, drop any fe.Field designation
          Contract.Assert(e.Type != null); // should have been resolved already
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
            bvIE.Var = bv; // resolve here
            bvIE.Type = bv.Type; // resolve here
            var sInE = new BinaryExpr(e.tok, BinaryExpr.Opcode.In, bvIE, e);
            if (eType is SeqType) {
              sInE.ResolvedOp = BinaryExpr.ResolvedOpcode.InSeq; // resolve here
            } else {
              sInE.ResolvedOp = BinaryExpr.ResolvedOpcode.InMultiSet; // resolve here
            }

            sInE.Type = Type.Bool; // resolve here
            var s = new SetComprehension(e.tok, e.tok, true, new List<BoundVar>() { bv }, sInE, bvIE, null);
            s.Type = new SetType(true, builtIns.ObjectQ()); // resolve here
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
        display.Type = new SetType(true, builtIns.ObjectQ()); // resolve here
        sets.Add(display);
      }

      if (sets.Count == 0) {
        Expression emptyset = new SetDisplayExpr(Token.NoToken, true, new List<Expression>());
        emptyset.Type = new SetType(true, builtIns.ObjectQ()); // resolve here
        return emptyset;
      } else {
        Expression s = sets[0];
        for (int i = 1; i < sets.Count; i++) {
          BinaryExpr union = new BinaryExpr(s.tok, BinaryExpr.Opcode.Add, s, sets[i]);
          union.ResolvedOp = BinaryExpr.ResolvedOpcode.Union; // resolve here
          union.Type = new SetType(true, builtIns.ObjectQ()); // resolve here
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
      int prevErrorCount = reporter.Count(ErrorLevel.Error);
      ResolveTopLevelDecls_Signatures(m, sig, m.TopLevelDecls, datatypeDependencies, codatatypeDependencies);
      Contract.Assert(AllTypeConstraints.Count == 0); // signature resolution does not add any type constraints
      ResolveAttributes(m, new ResolutionContext(new NoContext(m.EnclosingModule), false)); // Must follow ResolveTopLevelDecls_Signatures, in case attributes refer to members
      SolveAllTypeConstraints(); // solve any type constraints entailed by the attributes
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        ResolveTopLevelDecls_Core(m.TopLevelDecls, datatypeDependencies, codatatypeDependencies, isAnExport);
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
            reporter.Warning(MessageSource.Resolver, d.tok,
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
        var exportView = cloner.CloneModuleDefinition(m, m.Name);
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
        var modDef = new ModuleDefinition(tok, name, new List<IToken>(), false, false, null, moduleDecl, null, false,
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
      IToken root = qid.Path[0];
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
      IToken root = qid.Path[0];
      result = null;
      bool res = bindings.TryLookupFilter(root, out result,
        m => context != m && ((context.EnclosingModuleDefinition == m.EnclosingModuleDefinition && context.Exports.Count == 0) || m is LiteralModuleDecl));
      qid.Root = result;
      return res;
    }

    private bool ResolveQualifiedModuleIdRootAbstract(AbstractModuleDecl context, ModuleBindings bindings, ModuleQualifiedId qid,
      out ModuleDecl result) {
      Contract.Assert(qid != null);
      IToken root = qid.Path[0];
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

    private static string ModuleNotFoundErrorMessage(int i, List<IToken> path, string tail = "") {
      Contract.Requires(path != null);
      Contract.Requires(0 <= i && i < path.Count);
      return "module " + path[i].val + " does not exist" +
             (1 < path.Count
               ? " (position " + i.ToString() + " in path " + Util.Comma(".", path, x => x.val) + ")" + tail
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
              var field = new SpecialField(p.tok, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, false,
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
              var field = new SpecialField(p.tok, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, true,
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
            var field = new SpecialField(p.tok, nm, SpecialField.ID.UseIdParam, nm, true, true, false, tp, null);
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
          iter.Member_Reads = new SpecialField(iter.tok, "_reads", SpecialField.ID.Reads, null, true, false, false,
            new SetType(true, builtIns.ObjectQ()), null);
          iter.Member_Modifies = new SpecialField(iter.tok, "_modifies", SpecialField.ID.Modifies, null, true, false,
            false, new SetType(true, builtIns.ObjectQ()), null);
          iter.Member_New = new SpecialField(iter.tok, "_new", SpecialField.ID.New, null, true, true, true,
            new SetType(true, builtIns.ObjectQ()), null);
          foreach (var field in new List<Field>() { iter.Member_Reads, iter.Member_Modifies, iter.Member_New }) {
            field.EnclosingClass = iter; // resolve here
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
            var field = new SpecialField(p.tok, nm, SpecialField.ID.UseIdParam, nm, true, false, false,
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
          var init = new Constructor(iter.tok, "_ctor", false, new List<TypeParameter>(), iter.Ins,
            new List<AttributedExpression>(),
            new Specification<FrameExpression>(new List<FrameExpression>(), null),
            new List<AttributedExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, null, null);
          // --- here comes predicate Valid()
          var valid = new Predicate(iter.tok, "Valid", false, true, new List<TypeParameter>(),
            new List<Formal>(),
            null,
            new List<AttributedExpression>(),
            new List<FrameExpression>(),
            new List<AttributedExpression>(),
            new Specification<Expression>(new List<Expression>(), null),
            null, Predicate.BodyOriginKind.OriginalOrInherited, null, null, null, null);
          // --- here comes method MoveNext
          var moveNext = new Method(iter.tok, "MoveNext", false, false, new List<TypeParameter>(),
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
          var ctors = new Dictionary<string, DatatypeCtor>();
          datatypeCtors.Add(dt, ctors);
          // ... and of the other members
          var members = new Dictionary<string, MemberDecl>();
          classMembers.Add(dt, members);

          foreach (DatatypeCtor ctor in dt.Ctors) {
            if (ctor.Name.EndsWith("?")) {
              reporter.Error(MessageSource.Resolver, ctor,
                "a datatype constructor name is not allowed to end with '?'");
            } else if (ctors.ContainsKey(ctor.Name)) {
              reporter.Error(MessageSource.Resolver, ctor, "Duplicate datatype constructor name: {0}", ctor.Name);
            } else {
              ctors.Add(ctor.Name, ctor);
              ctor.InheritVisibility(dt);

              // create and add the query "method" (field, really)
              string queryName = ctor.Name + "?";
              var query = new DatatypeDiscriminator(ctor.tok, queryName, SpecialField.ID.UseIdParam, "is_" + ctor.CompileName,
                ctor.IsGhost, Type.Bool, null);
              query.InheritVisibility(dt);
              query.EnclosingClass = dt; // resolve here
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
                dtor = new DatatypeDestructor(formal.tok, ctor, formal, formal.Name, "dtor_" + formal.CompileName,
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
            var extraName = m.Name + "#";
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
            if (m is ExtremePredicate) {
              var extremePredicate = (ExtremePredicate)m;
              formals.AddRange(extremePredicate.Formals.ConvertAll(cloner.CloneFormal));

              List<TypeParameter> tyvars = extremePredicate.TypeArgs.ConvertAll(cloner.CloneTypeParam);

              // create prefix predicate
              extremePredicate.PrefixPredicate = new PrefixPredicate(extremePredicate.tok, extraName, extremePredicate.HasStaticKeyword,
                tyvars, k, formals,
                extremePredicate.Req.ConvertAll(cloner.CloneAttributedExpr),
                extremePredicate.Reads.ConvertAll(cloner.CloneFrameExpr),
                extremePredicate.Ens.ConvertAll(cloner.CloneAttributedExpr),
                new Specification<Expression>(new List<Expression>() { new IdentifierExpr(extremePredicate.tok, k.Name) }, null),
                cloner.CloneExpr(extremePredicate.Body),
                null,
                extremePredicate);
              extraMember = extremePredicate.PrefixPredicate;
              // In the call graph, add an edge from P# to P, since this will have the desired effect of detecting unwanted cycles.
              moduleDef.CallGraph.AddEdge(extremePredicate.PrefixPredicate, extremePredicate);
            } else {
              var extremeLemma = (ExtremeLemma)m;
              // _k has already been added to 'formals', so append the original formals
              formals.AddRange(extremeLemma.Ins.ConvertAll(cloner.CloneFormal));
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
              extremeLemma.PrefixLemma = new PrefixLemma(extremeLemma.tok, extraName, extremeLemma.HasStaticKeyword,
                extremeLemma.TypeArgs.ConvertAll(cloner.CloneTypeParam), k, formals, extremeLemma.Outs.ConvertAll(cloner.CloneFormal),
                req, cloner.CloneSpecFrameExpr(extremeLemma.Mod), ens,
                new Specification<Expression>(decr, null),
                null, // Note, the body for the prefix method will be created once the call graph has been computed and the SCC for the greatest lemma is known
                cloner.CloneAttributes(extremeLemma.Attributes), extremeLemma);
              extraMember = extremeLemma.PrefixLemma;
              // In the call graph, add an edge from M# to M, since this will have the desired effect of detecting unwanted cycles.
              moduleDef.CallGraph.AddEdge(extremeLemma.PrefixLemma, extremeLemma);
            }

            extraMember.InheritVisibility(m, false);
            members.Add(extraName, extraMember);
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
      var method = new Method(f.tok, f.Name, f.HasStaticKeyword, false, f.TypeArgs,
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

      var mod = new ModuleDefinition(Token.NoToken, Name + ".Abs", new List<IToken>(), true, true, null, null, null,
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
        var a = new AbstractModuleDecl(abs.QId, abs.tok, m, abs.Opened, abs.Exports);
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

      List<IToken> Path = qid.Path;
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

        var tld = p.TopLevels.GetValueOrDefault(Path[k].val, null);
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
      foreach (TopLevelDecl d in ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(declarations)) {
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
          ResolveAttributes(d, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false));
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
            ResolveExpression(dd.Constraint, new ResolutionContext(new CodeContextWrapper(dd, true), false));
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
          ResolveAttributes(d, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false));
          // type check the constraint
          Contract.Assert(object.ReferenceEquals(dd.Var.Type, dd.Rhs));  // follows from SubsetTypeDecl invariant
          Contract.Assert(dd.Constraint != null);  // follows from SubsetTypeDecl invariant
          scope.PushMarker();
          scope.AllowInstance = false;
          var added = scope.Push(dd.Var.Name, dd.Var);
          Contract.Assert(added == Scope<IVariable>.PushResult.Success);
          ResolveExpression(dd.Constraint, new ResolutionContext(new CodeContextWrapper(dd, true), false));
          Contract.Assert(dd.Constraint.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(dd.Constraint, "subset-type constraint must be of type bool (instead got {0})");
          SolveAllTypeConstraints();
          if (!CheckTypeInference_Visitor.IsDetermined(dd.Rhs.NormalizeExpand())) {
            reporter.Error(MessageSource.Resolver, dd.tok, "subset type's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
          }
          dd.ConstraintIsCompilable = ExpressionTester.CheckIsCompilable(null, dd.Constraint, new CodeContextWrapper(dd, true));
          dd.CheckedIfConstraintIsCompilable = true;

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
              var resolutionContext = new ResolutionContext(field, false);
              ResolveAttributes(field, resolutionContext);
              // Resolve the value expression
              if (field.Rhs != null) {
                var ec = reporter.Count(ErrorLevel.Error);
                scope.PushMarker();
                if (currentClass == null || !currentClass.AcceptThis) {
                  scope.AllowInstance = false;
                }
                ResolveExpression(field.Rhs, resolutionContext);
                scope.PopMarker();
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
                  ExpressionTester.CheckIsCompilable(this, field.Rhs, field);
                }
              }
            }
          }
        }
      }
      // Now, we're ready for the other declarations, along with any witness clauses of newtype/subset-type declarations.
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(AllTypeConstraints.Count == 0);
        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, false, d);
        if (d is NewtypeDecl || d is SubsetTypeDecl) {
          // NewTypeDecl's and SubsetTypeDecl's were already processed in the loop above, except for any witness clauses
          var dd = (RedirectingTypeDecl)d;
          if (dd.Witness != null) {
            var prevErrCnt = reporter.Count(ErrorLevel.Error);
            var codeContext = new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
            scope.PushMarker();
            if (d is not TopLevelDeclWithMembers topLevelDecl || !topLevelDecl.AcceptThis) {
              scope.AllowInstance = false;
            }
            ResolveExpression(dd.Witness, new ResolutionContext(codeContext, false));
            scope.PopMarker();
            ConstrainSubtypeRelation(dd.Var.Type, dd.Witness.Type, dd.Witness, "witness expression must have type '{0}' (got '{1}')", dd.Var.Type, dd.Witness.Type);
            SolveAllTypeConstraints();
            if (reporter.Count(ErrorLevel.Error) == prevErrCnt) {
              CheckTypeInference(dd.Witness, dd);
            }
            if (reporter.Count(ErrorLevel.Error) == prevErrCnt && dd.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
              ExpressionTester.CheckIsCompilable(this, dd.Witness, codeContext);
            }
          }
          if (d is TopLevelDeclWithMembers dm) {
            ResolveClassMemberBodies(dm);
          }
        } else {
          if (!(d is IteratorDecl)) {
            // Note, attributes of iterators are resolved by ResolvedIterator, after registering any names in the iterator signature
            ResolveAttributes(d, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false));
          }
          if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            ResolveIterator(iter);
            ResolveClassMemberBodies(iter);  // resolve the automatically generated members
          } else if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              ResolveAttributes(ctor, new ResolutionContext(new NoContext(d.EnclosingModuleDefinition), false));
              foreach (var formal in ctor.Formals) {
                AddTypeDependencyEdges((ICallable)d, formal.Type);
              }
            }
            // resolve any default parameters
            foreach (var ctor in dt.Ctors) {
              scope.PushMarker();
              scope.AllowInstance = false;
              ctor.Formals.ForEach(p => scope.Push(p.Name, p));
              ResolveParameterDefaultValues(ctor.Formals, ResolutionContext.FromCodeContext(dt));
              scope.PopMarker();
            }
            // resolve members
            ResolveClassMemberBodies(dt);
          } else if (d is TopLevelDeclWithMembers) {
            var dd = (TopLevelDeclWithMembers)d;
            ResolveClassMemberBodies(dd);
          }
        }
        allTypeParameters.PopMarker();
      }

      // ---------------------------------- Pass 1 ----------------------------------
      // This pass:
      // * checks that type inference was able to determine all types
      // * check that shared destructors in datatypes are in agreement
      // * fills in the .ResolvedOp field of binary expressions
      // * performs substitution for DefaultValueExpression's
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
            foreach (var formal in iter.Ins) {
              if (formal.DefaultValue != null) {
                CheckTypeInference(formal.DefaultValue, iter);
              }
            }
            iter.Members.Iter(CheckTypeInference_Member);
            if (prevErrCnt == reporter.Count(ErrorLevel.Error)) {
              iter.SubExpressions.Iter(e => CheckExpression(e, this, iter));
            }
            ResolveParameterDefaultValues_Pass1(iter.Ins, iter);
            if (iter.Body != null) {
              CheckTypeInference(iter.Body, iter);
              if (prevErrCnt == reporter.Count(ErrorLevel.Error)) {
                ComputeGhostInterest(iter.Body, false, null, iter);
                CheckExpression(iter.Body, this, iter);
              }
            }
          } else if (d is ClassDecl) {
            var dd = (ClassDecl)d;
            ResolveClassMembers_Pass1(dd);
          } else if (d is SubsetTypeDecl) {
            var dd = (SubsetTypeDecl)d;
            Contract.Assert(dd.Constraint != null);
            CheckExpression(dd.Constraint, this, new CodeContextWrapper(dd, true));
            if (dd.Witness != null) {
              CheckExpression(dd.Witness, this, new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost));
            }
          } else if (d is NewtypeDecl) {
            var dd = (NewtypeDecl)d;
            if (dd.Var != null) {
              Contract.Assert(dd.Constraint != null);
              CheckExpression(dd.Constraint, this, new CodeContextWrapper(dd, true));
              if (dd.Witness != null) {
                CheckExpression(dd.Witness, this, new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost));
              }
            }
            FigureOutNativeType(dd);
            ResolveClassMembers_Pass1(dd);
          } else if (d is DatatypeDecl) {
            var dd = (DatatypeDecl)d;
            foreach (var ctor in dd.Ctors) {
              foreach (var formal in ctor.Formals) {
                if (formal.DefaultValue != null) {
                  CheckTypeInference(formal.DefaultValue, dd);
                }
              }
            }
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
            foreach (var ctor in dd.Ctors) {
              ResolveParameterDefaultValues_Pass1(ctor.Formals, dd);
            }
            ResolveClassMembers_Pass1(dd);
          } else if (d is OpaqueTypeDecl) {
            var dd = (OpaqueTypeDecl)d;
            ResolveClassMembers_Pass1(dd);
          }
        }
      }

      FillInDefaultValueExpressions();

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
                  // For every focal predicate P in S, add to S all co-predicates in the same strongly connected
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
              var recursiveCall = new CallStmt(com.tok, com.tok, new List<Expression>(), methodSel, recursiveCallArgs.ConvertAll(e => new ActualBinding(null, e)));
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
              var forallStmt = new ForallStmt(com.tok, com.tok, bvs, attrs, range, new List<AttributedExpression>(), forallBody);
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
          currentClass = (TopLevelDeclWithMembers)prefixLemma.EnclosingClass;
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

          if (d is RedirectingTypeDecl) {
            var dd = (RedirectingTypeDecl)d;
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
      new SubsetConstraintGhostChecker(this).Traverse(declarations);
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
        CheckTypeInference_Member(member);
        if (prevErrCnt == reporter.Count(ErrorLevel.Error)) {
          if (member is Method) {
            var m = (Method)member;
            ResolveParameterDefaultValues_Pass1(m.Ins, m);
            if (m.Body != null) {
              ComputeGhostInterest(m.Body, m.IsGhost, m.IsLemmaLike ? "a " + m.WhatKind : null, m);
              CheckExpression(m.Body, this, m);
              new TailRecursion(reporter).DetermineTailRecursion(m);
            }
          } else if (member is Function) {
            var f = (Function)member;
            ResolveParameterDefaultValues_Pass1(f.Formals, f);
            if (f.ByMethodBody == null) {
              if (!f.IsGhost && f.Body != null) {
                ExpressionTester.CheckIsCompilable(this, f.Body, f);
              }
              if (f.Body != null) {
                new TailRecursion(reporter).DetermineTailRecursion(f);
              }
            } else {
              var m = f.ByMethodDecl;
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
          }
          if (prevErrCnt == reporter.Count(ErrorLevel.Error) && member is ICodeContext) {
            member.SubExpressions.Iter(e => CheckExpression(e, this, (ICodeContext)member));
          }
        }
      }
    }

    /// <summary>
    /// Check that default-value expressions are compilable, for non-ghost formals.
    /// </summary>
    void ResolveParameterDefaultValues_Pass1(List<Formal> formals, ICodeContext codeContext) {
      Contract.Requires(formals != null);

      foreach (var formal in formals.Where(f => f.DefaultValue != null)) {
        if ((!codeContext.IsGhost || codeContext is DatatypeDecl) && !formal.IsGhost) {
          ExpressionTester.CheckIsCompilable(this, formal.DefaultValue, codeContext);
        }
        CheckExpression(formal.DefaultValue, this, codeContext);
      }
    }


    /// <summary>
    /// Add edges to the callgraph.
    /// </summary>
    private void AddTypeDependencyEdges(ICodeContext context, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(context != null);
      var caller = CodeContextWrapper.Unwrap(context) as ICallable;
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

    private BigInteger MaxBV(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(t.IsBitVectorType);
      return MaxBV(t.AsBitVectorType.Width);
    }

    private BigInteger MaxBV(int bits) {
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
        if (DafnyOptions.O.Compiler.SupportedNativeTypes.Contains(nativeT.Name)) {
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

      DetermineRootLeaf(lhs, out var isRoot, out _, out _, out _);
      if (isRoot) {
        ConstrainSubtypeRelation(lhs, rhs, errMsg, true, allowDecisions);
        moreXConstraints = false;
      } else {
        var lhsWithProxyArgs = Type.HeadWithProxyArgs(lhs);
        ConstrainSubtypeRelation(lhsWithProxyArgs, rhs, errMsg, false, allowDecisions);
        ConstrainAssignableTypeArgs(lhs, lhsWithProxyArgs.TypeArgs, lhs.TypeArgs, errMsg, out moreXConstraints);
        if (lhs.AsCollectionType == null) {
          var sameHead = Type.SameHead(lhs, rhs);
          if (!sameHead && lhs is UserDefinedType udtLhs && rhs is UserDefinedType udtRhs) {
            // also allow the case where lhs is a possibly-null type and rhs is a non-null type
            sameHead = udtLhs.ResolvedClass == (udtRhs.ResolvedClass as NonNullTypeDecl)?.Class;
          }
          if (sameHead) {
            bool more2;
            ConstrainAssignableTypeArgs(lhs, lhs.TypeArgs, rhs.TypeArgs, errMsg, out more2);
            moreXConstraints = moreXConstraints || more2;
          }
        }
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
        var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter at index 0 expects {1} <: {0}", A[0], B[0]);
        AddAssignableConstraint(tok, A[0], B[0], em);
        em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter at index 1 expects {1} <: {0}", A[1], B[1]);
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
          var msgFormat = "variance for type parameter" + (B.Count == 1 ? "" : " at index " + i) + " expects {0} {1} {2}";
          if (cl.TypeArgs[i].Variance == TypeParameter.TPVariance.Co) {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "co" + msgFormat, A[i], ":>", B[i]);
            AddAssignableConstraint(tok, A[i], B[i], em);
            moreXConstraints = true;
          } else if (cl.TypeArgs[i].Variance == TypeParameter.TPVariance.Contra) {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "contra" + msgFormat, A[i], "<:", B[i]);
            AddAssignableConstraint(tok, B[i], A[i], em);
            moreXConstraints = true;
          } else {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "non" + msgFormat, A[i], "=", B[i]);
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
          c.FlagAsError(this);
          return false;
        }
        // TODO: inspect type parameters in order to produce some error messages sooner
        return true;
      }
    }

    /// <summary>
    /// "root" says that the type is a non-artificial type (that is, not an ArtificialType) with no proper supertypes.
    /// "leaf" says that the only possible proper subtypes are subset types of the type. Thus, the only
    /// types that are not leaf types are traits and artificial types.
    /// The "headIs" versions speak only about the head symbols, so it is possible that the given
    /// type arguments would change the root/leaf status of the entire type.
    /// </summary>
    void DetermineRootLeaf(Type t, out bool isRoot, out bool isLeaf, out bool headIsRoot, out bool headIsLeaf) {
      Contract.Requires(t != null);
      Contract.Ensures(!Contract.ValueAtReturn(out isRoot) || Contract.ValueAtReturn(out headIsRoot)); // isRoot ==> headIsRoot
      Contract.Ensures(!Contract.ValueAtReturn(out isLeaf) || Contract.ValueAtReturn(out headIsLeaf)); // isLeaf ==> headIsLeaf
      t = t.NormalizeExpandKeepConstraints();
      if (t.IsObjectQ) {
        isRoot = true; isLeaf = false;
        headIsRoot = true; headIsLeaf = false;
      } else if (t is ArrowType) {
        var arr = (ArrowType)t;
        headIsRoot = true; headIsLeaf = true;  // these are definitely true
        isRoot = true; isLeaf = true;  // set these to true until proven otherwise
        Contract.Assert(arr.Arity + 1 == arr.TypeArgs.Count);
        for (int i = 0; i < arr.TypeArgs.Count; i++) {
          var arg = arr.TypeArgs[i];
          DetermineRootLeaf(arg, out var r, out var l, out _, out _);
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
          if (cl is TypeParameter) {
            var tp = udt.AsTypeParameter;
            Contract.Assert(tp != null);
            headIsRoot = true; headIsLeaf = true;  // all type parameters are non-variant
          } else if (cl is SubsetTypeDecl) {
            headIsRoot = false; headIsLeaf = true;
          } else if (cl is NewtypeDecl) {
            headIsRoot = true; headIsLeaf = true;
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
              DetermineRootLeaf(udt.TypeArgs[i], out var r, out var l, out _, out _);
              // isRoot and isLeaf aren't duals, so Co and Contra require separate consideration beyond inversion.
              switch (variance) {
                case TypeParameter.TPVariance.Co: { isRoot &= r; isLeaf &= l; break; }
                // A invariably constructible subtype becomes a supertype, and thus the enclosing type is never a root.
                case TypeParameter.TPVariance.Contra: { isRoot &= false; isLeaf &= r; break; }
              }
            }
          }
        } else {
          isRoot = false; isLeaf = false;  // don't know
          headIsRoot = false; headIsLeaf = false;
        }
      } else if (t.IsBoolType || t.IsCharType || t.IsIntegerType || t.IsRealType || t.AsNewtype != null || t.IsBitVectorType || t.IsBigOrdinalType) {
        isRoot = true; isLeaf = true;
        headIsRoot = true; headIsLeaf = true;
      } else if (t is ArtificialType) {
        isRoot = false; isLeaf = false;
        headIsRoot = false; headIsLeaf = false;
      } else if (t is MapType) {  // map, imap
        Contract.Assert(t.TypeArgs.Count == 2);
        DetermineRootLeaf(t.TypeArgs[0], out var r0, out _, out _, out _);
        DetermineRootLeaf(t.TypeArgs[1], out var r1, out _, out _, out _);
        isRoot = r0 & r1; isLeaf = r0 & r1;  // map types are covariant in both type arguments
        headIsRoot = true; headIsLeaf = true;
      } else if (t is CollectionType) {  // set, iset, multiset, seq
        Contract.Assert(t.TypeArgs.Count == 1);
        DetermineRootLeaf(t.TypeArgs[0], out isRoot, out isLeaf, out _, out _);  // type is covariant is type argument
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
      if (_recursionDepth == 20000) {
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

      t = keepConstraints ? t.Normalize() : t.NormalizeExpand();
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
        Console.WriteLine("DEBUG: setting proxy {0}.T := {1}", proxy, t);
      }
      proxy.T = t;

      // check feasibility
      DetermineRootLeaf(t, out var isRoot, out var isLeaf, out _, out _);
      // propagate up
      foreach (var c in proxy.SupertypeConstraints) {
        var u = keepConstraints ? c.Super.NormalizeExpandKeepConstraints() : c.Super.NormalizeExpand();
        if (!(u is TypeProxy)) {
          ImposeSubtypingConstraint(u, t, c.ErrMsg);
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
          ImposeSubtypingConstraint(t, u, c.ErrMsg);
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
      super = super.NormalizeExpandKeepConstraints();
      sub = sub.NormalizeExpandKeepConstraints();
      List<int> polarities = ConstrainTypeHead_Recursive(super, ref sub);
      if (polarities == null) {
        errorMsg.FlagAsError(this);
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
          "non-variant type parameter{0} would require {1} = {2}",
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
    /// upward toward its parents until it finds a head that matches "super", if any.
    /// </summary>
    private static List<int> ConstrainTypeHead_Recursive(Type super, ref Type sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);

      super = super.NormalizeExpandKeepConstraints();
      sub = sub.NormalizeExpandKeepConstraints();

      var polarities = ConstrainTypeHead(super, sub);
      if (polarities != null) {
        return polarities;
      }

      foreach (var subParentType in sub.ParentTypes()) {
        sub = subParentType;
        polarities = ConstrainTypeHead_Recursive(super, ref sub);
        if (polarities != null) {
          return polarities;
        }
      }

      return null;
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
    private static List<int> ConstrainTypeHead(Type super, Type sub) {
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
          return null;
        default:
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
            var polarity = TypeParameter.Direction(tp.Variance);
            polarities.Add(polarity);
          }

          return polarities;
        } else if (udfSub.IsRefType && super.IsObjectQ) {
          return new List<int>();
        } else if (udfSub.IsNonNullRefType && super.IsObject) {
          return new List<int>();
        } else {
          return null;
        }
      }
    }
    private static bool KeepConstraints(Type super, Type sub) {
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

    public class XConstraint {
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
              var u = Types[1].NormalizeExpand();
              if (CheckTypeInference_Visitor.IsDetermined(t) &&
                  (fullstrength
                   || !ProxyWithNoSubTypeConstraint(u, resolver)
                   || (u is TypeProxy
                       && Types[0].NormalizeExpandKeepConstraints() is var t0constrained
                       && (t0constrained.IsNonNullRefType || t0constrained.AsSubsetType != null)
                       && resolver.HasApplicableNullableRefTypeConstraint(new HashSet<TypeProxy>() { (TypeProxy)u })))) {
                // This is the best case.  We convert Assignable(t, u) to the subtype constraint base(t) :> u.
                if (CheckTypeInference_Visitor.IsDetermined(u) && t.IsSubtypeOf(u, false, true) && t.IsRefType) {
                  // But we also allow cases where the rhs is a proper supertype of the lhs, and let the verifier
                  // determine whether the rhs is provably an instance of the lhs.
                  resolver.ConstrainAssignable((NonProxyType)u, (NonProxyType)t, errorMsg, out moreXConstraints, fullstrength);
                } else {
                  resolver.ConstrainAssignable((NonProxyType)t, u, errorMsg, out moreXConstraints, fullstrength);
                }
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
            satisfied = t.IsNumericBased(Type.NumericPersuasion.Int);
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
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SeqType || t is SetType || t is MultiSetType || t is MapType;
            break;
          case "Minusable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SetType || t is MultiSetType || t is MapType;
            break;
          case "Mullable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t is SetType || t is MultiSetType;
            break;
          case "IntOrORDINAL":
            if (!(t is TypeProxy)) {
              if (TernaryExpr.PrefixEqUsesNat) {
                satisfied = t.IsNumericBased(Type.NumericPersuasion.Int);
              } else {
                satisfied = t.IsNumericBased(Type.NumericPersuasion.Int) || t.IsBigOrdinalType;
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
            satisfied = t.IsNumericBased(Type.NumericPersuasion.Int) || t.IsBitVectorType;
            break;
          case "BooleanBits":
            satisfied = t.IsBoolType || t.IsBitVectorType;
            break;
          case "Sizeable":
            satisfied = (t is SetType && ((SetType)t).Finite) || t is MultiSetType || t is SeqType || (t is MapType && ((MapType)t).Finite);
            break;
          case "Disjointable":
            satisfied = t is SetType || t is MultiSetType;
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
              Type join = null;
              if (resolver.JoinOfAllSubtypes(proxy, ref join, new HashSet<TypeProxy>()) && join != null) {
                var headWithProxyArgs = Type.HeadWithProxyArgs(join);
                var tt = headWithProxyArgs.NormalizeExpand();
                satisfied = tt is SeqType || tt is MultiSetType || tt is MapType || (tt.IsArrayType && tt.AsArrayType.Dims == 1);
                if (satisfied) {
                  resolver.AssignProxyAndHandleItsConstraints(proxy, headWithProxyArgs, true);
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
              Type join = null;
              if (resolver.JoinOfAllSubtypes(proxy, ref join, new HashSet<TypeProxy>()) && join != null) {
                var headWithProxyArgs = Type.HeadWithProxyArgs(join);
                var tt = headWithProxyArgs.NormalizeExpand();
                satisfied = tt is SeqType || (tt.IsArrayType && tt.AsArrayType.Dims == 1);
                if (satisfied) {
                  resolver.AssignProxyAndHandleItsConstraints(proxy, headWithProxyArgs, true);
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
                resolver.ConstrainToIntegerType(index, true, "sequence update requires integer- or bitvector-based index (got {0})");
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
                resolver.ConstrainToIntegerType(value, false, "multiset update requires integer-based numeric value (got {0})");
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
            if (t is SeqType || t.IsArrayType) {
              resolver.ConstrainToIntegerType(errorMsg.Tok, Types[1], true, errorMsg);
              convertedIntoOtherTypeConstraints = true;
              return true;
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
              Type a, b;
              satisfied = Type.FromSameHead_Subtype(t, u, out a, out b);
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
              if (moreExactThis.TreatTypeParamAsWild && (t.IsTypeParameter || u.IsTypeParameter || t.IsOpaqueType || u.IsOpaqueType)) {
                return true;
              } else if (!moreExactThis.AllowSuperSub) {
                resolver.ConstrainSubtypeRelation_Equal(t, u, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              Type a, b;
              // okay if t<:u or u<:t (this makes type inference more manageable, though it is more liberal than one might wish)
              satisfied = Type.FromSameHead_Subtype(t, u, out a, out b);
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
              if (collType is SetType || collType is SeqType) {
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
              if (t.IsRefType && (arrTy == null || collType != null)) {
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
          errorMsg.FlagAsError(resolver);
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

    public class XConstraintWithExprs : XConstraint {
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

    public class XConstraint_EquatableArg : XConstraint {
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

          case 11: {
              // Last resort decisions. Sometimes get here even with some 'obvious'
              // inferences. Before this case was added, the type inference returned with
              // failure, so this is a conservative addition, and could be made more
              // capable.
              if (!allowDecisions) {
                break;
              }

              foreach (var c in AllXConstraints) {
                if (c.ConstraintName == "EquatableArg") {
                  ConstrainSubtypeRelation_Equal(c.Types[0], c.Types[1], c.errorMsg);
                  anyNewConstraints = true;
                  AllXConstraints.Remove(c);
                  break;
                }
              }
              if (anyNewConstraints) {
                break;
              }

              TypeConstraint.ErrorMsg oneSuperErrorMsg = null;
              TypeConstraint.ErrorMsg oneSubErrorMsg = null;
              var ss = new HashSet<Type>();
              foreach (var c in AllTypeConstraints) {
                var super = c.Super.NormalizeExpand();
                var sub = c.Sub.NormalizeExpand();
                if (super is TypeProxy && !ss.Contains(super)) {
                  ss.Add(super);
                }
                if (sub is TypeProxy && !ss.Contains(sub)) {
                  ss.Add(sub);
                }
              }

              foreach (var t in ss) {
                var lowers = new HashSet<Type>();
                var uppers = new HashSet<Type>();
                foreach (var c in AllTypeConstraints) {
                  var super = c.Super.NormalizeExpand();
                  var sub = c.Sub.NormalizeExpand();
                  if (t.Equals(super)) {
                    lowers.Add(sub);
                    oneSubErrorMsg = c.ErrMsg;
                  }
                  if (t.Equals(sub)) {
                    uppers.Add(super);
                    oneSuperErrorMsg = c.ErrMsg;
                  }
                }

                bool done = false;
                foreach (var tl in lowers) {
                  foreach (var tu in uppers) {
                    if (tl.Equals(tu)) {
                      if (!ContainsAsTypeParameter(tu, t)) {
                        var errorMsg = new TypeConstraint.ErrorMsgWithBase(AllTypeConstraints[0].ErrMsg,
                          "Decision: {0} is decided to be {1} because the latter is both the upper and lower bound to the proxy",
                          t, tu);
                        ConstrainSubtypeRelation_Equal(t, tu, errorMsg);
                        // The above changes t so that it is a proxy with an assigned type
                        anyNewConstraints = true;
                        done = true;
                        break;
                      }
                    }
                  }
                  if (done) {
                    break;
                  }
                }
              }
              if (anyNewConstraints) {
                break;
              }

              foreach (var t in ss) {
                var lowers = new HashSet<Type>();
                var uppers = new HashSet<Type>();
                foreach (var c in AllTypeConstraints) {
                  var super = c.Super.NormalizeExpand();
                  var sub = c.Sub.NormalizeExpand();
                  if (t.Equals(super)) {
                    lowers.Add(sub);
                  }

                  if (t.Equals(sub)) {
                    uppers.Add(super);
                  }
                }

                if (uppers.Count == 0) {
                  if (lowers.Count == 1) {
                    var em = lowers.GetEnumerator();
                    em.MoveNext();
                    if (!ContainsAsTypeParameter(em.Current, t)) {
                      var errorMsg = new TypeConstraint.ErrorMsgWithBase(oneSubErrorMsg,
                        "Decision: {0} is decided to be {1} because the latter is a lower bound to the proxy and there is no constraint with an upper bound",
                        t, em.Current);
                      ConstrainSubtypeRelation_Equal(t, em.Current, errorMsg);
                      anyNewConstraints = true;
                      break;
                    }
                  }
                }
                if (lowers.Count == 0) {
                  if (uppers.Count == 1) {
                    var em = uppers.GetEnumerator();
                    em.MoveNext();
                    if (!ContainsAsTypeParameter(em.Current, t)) {
                      var errorMsg = new TypeConstraint.ErrorMsgWithBase(oneSuperErrorMsg,
                        "Decision: {0} is decided to be {1} because the latter is an upper bound to the proxy and there is no constraint with a lower bound",
                        t, em.Current);
                      ConstrainSubtypeRelation_Equal(t, em.Current, errorMsg);
                      anyNewConstraints = true;
                      break;
                    }
                  }
                }
              }

              break;
            }

          case 12:
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

    private bool ContainsAsTypeParameter(Type t, Type u) {
      if (t.Equals(u)) {
        return true;
      }

      if (t is UserDefinedType udt) {
        foreach (var tp in udt.TypeArgs) {
          if (ContainsAsTypeParameter(tp, u)) {
            return true;
          }
        }
      }
      if (t is CollectionType st) {
        foreach (var tp in st.TypeArgs) {
          if (ContainsAsTypeParameter(tp, u)) {
            return true;
          }
        }
      }
      return false;
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
    /// Set "lhs" to the join of "rhss" and "lhs.Subtypes, if possible.
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
      Type join = null;
      foreach (var rhs in rhss) {
        if (rhs is TypeProxy) { return false; }
        join = join == null ? rhs : Type.Join(join, rhs, builtIns);
      }
      foreach (var sub in lhs.SubtypesKeepConstraints) {
        if (sub is TypeProxy) { return false; }
        join = join == null ? sub : Type.Join(join, sub, builtIns);
      }
      if (join == null) {
        return false;
      } else if (Reaches(join, lhs, 1, new HashSet<TypeProxy>())) {
        // would cause a cycle, so don't do it
        return false;
      } else {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: ProcessAssignable: assigning proxy {0}.T := {1}", lhs, join);
        }
        lhs.T = join;
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
        ImposeSubtypingConstraint(super, sub, c.ErrMsg);
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
        DetermineRootLeaf(su, out var isRoot, out _, out var headRoot, out _);
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
          DetermineRootLeaf(su, out _, out var isLeaf, out _, out var headLeaf);
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
      // If the join of the subtypes exists, use it
      var joins = new List<Type>();
      foreach (var su in proxy.Subtypes) {
        if (su is TypeProxy) {
          continue;  // don't include proxies in the meet computation
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
          // we went to the end without finding a place to meet up
          joins.Add(su);
        }
      }
      if (joins.Count == 1 && !Reaches(joins[0], proxy, 1, new HashSet<TypeProxy>())) {
        // we were able to compute a meet of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, joins[0]);
        return true;
      }
      // If the meet of the supertypes exists, use it
      var meets = new List<Type>();
      foreach (var su in proxy.Supertypes) {
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
          // we went to the end without finding a place to meet
          meets.Add(su);
        }
      }
      if (meets.Count == 1 && !(meets[0] is ArtificialType) && !Reaches(meets[0], proxy, -1, new HashSet<TypeProxy>())) {
        // we were able to compute a meet of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, meets[0]);
        return true;
      }

      return false;
    }

    bool AssignKnownEndsFullstrength_SubDirection(TypeProxy proxy) {
      Contract.Requires(proxy != null && proxy.T == null);
      // If the join the subtypes exists, use it
      var joins = new List<Type>();
      var proxySubs = new HashSet<TypeProxy>();
      proxySubs.Add(proxy);
      foreach (var su in proxy.SubtypesKeepConstraints_WithAssignable(AllXConstraints)) {
        if (su is TypeProxy) {
          proxySubs.Add((TypeProxy)su);
        } else {
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
      }
      if (joins.Count == 1 && !Reaches(joins[0], proxy, 1, new HashSet<TypeProxy>())) {
        // We were able to compute a join of all the subtyping constraints, so use it.
        // Well, maybe.  If "join[0]" denotes a non-null type and "proxy" is something
        // that could be assigned "null", then set "proxy" to the nullable version of "join[0]".
        // Stated differently, think of an applicable "IsNullableRefType" constraint as
        // being part of the join computation, essentially throwing in a "...?".
        // Except: If the join is a tight bound--meaning, it is also a meet--then pick it
        // after all, because that seems to give rise to less confusing error messages.
        if (joins[0].IsNonNullRefType) {
          Type meet = null;
          if (MeetOfAllSupertypes(proxy, ref meet, new HashSet<TypeProxy>(), false) && meet != null && Type.SameHead(joins[0], meet)) {
            // leave it
          } else {
            CloseOverAssignableRhss(proxySubs);
            if (HasApplicableNullableRefTypeConstraint(proxySubs)) {
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("DEBUG: Found join {0} for proxy {1}, but weakening it to {2}", joins[0], proxy, joins[0].NormalizeExpand());
              }
              AssignProxyAndHandleItsConstraints(proxy, joins[0].NormalizeExpand(), true);
              return true;
            }
          }
        }
        AssignProxyAndHandleItsConstraints(proxy, joins[0], true);
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
      // First, compute the the join of the Assignable LHSs.  Then, compute
      // the meet of that join and the supertypes.
      var joins = new List<Type>();
      foreach (var xc in AllXConstraints) {
        if (xc.ConstraintName == "Assignable" && xc.Types[1].Normalize() == proxy) {
          var su = xc.Types[0].Normalize();
          if (su is TypeProxy) {
            continue; // don't include proxies in the join computation
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
      }
      // If the meet of the supertypes exists, use it
      var meets = new List<Type>(joins);
      foreach (var su in proxy.SupertypesKeepConstraints) {
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
      if (meets.Count == 1 && !(meets[0] is ArtificialType) && !Reaches(meets[0], proxy, -1, new HashSet<TypeProxy>())) {
        // we were able to compute a meet of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, meets[0], true);
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
        var polarities = Type.GetPolarities(t).ConvertAll(TypeParameter.Direction);
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
          constraint.FlagAsError(this);
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
          xc.errorMsg.FlagAsError(this);
        }
      }
      TypeConstraint.ReportErrors(this, reporter);
      AllTypeConstraints.Clear();
      AllXConstraints.Clear();
    }

    // ------------------------------------------------------------------------------------------------------
    // ----- Visitors ---------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    #region Visitors
    class ResolverBottomUpVisitor : BottomUpVisitor {
      protected Resolver resolver;
      public ResolverBottomUpVisitor(Resolver resolver) {
        Contract.Requires(resolver != null);
        this.resolver = resolver;
      }
    }
    abstract class ResolverTopDownVisitor<T> : TopDownVisitor<T> {
      protected Resolver resolver;
      public ResolverTopDownVisitor(Resolver resolver) {
        Contract.Requires(resolver != null);
        this.resolver = resolver;
      }
    }
    #endregion Visitors

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
          return VisitOneExpr(e.ResolvedExpression, ref cp);
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
      var visitor = new GhostInterestVisitor(codeContext, this, false);
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
    readonly Scope<IVariable>/*!*/ scope = new Scope<IVariable>();
    Scope<Statement>/*!*/ enclosingStatementLabels = new Scope<Statement>();
    readonly Scope<Label>/*!*/ dominatingStatementLabels = new Scope<Label>();
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
            //adding a call graph edge from the trait method to that of class
            cl.EnclosingModuleDefinition.CallGraph.AddEdge(traitMethod, classMethod);

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
            //adding a call graph edge from the trait function to that of class
            cl.EnclosingModuleDefinition.CallGraph.AddEdge(traitFunction, classFunction);

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
          var resolutionContext = new ResolutionContext(new NoContext(currentClass.EnclosingModuleDefinition), false);
          ResolveAttributes(member, resolutionContext);
        } else if (member is Function) {
          var f = (Function)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(f.TypeArgs, false, f);
          ResolveFunction(f);
          allTypeParameters.PopMarker();
          if (f is ExtremePredicate ef && ef.PrefixPredicate != null && ec == reporter.Count(ErrorLevel.Error)) {
            var ff = ef.PrefixPredicate;
            allTypeParameters.PushMarker();
            ResolveTypeParameters(ff.TypeArgs, false, ff);
            ResolveFunction(ff);
            allTypeParameters.PopMarker();
          }

        } else if (member is Method) {
          var m = (Method)member;
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(m.TypeArgs, false, m);
          ResolveMethod(m);
          allTypeParameters.PopMarker();
          if (m is ExtremeLemma em && em.PrefixLemma != null && ec == reporter.Count(ErrorLevel.Error)) {
            var mm = em.PrefixLemma;
            allTypeParameters.PushMarker();
            ResolveTypeParameters(mm.TypeArgs, false, mm);
            ResolveMethod(mm);
            allTypeParameters.PopMarker();
          }

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
            if (co != null && codt.EnclosingModuleDefinition == co.EnclosingModuleDefinition) {
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
      if (dependee != null && dt.EnclosingModuleDefinition == dependee.EnclosingModuleDefinition) {
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

    void ResolveAttributes(IAttributeBearingDeclaration attributeHost, ResolutionContext resolutionContext) {
      Contract.Requires(resolutionContext != null);
      Contract.Requires(attributeHost != null);

      // order does not matter much for resolution, so resolve them in reverse order
      foreach (var attr in attributeHost.Attributes.AsEnumerable()) {
        if (attr is UserSuppliedAttributes) {
          var usa = (UserSuppliedAttributes)attr;
          usa.Recognized = IsRecognizedAttribute(usa, attributeHost);
        }
        if (attr.Args != null) {
          foreach (var arg in attr.Args) {
            Contract.Assert(arg != null);
            int prevErrors = reporter.Count(ErrorLevel.Error);
            ResolveExpression(arg, resolutionContext);
            if (prevErrors == reporter.Count(ErrorLevel.Error)) {
              CheckTypeInference(arg, resolutionContext.CodeContext);
            }
          }
        }
      }
    }

    void ResolveParameterDefaultValues(List<Formal> formals, ResolutionContext resolutionContext) {
      Contract.Requires(formals != null);
      Contract.Requires(resolutionContext != null);

      var dependencies = new Graph<IVariable>();
      var allowMoreRequiredParameters = true;
      var allowNamelessParameters = true;
      foreach (var formal in formals) {
        var d = formal.DefaultValue;
        if (d != null) {
          allowMoreRequiredParameters = false;
          ResolveExpression(d, resolutionContext);
          AddAssignableConstraint(d.tok, formal.Type, d.Type, "default-value expression (of type '{1}') is not assignable to formal (of type '{0}')");
          foreach (var v in FreeVariables(d)) {
            dependencies.AddEdge(formal, v);
          }
        } else if (!allowMoreRequiredParameters) {
          reporter.Error(MessageSource.Resolver, formal.tok, "a required parameter must precede all optional parameters");
        }
        if (!allowNamelessParameters && !formal.HasName) {
          reporter.Error(MessageSource.Resolver, formal.tok, "a nameless parameter must precede all nameonly parameters");
        }
        if (formal.IsNameOnly) {
          allowNamelessParameters = false;
        }
      }
      SolveAllTypeConstraints();

      foreach (var cycle in dependencies.AllCycles()) {
        var cy = Util.Comma(" -> ", cycle, v => v.Name) + " -> " + cycle[0].Name;
        reporter.Error(MessageSource.Resolver, cycle[0], $"default-value expressions for parameters contain a cycle: {cy}");
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

      if (f.IsGhost) {
        foreach (TypeParameter p in f.TypeArgs) {
          if (p.SupportsEquality) {
            reporter.Warning(MessageSource.Resolver, p.tok,
              $"type parameter {p.Name} of ghost {f.WhatKind} {f.Name} is declared (==), which is unnecessary because the {f.WhatKind} doesn't contain any compiled code");
          }
        }
      }

      foreach (Formal p in f.Formals) {
        scope.Push(p.Name, p);
      }
      ResolveAttributes(f, new ResolutionContext(f, false));
      // take care of the warnShadowing attribute
      if (Attributes.ContainsBool(f.Attributes, "warnShadowing", ref warnShadowing)) {
        DafnyOptions.O.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }
      ResolveParameterDefaultValues(f.Formals, ResolutionContext.FromCodeContext(f));
      foreach (AttributedExpression e in f.Req) {
        ResolveAttributes(e, new ResolutionContext(f, f is TwoStateFunction));
        Expression r = e.E;
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction));
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(r, "Precondition must be a boolean (got {0})");
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpressionTopLevel(fr, FrameExpressionUse.Reads, f);
      }
      foreach (AttributedExpression e in f.Ens) {
        Expression r = e.E;
        if (f.Result != null) {
          scope.PushMarker();
          scope.Push(f.Result.Name, f.Result);  // function return only visible in post-conditions
        }
        ResolveAttributes(e, new ResolutionContext(f, f is TwoStateFunction));
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction) with { InFunctionPostcondition = true });
        Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(r, "Postcondition must be a boolean (got {0})");
        if (f.Result != null) {
          scope.PopMarker();
        }
      }
      ResolveAttributes(f.Decreases, new ResolutionContext(f, f is TwoStateFunction));
      foreach (Expression r in f.Decreases.Expressions) {
        ResolveExpression(r, new ResolutionContext(f, f is TwoStateFunction));
        // any type is fine
      }
      SolveAllTypeConstraints();

      if (f.ByMethodBody != null) {
        // The following conditions are assured by the parser and other callers of the Function constructor
        Contract.Assert(f.Body != null);
        Contract.Assert(!f.IsGhost);
      }
      if (f.Body != null) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(f.Body, new ResolutionContext(f, f is TwoStateFunction));
        Contract.Assert(f.Body.Type != null);  // follows from postcondition of ResolveExpression
        AddAssignableConstraint(f.tok, f.ResultType, f.Body.Type, "Function body type mismatch (expected {0}, got {1})");
        SolveAllTypeConstraints();

        if (f.ByMethodBody != null) {
          var method = f.ByMethodDecl;
          if (method != null) {
            ResolveMethod(method);
          } else {
            // method should have been filled in by now,
            // unless there was a function by method and a method of the same name
            // but then this error must have been reported.
            Contract.Assert(reporter.ErrorCount > 0);
          }
        }
      }

      scope.PopMarker();

      DafnyOptions.O.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
    }

    public enum FrameExpressionUse { Reads, Modifies, Unchanged }

    void ResolveFrameExpressionTopLevel(FrameExpression fe, FrameExpressionUse use, ICodeContext codeContext) {
      ResolveFrameExpression(fe, use, new ResolutionContext(codeContext, false));
    }

    void ResolveFrameExpression(FrameExpression fe, FrameExpressionUse use, ResolutionContext resolutionContext) {
      Contract.Requires(fe != null);
      Contract.Requires(resolutionContext != null);

      ResolveExpression(fe.E, resolutionContext);
      Type t = fe.E.Type;
      Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
      var eventualRefType = new InferredTypeProxy();
      if (use == FrameExpressionUse.Reads) {
        AddXConstraint(fe.E.tok, "ReadsFrame", t, eventualRefType,
          "a reads-clause expression must denote an object, a set/iset/multiset/seq of objects, or a function to a set/iset/multiset/seq of objects (instead got {0})");
      } else {
        AddXConstraint(fe.E.tok, "ModifiesFrame", t, eventualRefType,
          use == FrameExpressionUse.Modifies ?
          "a modifies-clause expression must denote an object or a set/iset/multiset/seq of objects (instead got {0})" :
          "an unchanged expression must denote an object or a set/iset/multiset/seq of objects (instead got {0})");
      }
      if (fe.FieldName != null) {
        NonProxyType tentativeReceiverType;
        var member = ResolveMember(fe.E.tok, eventualRefType, fe.FieldName, out tentativeReceiverType);
        var ctype = (UserDefinedType)tentativeReceiverType;  // correctness of cast follows from the DenotesClass test above
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

        if (m.IsGhost) {
          foreach (TypeParameter p in m.TypeArgs) {
            if (p.SupportsEquality) {
              reporter.Warning(MessageSource.Resolver, p.tok,
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
          scope.Push(p.Name, p);
        }
        ResolveParameterDefaultValues(m.Ins, new ResolutionContext(m, m is TwoStateLemma));

        // Start resolving specification...
        foreach (AttributedExpression e in m.Req) {
          ResolveAttributes(e, new ResolutionContext(m, m is TwoStateLemma));
          ResolveExpression(e.E, new ResolutionContext(m, m is TwoStateLemma));
          Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
        }

        ResolveAttributes(m.Mod, new ResolutionContext(m, false));
        foreach (FrameExpression fe in m.Mod.Expressions) {
          ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Modifies, m);
          if (m.IsLemmaLike) {
            reporter.Error(MessageSource.Resolver, fe.tok, "{0}s are not allowed to have modifies clauses", m.WhatKind);
          } else if (m.IsGhost) {
            DisallowNonGhostFieldSpecifiers(fe);
          }
        }
        ResolveAttributes(m.Decreases, new ResolutionContext(m, false));
        foreach (Expression e in m.Decreases.Expressions) {
          ResolveExpression(e, new ResolutionContext(m, m is TwoStateLemma));
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
        if (m is ExtremeLemma && m.Outs.Count != 0) {
          reporter.Error(MessageSource.Resolver, m.Outs[0].tok, "{0}s are not allowed to have out-parameters", m.WhatKind);
        } else {
          foreach (Formal p in m.Outs) {
            scope.Push(p.Name, p);
          }
        }

        // ... continue resolving specification
        foreach (AttributedExpression e in m.Ens) {
          ResolveAttributes(e, new ResolutionContext(m, true));
          ResolveExpression(e.E, new ResolutionContext(m, true));
          Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
        }
        SolveAllTypeConstraints();

        // Resolve body
        if (m.Body != null) {
          if (m is ExtremeLemma com && com.PrefixLemma != null) {
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
          ResolveBlockStatement(m.Body, ResolutionContext.FromCodeContext(m));
          dominatingStatementLabels.PopMarker();
          SolveAllTypeConstraints();
        }

        // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for greatest lemmas)
        ResolveAttributes(m, new ResolutionContext(m, m is TwoStateLemma));

        DafnyOptions.O.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
        scope.PopMarker();  // for the out-parameters and outermost-level locals
        scope.PopMarker();  // for the in-parameters
      }
      finally {
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
      ResolveParameterDefaultValues(iter.Ins, new ResolutionContext(iter, false));

      // Start resolving specification...
      // we start with the decreases clause, because the _decreases<n> fields were only given type proxies before; we'll know
      // the types only after resolving the decreases clause (and it may be that some of resolution has already seen uses of
      // these fields; so, with no further ado, here we go
      ResolveAttributes(iter.Decreases, new ResolutionContext(iter, false));
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        ResolveExpression(e, new ResolutionContext(iter, false));
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        // If the following type constraint does not hold, then: Bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
        ConstrainSubtypeRelation(d.Type, e.Type, e, "type of field {0} is {1}, but has been constrained elsewhere to be of type {2}", d.Name, e.Type, d.Type);
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Reads, iter);
      }
      ResolveAttributes(iter.Modifies, new ResolutionContext(iter, false));
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Modifies, iter);
      }
      foreach (AttributedExpression e in iter.Requires) {
        ResolveAttributes(e, new ResolutionContext(iter, false));
        ResolveExpression(e.E, new ResolutionContext(iter, false));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
      }

      scope.PopMarker();  // for the in-parameters

      // We resolve the rest of the specification in an instance context.  So mentions of the in- or yield-parameters
      // get resolved as field dereferences (with an implicit "this")
      scope.PushMarker();
      currentClass = iter;
      Contract.Assert(scope.AllowInstance);

      foreach (AttributedExpression e in iter.YieldRequires) {
        ResolveAttributes(e, new ResolutionContext(iter, false));
        ResolveExpression(e.E, new ResolutionContext(iter, false));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Yield precondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.YieldEnsures) {
        ResolveAttributes(e, new ResolutionContext(iter, true));
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Yield postcondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.Ensures) {
        ResolveAttributes(e, new ResolutionContext(iter, true));
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
      }
      SolveAllTypeConstraints();

      ResolveAttributes(iter, new ResolutionContext(iter, false));

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
        ResolveBlockStatement(iter.Body, ResolutionContext.FromCodeContext(iter));
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

      iter.EnclosingModuleDefinition.CallGraph.AddEdge(iter.Member_MoveNext, iter);
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
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// </summary>
    public void ResolveType(IToken tok, Type type, ResolutionContext resolutionContext, ResolveTypeOptionEnum eopt, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(eopt != ResolveTypeOptionEnum.AllowPrefixExtend);
      ResolveType(tok, type, resolutionContext, new ResolveTypeOption(eopt), defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ICodeContext topLevelContext, ResolveTypeOptionEnum eopt, List<TypeParameter> defaultTypeArguments) {
      ResolveType(tok, type, ResolutionContext.FromCodeContext(topLevelContext), eopt, defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ICodeContext topLevelContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      ResolveType(tok, type, ResolutionContext.FromCodeContext(topLevelContext), option, defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ResolutionContext resolutionContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(option != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));
      var r = ResolveTypeLenient(tok, type, resolutionContext, option, defaultTypeArguments, false);
      Contract.Assert(r == null);
    }

    public class ResolveTypeReturn {
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
    public ResolveTypeReturn ResolveTypeLenient(IToken tok, Type type, ResolutionContext resolutionContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments, bool allowDanglingDotName) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(resolutionContext != null);
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
          ResolveType(tok, mt.Domain, resolutionContext, option, defaultTypeArguments);
          ResolveType(tok, mt.Range, resolutionContext, option, defaultTypeArguments);
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
          ResolveType(tok, t.Arg, resolutionContext, option, defaultTypeArguments);
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
        if (t.ResolvedClass != null) {
          // Apparently, this type has already been resolved
          return null;
        }
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        if (t.NamePath is ExprDotName) {
          var ret = ResolveDotSuffix_Type((ExprDotName)t.NamePath, resolutionContext, allowDanglingDotName, option, defaultTypeArguments);
          if (ret != null) {
            return ret;
          }
        } else {
          var s = (NameSegment)t.NamePath;
          ResolveNameSegment_Type(s, resolutionContext, option, defaultTypeArguments);
        }
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var r = t.NamePath.Resolved as Resolver_IdentifierExpr;
          if (r == null || !(r.Type is Resolver_IdentifierExpr.ResolverType_Type)) {
            reporter.Error(MessageSource.Resolver, t.tok, "expected type");
          } else if (r.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            var d = r.Decl;
            if (d is OpaqueTypeDecl) {
              // resolve like a type parameter, and it may have type parameters if it's an opaque type
              t.ResolvedClass = d;  // Store the decl, so the compiler will generate the fully qualified name
            } else if (d is RedirectingTypeDecl) {
              var dd = (RedirectingTypeDecl)d;
              var caller = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) as ICallable;
              if (caller != null && !(d is SubsetTypeDecl && caller is SpecialFunction)) {
                if (caller != d) {
                  caller.EnclosingModule.CallGraph.AddEdge(caller, dd);
                } else if (d is TypeSynonymDecl && !(d is SubsetTypeDecl)) {
                  // detect self-loops here, since they don't show up in the graph's SCC methods
                  reporter.Error(MessageSource.Resolver, d.tok, "type-synonym cycle: {0} -> {0}", d.Name);
                } else {
                  // detect self-loops here, since they don't show up in the graph's SCC methods
                  reporter.Error(MessageSource.Resolver, d.tok, "recursive constraint dependency involving a {0}: {1} -> {1}", d.WhatKind, d.Name);
                }
              }
              t.ResolvedClass = d;
            } else if (d is DatatypeDecl) {
              var dd = (DatatypeDecl)d;
              var caller = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) as ICallable;
              if (caller != null) {
                caller.EnclosingModule.CallGraph.AddEdge(caller, dd);
              }
              t.ResolvedClass = d;
            } else {
              // d is a type parameter, coinductive datatype, or class, and it may have type parameters
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
        if (t.ResolvedClass == null) {
          // There was some error. Still, we will set .ResolvedClass to some value to prevent some crashes in the downstream resolution.  The
          // 0-tuple is convenient, because it is always in scope.
          t.ResolvedClass = builtIns.TupleType(t.tok, 0, false);
          // clear out the TypeArgs since 0-tuple doesn't take TypeArg
          t.TypeArgs = new List<Type>();
        }

      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T != null) {
          ResolveType(tok, t.T, resolutionContext, option, defaultTypeArguments);
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
              tp.Characteristics.AutoInit = Type.AutoInitInfo.CompilableValue;
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
    Type ResolvedArrayType(IToken tok, int dims, Type arg, ResolutionContext resolutionContext, bool useClassNameType) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      var at = builtIns.ArrayType(tok, dims, new List<Type> { arg }, false, useClassNameType);
      ResolveType(tok, at, resolutionContext, ResolveTypeOptionEnum.DontInfer, null);
      return at;
    }

    public void ResolveStatement(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      if (!(stmt is ForallStmt || stmt is ForLoopStmt)) {  // "forall" and "for" statements do their own attribute resolution below
        ResolveAttributes(stmt, resolutionContext);
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
        ResolveExpression(s.Expr, resolutionContext);
        Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(s.Expr, "condition is expected to be of type bool, but is {0}");
        if (assertStmt != null && assertStmt.Proof != null) {
          // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave a the proof body
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(assertStmt.Proof, resolutionContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        }
        var expectStmt = stmt as ExpectStmt;
        if (expectStmt != null) {
          if (expectStmt.Message == null) {
            expectStmt.Message = new StringLiteralExpr(s.Tok, "expectation violation", false);
          }
          ResolveExpression(expectStmt.Message, resolutionContext);
          Contract.Assert(expectStmt.Message.Type != null);  // follows from postcondition of ResolveExpression
        }

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        s.Args.Iter(e => ResolveExpression(e, resolutionContext));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        foreach (var expr in s.Exprs) {
          var name = RevealStmt.SingleName(expr);
          var labeledAssert = name == null ? null : dominatingStatementLabels.Find(name) as AssertLabel;
          if (labeledAssert != null) {
            s.LabeledAsserts.Add(labeledAssert);
          } else {
            var revealResolutionContext = resolutionContext with { InReveal = true };
            if (expr is ApplySuffix) {
              var e = (ApplySuffix)expr;
              var methodCallInfo = ResolveApplySuffix(e, revealResolutionContext, true);
              if (methodCallInfo == null) {
                reporter.Error(MessageSource.Resolver, expr.tok, "expression has no reveal lemma");
              } else if (methodCallInfo.Callee.Member is TwoStateLemma && !revealResolutionContext.IsTwoState) {
                reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "a two-state function can only be revealed in a two-state context");
              } else if (methodCallInfo.Callee.AtLabel != null) {
                Contract.Assert(methodCallInfo.Callee.Member is TwoStateLemma);
                reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "to reveal a two-state function, do not list any parameters or @-labels");
              } else {
                var call = new CallStmt(methodCallInfo.Tok, s.EndTok, new List<Expression>(), methodCallInfo.Callee, methodCallInfo.ActualParameters);
                s.ResolvedStatements.Add(call);
              }
            } else if (expr is NameSegment or ExprDotName) {
              if (expr is NameSegment) {
                ResolveNameSegment((NameSegment)expr, true, null, revealResolutionContext, true);
              } else {
                ResolveDotSuffix((ExprDotName)expr, true, null, revealResolutionContext, true);
              }
              MemberSelectExpr callee = (MemberSelectExpr)((ConcreteSyntaxExpression)expr).ResolvedExpression;
              if (callee == null) {
              } else if (callee.Member is Lemma or TwoStateLemma && Attributes.Contains(callee.Member.Attributes, "axiom")) {
                //The revealed member is a function
                reporter.Error(MessageSource.Resolver, callee.tok, "to reveal a function ({0}), append parentheses", callee.Member.ToString().Substring(7));
              } else {
                var call = new CallStmt(expr.tok, s.EndTok, new List<Expression>(), callee, new List<ActualBinding>());
                s.ResolvedStatements.Add(call);
              }
            } else {
              ResolveExpression(expr, revealResolutionContext);
            }
          }
        }
        foreach (var a in s.ResolvedStatements) {
          ResolveStatement(a, resolutionContext);
        }
      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          Statement target = enclosingStatementLabels.Find(s.TargetLabel.val);
          if (target == null) {
            reporter.Error(MessageSource.Resolver, s.TargetLabel, $"{s.Kind} label is undefined or not in scope: {s.TargetLabel.val}");
          } else if (s.IsContinue && !(target is LoopStmt)) {
            reporter.Error(MessageSource.Resolver, s.TargetLabel, $"continue label must designate a loop: {s.TargetLabel.val}");
          } else {
            s.TargetStmt = target;
          }
        } else {
          Contract.Assert(1 <= s.BreakAndContinueCount); // follows from BreakStmt class invariant and the guard for this "else" branch
          var jumpStmt = s.BreakAndContinueCount == 1 ?
            $"a non-labeled '{s.Kind}' statement" :
            $"a '{Util.Repeat(s.BreakAndContinueCount - 1, "break ")}{s.Kind}' statement";
          if (loopStack.Count == 0) {
            reporter.Error(MessageSource.Resolver, s, $"{jumpStmt} is allowed only in loops");
          } else if (loopStack.Count < s.BreakAndContinueCount) {
            reporter.Error(MessageSource.Resolver, s,
              $"{jumpStmt} is allowed only in contexts with {s.BreakAndContinueCount} enclosing loops, but the current context only has {loopStack.Count}");
          } else {
            Statement target = loopStack[loopStack.Count - s.BreakAndContinueCount];
            if (target.Labels == null) {
              // make sure there is a label, because the compiler and translator will want to see a unique ID
              target.Labels = new LList<Label>(new Label(target.Tok, null), null);
            }
            s.TargetStmt = target;
          }
        }

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        if (stmt is YieldStmt && !(resolutionContext.CodeContext is IteratorDecl)) {
          reporter.Error(MessageSource.Resolver, stmt, "yield statement is allowed only in iterators");
        } else if (stmt is ReturnStmt && !(resolutionContext.CodeContext is Method)) {
          reporter.Error(MessageSource.Resolver, stmt, "return statement is allowed only in method");
        } else if (resolutionContext.InFirstPhaseConstructor) {
          reporter.Error(MessageSource.Resolver, stmt, "return statement is not allowed before 'new;' in a constructor");
        }
        var s = (ProduceStmt)stmt;
        if (s.Rhss != null) {
          var cmc = resolutionContext.CodeContext as IMethodCodeContext;
          if (cmc == null) {
            // an error has already been reported above
          } else if (cmc.Outs.Count != s.Rhss.Count) {
            reporter.Error(MessageSource.Resolver, s, "number of {2} parameters does not match declaration (found {0}, expected {1})", s.Rhss.Count, cmc.Outs.Count, kind);
          } else {
            Contract.Assert(s.Rhss.Count > 0);
            // Create a hidden update statement using the out-parameter formals, resolve the RHS, and check that the RHS is good.
            List<Expression> formals = new List<Expression>();
            foreach (Formal f in cmc.Outs) {
              Expression produceLhs;
              if (stmt is ReturnStmt) {
                var ident = new ImplicitIdentifierExpr(f.tok, f.Name);
                // resolve it here to avoid capture into more closely declared local variables
                ident.Var = f;
                ident.Type = ident.Var.Type;
                Contract.Assert(f.Type != null);
                produceLhs = ident;
              } else {
                var yieldIdent = new MemberSelectExpr(f.tok, new ImplicitThisExpr(f.tok), f.Name);
                ResolveExpression(yieldIdent, resolutionContext);
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
            }
            s.HiddenUpdate = new UpdateStmt(s.Tok, s.EndTok, formals, s.Rhss, true);
            // resolving the update statement will check for return/yield statement specifics.
            ResolveStatement(s.HiddenUpdate, resolutionContext);
          }
        } else {// this is a regular return/yield statement.
          s.HiddenUpdate = null;
        }
      } else if (stmt is ConcreteUpdateStatement) {
        ResolveConcreteUpdateStmt((ConcreteUpdateStatement)stmt, resolutionContext);
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
          ResolveType(local.Tok, local.OptionalType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
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
          ResolveConcreteUpdateStmt(s.Update, resolutionContext);
        }

        if (s.Update is AssignOrReturnStmt) {
          var assignOrRet = (AssignOrReturnStmt)s.Update;
          // resolve the LHS
          Contract.Assert(assignOrRet.Lhss.Count == s.Locals.Count);
          for (int i = 0; i < s.Locals.Count; i++) {
            var local = s.Locals[i];
            var lhs = (IdentifierExpr)assignOrRet
              .Lhss[i]; // the LHS in this case will be an IdentifierExpr, because that's how the parser creates the VarDeclStmt
            Contract.Assert(lhs.Type == null); // not yet resolved
            lhs.Var = local;
            lhs.Type = local.Type;
          }

          // resolve the whole thing
          ResolveAssignOrReturnStmt(assignOrRet, resolutionContext);
        }
        // Add the locals to the scope
        foreach (var local in s.Locals) {
          ScopePushAndReport(scope, local, "local-variable");
        }
        // With the new locals in scope, it's now time to resolve the attributes on all the locals
        foreach (var local in s.Locals) {
          ResolveAttributes(local, resolutionContext);
        }
        // Resolve the AssignSuchThatStmt, if any
        if (s.Update is AssignSuchThatStmt) {
          ResolveConcreteUpdateStmt(s.Update, resolutionContext);
        }
        // Check on "assumption" variables
        foreach (var local in s.Locals) {
          if (Attributes.Contains(local.Attributes, "assumption")) {
            if (currentMethod != null) {
              ConstrainSubtypeRelation(Type.Bool, local.type, local.Tok, "assumption variable must be of type 'bool'");
              if (!local.IsGhost) {
                reporter.Error(MessageSource.Resolver, local.Tok, "assumption variable must be ghost");
              }
            } else {
              reporter.Error(MessageSource.Resolver, local.Tok, "assumption variable can only be declared in a method");
            }
          }
        }
      } else if (stmt is VarDeclPattern) {
        VarDeclPattern s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(local.Tok, local.OptionalType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
            local.type = local.OptionalType;
          } else {
            local.type = new InferredTypeProxy();
          }
        }
        ResolveExpression(s.RHS, resolutionContext);
        ResolveCasePattern(s.LHS, s.RHS.Type, resolutionContext);
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
        ResolveExpression(s.Lhs, resolutionContext);  // allow ghosts for now, tighted up below
        bool lhsResolvedSuccessfully = reporter.Count(ErrorLevel.Error) == prevErrorCount;
        Contract.Assert(s.Lhs.Type != null);  // follows from postcondition of ResolveExpression
        // check that LHS denotes a mutable variable or a field
        var lhs = s.Lhs.Resolved;
        if (lhs is IdentifierExpr) {
          IVariable var = ((IdentifierExpr)lhs).Var;
          if (var == null) {
            // the LHS didn't resolve correctly; some error would already have been reported
          } else {
            CheckIsLvalue(lhs, resolutionContext);

            var localVar = var as LocalVariable;
            if (localVar != null && currentMethod != null && Attributes.Contains(localVar.Attributes, "assumption")) {
              var rhs = s.Rhs as ExprRhs;
              var expr = (rhs != null ? rhs.Expr : null);
              var binaryExpr = expr as BinaryExpr;
              if (binaryExpr != null
                  && (binaryExpr.Op == BinaryExpr.Opcode.And)
                  && (binaryExpr.E0.Resolved is IdentifierExpr)
                  && ((IdentifierExpr)(binaryExpr.E0.Resolved)).Var == localVar
                  && !currentMethod.AssignedAssumptionVariables.Contains(localVar)) {
                currentMethod.AssignedAssumptionVariables.Add(localVar);
              } else {
                reporter.Error(MessageSource.Resolver, stmt,
                  string.Format("there may be at most one assignment to an assumption variable, the RHS of which must match the expression \"{0} && <boolean expression>\"", localVar.Name));
              }
            }
          }
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          if (fse.Member != null) {  // otherwise, an error was reported above
            CheckIsLvalue(fse, resolutionContext);
          }
        } else if (lhs is SeqSelectExpr) {
          var slhs = (SeqSelectExpr)lhs;
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            Contract.Assert(slhs.Seq.Type != null);
            CheckIsLvalue(slhs, resolutionContext);
          }
        } else if (lhs is MultiSelectExpr) {
          CheckIsLvalue(lhs, resolutionContext);
        } else {
          CheckIsLvalue(lhs, resolutionContext);
        }
        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, resolutionContext);
          Contract.Assert(rr.Expr.Type != null);  // follows from postcondition of ResolveExpression

          if (s.Lhs is ImplicitIdentifierExpr { Var: Formal { InParam: false } }) {
            AddAssignableConstraint(stmt.Tok, lhsType, rr.Expr.Type, "Method return value mismatch (expected {0}, got {1})");
          } else {
            AddAssignableConstraint(stmt.Tok, lhsType, rr.Expr.Type, "RHS (of type {1}) not assignable to LHS (of type {0})");
          }
        } else if (s.Rhs is TypeRhs) {
          TypeRhs rr = (TypeRhs)s.Rhs;
          Type t = ResolveTypeRhs(rr, stmt, resolutionContext);
          AddAssignableConstraint(stmt.Tok, lhsType, t, "type {1} is not assignable to LHS (of type {0})");
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        ResolveCallStmt(s, resolutionContext, null);

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        ResolveBlockStatement(s, resolutionContext);
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        if (s.Guard != null) {
          ResolveExpression(s.Guard, resolutionContext);
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
        ResolveBlockStatement(s.Thn, resolutionContext);
        dominatingStatementLabels.PopMarker();
        scope.PopMarker();

        if (s.Els != null) {
          dominatingStatementLabels.PushMarker();
          ResolveStatement(s.Els, resolutionContext);
          dominatingStatementLabels.PopMarker();
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        ResolveAlternatives(s.Alternatives, null, resolutionContext);

      } else if (stmt is OneBodyLoopStmt) {
        var s = (OneBodyLoopStmt)stmt;
        var fvs = new HashSet<IVariable>();
        var usesHeap = false;
        if (s is WhileStmt whileS && whileS.Guard != null) {
          ResolveExpression(whileS.Guard, resolutionContext);
          Contract.Assert(whileS.Guard.Type != null);  // follows from postcondition of ResolveExpression
          FreeVariablesUtil.ComputeFreeVariables(whileS.Guard, fvs, ref usesHeap);
          ConstrainTypeExprBool(whileS.Guard, "condition is expected to be of type bool, but is {0}");
        } else if (s is ForLoopStmt forS) {
          var loopIndex = forS.LoopIndex;
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(loopIndex.Tok, loopIndex.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var err = new TypeConstraint.ErrorMsgWithToken(loopIndex.Tok, "index variable is expected to be of an integer type (got {0})", loopIndex.Type);
          ConstrainToIntegerType(loopIndex.Tok, loopIndex.Type, false, err);
          fvs.Add(loopIndex);

          ResolveExpression(forS.Start, resolutionContext);
          FreeVariablesUtil.ComputeFreeVariables(forS.Start, fvs, ref usesHeap);
          AddAssignableConstraint(forS.Start.tok, forS.LoopIndex.Type, forS.Start.Type, "lower bound (of type {1}) not assignable to index variable (of type {0})");
          if (forS.End != null) {
            ResolveExpression(forS.End, resolutionContext);
            FreeVariablesUtil.ComputeFreeVariables(forS.End, fvs, ref usesHeap);
            AddAssignableConstraint(forS.End.tok, forS.LoopIndex.Type, forS.End.Type, "upper bound (of type {1}) not assignable to index variable (of type {0})");
            if (forS.Decreases.Expressions.Count != 0) {
              reporter.Error(MessageSource.Resolver, forS.Decreases.Expressions[0].tok,
                "a 'for' loop is allowed an explicit 'decreases' clause only if the end-expression is '*'");
            }
          } else if (forS.Decreases.Expressions.Count == 0 && !resolutionContext.CodeContext.AllowsNontermination) {
            // note, the following error message is also emitted elsewhere (if the loop bears a "decreases *")
            reporter.Error(MessageSource.Resolver, forS.Tok,
              "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating" +
              " (or you can add a 'decreases' clause to this 'for' loop if you want to prove that it does indeed terminate)");
          }

          // Create a new scope, add the local to the scope, and resolve the attributes
          scope.PushMarker();
          ScopePushAndReport(scope, loopIndex, "index-variable");
          ResolveAttributes(s, resolutionContext);
        }

        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext, fvs, ref usesHeap);

        if (s.Body != null) {
          loopStack.Add(s);  // push
          dominatingStatementLabels.PushMarker();
          ResolveStatement(s.Body, resolutionContext);
          dominatingStatementLabels.PopMarker();
          loopStack.RemoveAt(loopStack.Count - 1);  // pop
        } else {
          Contract.Assert(s.BodySurrogate == null);  // .BodySurrogate is set only once
          var loopFrame = new List<IVariable>();
          if (s is ForLoopStmt forLoopStmt) {
            loopFrame.Add(forLoopStmt.LoopIndex);
          }
          loopFrame.AddRange(fvs.Where(fv => fv.IsMutable));
          s.BodySurrogate = new WhileStmt.LoopBodySurrogate(loopFrame, usesHeap);
          var text = Util.Comma(s.BodySurrogate.LocalLoopTargets, fv => fv.Name);
          if (s.BodySurrogate.UsesHeap) {
            text += text.Length == 0 ? "$Heap" : ", $Heap";
          }
          text = string.Format("note, this loop has no body{0}", text.Length == 0 ? "" : " (loop frame: " + text + ")");
          reporter.Warning(MessageSource.Resolver, s.Tok, text);
        }

        if (s is ForLoopStmt) {
          scope.PopMarker();
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        ResolveAlternatives(s.Alternatives, s, resolutionContext);
        var usesHeapDontCare = false;
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext, null, ref usesHeapDontCare);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in s.BoundVars) {
          ScopePushAndReport(scope, v, "local-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
        ResolveExpression(s.Range, resolutionContext);
        Contract.Assert(s.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(s.Range, "range restriction in forall statement must be of type bool (instead got {0})");
        foreach (var ens in s.Ens) {
          ResolveExpression(ens.E, resolutionContext);
          Contract.Assert(ens.E.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(ens.E, "ensures condition is expected to be of type bool, but is {0}");
        }
        // Since the range and postconditions are more likely to infer the types of the bound variables, resolve them
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(s, resolutionContext);

        if (s.Body != null) {
          // clear the labels for the duration of checking the body, because break statements are not allowed to leave a forall statement
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(s.Body, resolutionContext);
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

              var rhs = ((AssignStmt)s0).Rhs;
              if (rhs is TypeRhs) {
                reporter.Error(MessageSource.Resolver, rhs.Tok, "new allocation not supported in aggregate assignments");
              }

            } else if (s0 is CallStmt) {
              s.Kind = ForallStmt.BodyKind.Call;
              var call = (CallStmt)s.S0;
              var method = call.Method;
              // if the called method is not in the same module as the ForallCall stmt
              // don't convert it to ForallExpression since the inlined called method's
              // ensure clause might not be resolved correctly(test\dafny3\GenericSort.dfy)
              if (method.EnclosingClass.EnclosingModuleDefinition != resolutionContext.CodeContext.EnclosingModule) {
                s.CanConvert = false;
              }
              // Additional information (namely, the postcondition of the call) will be reported later. But it cannot be
              // done yet, because the specification of the callee may not have been resolved yet.
            } else if (s0 is CalcStmt) {
              s.Kind = ForallStmt.BodyKind.Proof;
              // add the conclusion of the calc as a free postcondition
              var result = ((CalcStmt)s0).Result;
              s.Ens.Add(new AttributedExpression(result));
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

          if (s.ForallExpressions != null) {
            foreach (Expression expr in s.ForallExpressions) {
              ResolveExpression(expr, resolutionContext);
            }
          }
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        ResolveAttributes(s.Mod, resolutionContext);
        foreach (FrameExpression fe in s.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext);
        }
        if (s.Body != null) {
          ResolveBlockStatement(s.Body, resolutionContext);
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
          ResolveExpression(e0, resolutionContext);
          Contract.Assert(e0.Type != null);  // follows from postcondition of ResolveExpression
          var err = new TypeConstraint.ErrorMsgWithToken(e0.tok, "all lines in a calculation must have the same type (got {0} after {1})", e0.Type, lineType);
          ConstrainSubtypeRelation(lineType, e0.Type, err);
          for (int i = 1; i < s.Lines.Count; i++) {
            var e1 = s.Lines[i];
            ResolveExpression(e1, resolutionContext);
            Contract.Assert(e1.Type != null);  // follows from postcondition of ResolveExpression
            // reuse the error object if we're on the dummy line; this prevents a duplicate error message
            if (i < s.Lines.Count - 1) {
              err = new TypeConstraint.ErrorMsgWithToken(e1.tok, "all lines in a calculation must have the same type (got {0} after {1})", e1.Type, lineType);
            }
            ConstrainSubtypeRelation(lineType, e1.Type, err);
            var step = (s.StepOps[i - 1] ?? s.Op).StepExpr(e0, e1); // Use custom line operator
            ResolveExpression(step, resolutionContext);
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
              ResolveStatement(oneHint, resolutionContext);
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
        ResolveExpression(s.Result, resolutionContext);
        Contract.Assert(s.Result != null);
        Contract.Assert(prevErrorCount != reporter.Count(ErrorLevel.Error) || s.Steps.Count == s.Hints.Count);

      } else if (stmt is MatchStmt) {
        ResolveMatchStmt((MatchStmt)stmt, resolutionContext);

      } else if (stmt is NestedMatchStmt) {
        var s = (NestedMatchStmt)stmt;
        ResolveNestedMatchStmt(s, resolutionContext);
      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        reporter.Error(MessageSource.Resolver, s.Tok, "skeleton statements are allowed only in refining methods");
        // nevertheless, resolve the underlying statement; hey, why not
        if (s.S != null) {
          ResolveStatement(s.S, resolutionContext);
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveLoopSpecificationComponents(List<AttributedExpression> invariants, Specification<Expression> decreases,
      Specification<FrameExpression> modifies, ResolutionContext resolutionContext, HashSet<IVariable> fvs, ref bool usesHeap) {
      Contract.Requires(invariants != null);
      Contract.Requires(decreases != null);
      Contract.Requires(modifies != null);
      Contract.Requires(resolutionContext != null);

      foreach (AttributedExpression inv in invariants) {
        ResolveAttributes(inv, resolutionContext);
        ResolveExpression(inv.E, resolutionContext);
        Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
        if (fvs != null) {
          FreeVariablesUtil.ComputeFreeVariables(inv.E, fvs, ref usesHeap);
        }
        ConstrainTypeExprBool(inv.E, "invariant is expected to be of type bool, but is {0}");
      }

      ResolveAttributes(decreases, resolutionContext);
      foreach (Expression e in decreases.Expressions) {
        ResolveExpression(e, resolutionContext);
        if (e is WildcardExpr && !resolutionContext.CodeContext.AllowsNontermination) {
          reporter.Error(MessageSource.Resolver, e, "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating");
        }
        if (fvs != null) {
          FreeVariablesUtil.ComputeFreeVariables(e, fvs, ref usesHeap);
        }
        // any type is fine
      }

      ResolveAttributes(modifies, resolutionContext);
      if (modifies.Expressions != null) {
        usesHeap = true;  // bearing a modifies clause counts as using the heap
        foreach (FrameExpression fe in modifies.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext);
        }
      }
    }

    /// <summary>
    /// Resolves a NestedMatchStmt by
    /// 1 - checking that all of its patterns are linear
    /// 2 - desugaring it into a decision tree of MatchStmt and IfStmt (for constant matching)
    /// 3 - resolving the generated (sub)statement.
    /// </summary>
    void ResolveNestedMatchStmt(NestedMatchStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(s.ResolvedStatement == null);

      bool debugMatch = DafnyOptions.O.MatchCompilerDebug;

      Contract.Assert(resolutionContext.IsTwoState); // refactoring sanity check
      ResolveExpression(s.Source, resolutionContext);
      Contract.Assert(s.Source.Type != null);  // follows from postcondition of ResolveExpression

      if (s.Source.Type is TypeProxy) {
        PartiallySolveTypeConstraints(true);

        if (debugMatch) {
          Console.WriteLine("DEBUG: Type of {0} was still a proxy, solving type constraints results in type {1}", Printer.ExprToString(s.Source), s.Source.Type.ToString());
        }

        if (s.Source.Type is TypeProxy) {
          reporter.Error(MessageSource.Resolver, s.Tok, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
          return;
        }
      }

      var sourceType = PartiallyResolveTypeForMemberSelection(s.Source.tok, s.Source.Type).NormalizeExpand();

      var errorCount = reporter.Count(ErrorLevel.Error);
      CheckLinearNestedMatchStmt(sourceType, s, resolutionContext);
      if (reporter.Count(ErrorLevel.Error) != errorCount) {
        return;
      }

      errorCount = reporter.Count(ErrorLevel.Error);
      CompileNestedMatchStmt(s, resolutionContext);
      if (reporter.Count(ErrorLevel.Error) != errorCount) {
        return;
      }

      enclosingStatementLabels.PushMarker();
      ResolveStatement(s.ResolvedStatement, resolutionContext);
      enclosingStatementLabels.PopMarker();
    }

    void ResolveMatchStmt(MatchStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(s.OrigUnresolved == null);

      // first, clone the original match statement
      s.OrigUnresolved = (MatchStmt)new ClonerKeepParensExpressions().CloneStmt(s);
      ResolveExpression(s.Source, resolutionContext);
      Contract.Assert(s.Source.Type != null);  // follows from postcondition of ResolveExpression
      var errorCount = reporter.Count(ErrorLevel.Error);
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
        subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs); // build the type-parameter substitution map for this use of the datatype
      }

      ISet<string> memberNamesUsed = new HashSet<string>();

      foreach (MatchCaseStmt mc in s.Cases) {
        if (ctors != null) {
          Contract.Assert(dtd != null);
          var ctorId = mc.Ctor.Name;
          if (s.Source.Type.AsDatatype is TupleTypeDecl) {
            var tuple = (TupleTypeDecl)s.Source.Type.AsDatatype;
            ctorId = BuiltIns.TupleTypeCtorName(tuple.Dims);
          }
          if (!ctors.ContainsKey(ctorId)) {
            reporter.Error(MessageSource.Resolver, mc.tok, "member '{0}' does not exist in datatype '{1}'", ctorId, dtd.Name);
          } else {
            if (mc.Ctor.Formals.Count != mc.Arguments.Count) {
              if (s.Source.Type.AsDatatype is TupleTypeDecl) {
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
          ResolveStatementWithLabels(ss, resolutionContext);
        }
        dominatingStatementLabels.PopMarker();

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

    /* Temporary information about the Match being desugared  */
    private class MatchTempInfo {
      public IToken Tok;
      public IToken EndTok;
      public IToken[] BranchTok;
      public int[] BranchIDCount; // Records the number of copies of each branch
      public bool isStmt; // true if we are desugaring a MatchStmt, false if a MatchExpr
      public bool Debug;
      public readonly ICodeContext CodeContext;
      public List<ExtendedPattern> MissingCases;
      public Attributes Attributes;

      public MatchTempInfo(IToken tok, int branchidnum, ICodeContext codeContext, bool debug = false, Attributes attrs = null) {
        int[] init = new int[branchidnum];
        for (int i = 0; i < branchidnum; i++) {
          init[i] = 1;
        }
        this.Tok = tok;
        this.EndTok = tok;
        this.BranchTok = new IToken[branchidnum];
        this.BranchIDCount = init;
        this.isStmt = false;
        this.Debug = debug;
        this.CodeContext = codeContext;
        this.MissingCases = new List<ExtendedPattern>();
        this.Attributes = attrs;
      }
      public MatchTempInfo(IToken tok, IToken endtok, int branchidnum, ICodeContext codeContext, bool debug = false, Attributes attrs = null) {
        int[] init = new int[branchidnum];
        for (int i = 0; i < branchidnum; i++) {
          init[i] = 1;
        }
        this.Tok = tok;
        this.EndTok = endtok;
        this.BranchTok = new IToken[branchidnum];
        this.BranchIDCount = init;
        this.isStmt = true;
        this.Debug = debug;
        this.CodeContext = codeContext;
        this.MissingCases = new List<ExtendedPattern>();
        this.Attributes = attrs;
      }

      public void UpdateBranchID(int branchID, int update) {
        BranchIDCount[branchID] += update;
      }
    }

    /// <summary>
    /// A SyntaxContainer is a wrapper around either an Expression or a Statement
    /// It allows for generic functions over the two syntax spaces of Dafny
    /// </summary>
    private abstract class SyntaxContainer {
      public readonly IToken Tok;

      public SyntaxContainer(IToken tok) {
        this.Tok = tok;
      }
    }

    private class CExpr : SyntaxContainer {
      public readonly Expression Body;
      public Attributes Attributes;

      public CExpr(IToken tok, Expression body, Attributes attrs = null) : base(tok) {
        this.Body = body;
        this.Attributes = attrs;
      }
    }

    private class CStmt : SyntaxContainer {
      public readonly Statement Body;
      public Attributes Attributes;

      public CStmt(IToken tok, Statement body, Attributes attrs = null) : base(tok) {
        this.Body = body;
        this.Attributes = attrs;
      }
    }

    /// Unwraps a CStmt and returns its Body as a BlockStmt
    private BlockStmt BlockStmtOfCStmt(IToken tok, IToken endTok, CStmt con) {
      var stmt = con.Body;
      if (stmt is BlockStmt) {
        return (BlockStmt)stmt;
      } else {
        var stmts = new List<Statement>();
        stmts.Add(stmt);
        return new BlockStmt(tok, endTok, stmts);
      }
    }

    /// <summary>
    /// RBranch is an intermediate data-structure representing a branch during pattern-match compilation
    /// </summary>
    private abstract class RBranch {
      public readonly IToken Tok;
      public int BranchID;
      public List<ExtendedPattern> Patterns;

      public RBranch(IToken tok, int branchid, List<ExtendedPattern> patterns) {
        Contract.Requires(patterns.All(p => !(p is DisjunctivePattern)));
        this.Tok = tok;
        this.BranchID = branchid;
        this.Patterns = patterns;
      }
    }


    private class RBranchStmt : RBranch {
      public List<Statement> Body;
      public Attributes Attributes;

      public RBranchStmt(IToken tok, int branchid, List<ExtendedPattern> patterns, List<Statement> body, Attributes attrs = null) : base(tok, branchid, patterns) {
        this.Body = body;
        this.Attributes = attrs;
      }

      public RBranchStmt(int branchid, NestedMatchCaseStmt x, Attributes attrs = null) : base(x.Tok, branchid, new List<ExtendedPattern>()) {
        Contract.Requires(!(x.Pat is DisjunctivePattern)); // No nested or patterns
        this.Body = new List<Statement>(x.Body); // Resolving the body will insert new elements.
        this.Attributes = attrs;
        this.Patterns.Add(x.Pat);
      }

      public override string ToString() {
        var bodyStr = "";
        foreach (var stmt in this.Body) {
          bodyStr += string.Format("{1}{0};\n", Printer.StatementToString(stmt), "\t");
        }
        return string.Format("\t> id: {0}\n\t> patterns: <{1}>\n\t-> body:\n{2} \n", this.BranchID, String.Join(",", this.Patterns.ConvertAll(x => x.ToString())), bodyStr);
      }
    }

    private class RBranchExpr : RBranch {

      public Expression Body;
      public Attributes Attributes;

      public RBranchExpr(IToken tok, int branchid, List<ExtendedPattern> patterns, Expression body, Attributes attrs = null) : base(tok, branchid, patterns) {
        this.Body = body;
        this.Attributes = attrs;
      }

      public RBranchExpr(int branchid, NestedMatchCaseExpr x, Attributes attrs = null) : base(x.Tok, branchid, new List<ExtendedPattern>()) {
        this.Body = x.Body;
        this.Patterns.Add(x.Pat);
        this.Attributes = attrs;
      }

      public override string ToString() {
        return string.Format("\t> id: {0}\n\t-> patterns: <{1}>\n\t-> body: {2}", this.BranchID, String.Join(",", this.Patterns.ConvertAll(x => x.ToString())), Printer.ExprToString(this.Body));
      }
    }

    private class ClonerButIVariablesAreKeptOnce : ClonerKeepParensExpressions {
      private HashSet<IVariable> alreadyCloned = new();

      private VT CloneIVariableHelper<VT>(VT local, Func<VT, VT> returnMethod) where VT : IVariable {
        if (!alreadyCloned.Contains(local)) {
          alreadyCloned.Add(local);
          return local;
        }

        return returnMethod(local);
      }

      public override LocalVariable CloneLocalVariable(LocalVariable local) {
        return CloneIVariableHelper(local, base.CloneLocalVariable);
      }

      public override Formal CloneFormal(Formal local) {
        return CloneIVariableHelper(local, base.CloneFormal);
      }
      public override BoundVar CloneBoundVar(BoundVar local) {
        return CloneIVariableHelper(local, base.CloneBoundVar);
      }
    }

    private Cloner matchBranchCloner = new ClonerButIVariablesAreKeptOnce();

    // deep clone Patterns and Body
    private RBranchStmt CloneRBranchStmt(RBranchStmt branch) {
      Cloner cloner = matchBranchCloner;
      return new RBranchStmt(branch.Tok, branch.BranchID, branch.Patterns.ConvertAll(x => cloner.CloneExtendedPattern(x)), branch.Body.ConvertAll(x => cloner.CloneStmt(x)), cloner.CloneAttributes(branch.Attributes));
    }

    private RBranchExpr CloneRBranchExpr(RBranchExpr branch) {
      Cloner cloner = matchBranchCloner;
      return new RBranchExpr(branch.Tok, branch.BranchID, branch.Patterns.ConvertAll(x => cloner.CloneExtendedPattern(x)), cloner.CloneExpr(branch.Body), cloner.CloneAttributes((branch.Attributes)));
    }

    private RBranch CloneRBranch(RBranch branch) {
      if (branch is RBranchStmt) {
        return CloneRBranchStmt((RBranchStmt)branch);
      } else {
        return CloneRBranchExpr((RBranchExpr)branch);
      }
    }

    private static ExtendedPattern getPatternHead(RBranch branch) {
      return branch.Patterns.First();
    }

    private static RBranch dropPatternHead(RBranch branch) {
      branch.Patterns.RemoveAt(0);
      return branch;
    }

    private SyntaxContainer PackBody(IToken tok, RBranch branch) {
      if (branch is RBranchStmt br) {
        return new CStmt(tok, new BlockStmt(tok, tok, br.Body), br.Attributes);
      } else if (branch is RBranchExpr) {
        return new CExpr(tok, ((RBranchExpr)branch).Body, ((RBranchExpr)branch).Attributes);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException(); // RBranch has only two implementations
      }
    }

    private List<Statement> UnboxStmtContainer(SyntaxContainer con) {
      if (con is CStmt cstmt) {
        if (cstmt.Body is BlockStmt block) {
          return block.Body;
        } else {
          return new List<Statement>() { cstmt.Body };
        }
      } else {
        throw new NotImplementedException("Bug in CompileRBranch: expected a StmtContainer");
      }
    }

    // let-bind a variable of name "name" and type "type" as "expr" on the body of "branch"
    private void LetBind(RBranch branch, IdPattern var, Expression genExpr) {
      var name = var.Id;
      var type = var.Type;
      var isGhost = var.IsGhost;

      // if the expression is a generated IdentifierExpr, replace its token by the branch's
      Expression expr = genExpr;
      if (genExpr is IdentifierExpr idExpr) {
        if (idExpr.Name.StartsWith("_")) {
          expr = new IdentifierExpr(var.Tok, idExpr.Var);
        }
      }
      if (branch is RBranchStmt branchStmt) {
        var cLVar = new LocalVariable(var.Tok, var.Tok, name, type, isGhost);
        var cPat = new CasePattern<LocalVariable>(cLVar.EndTok, cLVar);
        var cLet = new VarDeclPattern(cLVar.Tok, cLVar.Tok, cPat, expr, false);
        branchStmt.Body.Insert(0, cLet);
      } else if (branch is RBranchExpr branchExpr) {
        var cBVar = new BoundVar(new AutoGeneratedToken(var.Tok), name, type);
        cBVar.IsGhost = isGhost;
        var cPat = new CasePattern<BoundVar>(cBVar.Tok, cBVar);
        var cPats = new List<CasePattern<BoundVar>>();
        cPats.Add(cPat);
        var exprs = new List<Expression>();
        exprs.Add(expr);
        var cLet = new LetExpr(cBVar.tok, cPats, exprs, branchExpr.Body, true);
        branchExpr.Body = cLet;
      }
      return;
    }

    // If cp is not a wildcard, replace branch.Body with let cp = expr in branch.Body
    // Otherwise do nothing
    private void LetBindNonWildCard(RBranch branch, IdPattern var, Expression expr) {
      if (!var.IsWildcardPattern) {
        LetBind(branch, var, expr);
      }
    }

    // Assumes that all SyntaxContainers in blocks and def are of the same subclass
    private SyntaxContainer MakeIfFromContainers(MatchTempInfo mti, MatchingContext context, Expression matchee, List<Tuple<LiteralExpr, SyntaxContainer>> blocks, SyntaxContainer def) {

      if (blocks.Count == 0) {
        if (def is CStmt sdef) {
          // Ensures the statements are wrapped in braces
          return new CStmt(null, BlockStmtOfCStmt(sdef.Body.Tok, sdef.Body.EndTok, sdef));
        } else {
          return def;
        }
      }

      Tuple<LiteralExpr, SyntaxContainer> currBlock = blocks.First();
      blocks = blocks.Skip(1).ToList();

      IToken tok = matchee.tok;
      IToken endtok = matchee.tok;
      Expression guard = new BinaryExpr(tok, BinaryExpr.Opcode.Eq, matchee, currBlock.Item1);

      var elsC = MakeIfFromContainers(mti, context, matchee, blocks, def);

      if (currBlock.Item2 is CExpr) {
        var item2 = (CExpr)currBlock.Item2;
        if (elsC is null) {
          // handle an empty default
          // assert guard; item2.Body
          var contextStr = context.FillHole(new IdCtx(string.Format("c: {0}", matchee.Type.ToString()), new List<MatchingContext>())).AbstractAllHoles().ToString();
          var errorMessage = new StringLiteralExpr(mti.Tok, string.Format("missing case in match expression: {0} (not all possibilities for constant 'c' in context have been covered)", contextStr), true);
          var attr = new Attributes("error", new List<Expression>() { errorMessage }, null);
          var ag = new AssertStmt(mti.Tok, endtok, new AutoGeneratedExpression(mti.Tok, guard), null, null, attr);
          return new CExpr(null, new StmtExpr(tok, ag, item2.Body));
        } else {
          var els = (CExpr)elsC;
          return new CExpr(null, new ITEExpr(tok, false, guard, item2.Body, els.Body));
        }
      } else {
        var item2 = BlockStmtOfCStmt(tok, endtok, (CStmt)currBlock.Item2);
        if (elsC is null) {
          // handle an empty default
          // assert guard; item2.Body
          var contextStr = context.FillHole(new IdCtx(string.Format("c: {0}", matchee.Type.ToString()), new List<MatchingContext>())).AbstractAllHoles().ToString();
          var errorMessage = new StringLiteralExpr(mti.Tok, string.Format("missing case in match statement: {0} (not all possibilities for constant 'c' have been covered)", contextStr), true);
          var attr = new Attributes("error", new List<Expression>() { errorMessage }, null);
          var ag = new AssertStmt(mti.Tok, endtok, new AutoGeneratedExpression(mti.Tok, guard), null, null, attr);
          var body = new List<Statement>();
          body.Add(ag);
          body.AddRange(item2.Body);
          return new CStmt(null, new BlockStmt(tok, endtok, body));
        } else {
          var els = (CStmt)elsC;
          return new CStmt(null, new IfStmt(tok, endtok, false, guard, item2, els.Body));
        }
      }
    }


    private MatchCase MakeMatchCaseFromContainer(IToken tok, KeyValuePair<string, DatatypeCtor> ctor, List<BoundVar> freshPatBV, SyntaxContainer insideContainer, bool FromBoundVar) {
      MatchCase newMatchCase;
      if (insideContainer is CStmt c) {
        List<Statement> insideBranch = UnboxStmtContainer(insideContainer);
        newMatchCase = new MatchCaseStmt(tok, ctor.Value, FromBoundVar, freshPatBV, insideBranch, c.Attributes);
      } else {
        var insideBranch = ((CExpr)insideContainer).Body;
        var attrs = ((CExpr)insideContainer).Attributes;
        newMatchCase = new MatchCaseExpr(tok, ctor.Value, FromBoundVar, freshPatBV, insideBranch, attrs);
      }
      newMatchCase.Ctor = ctor.Value;
      return newMatchCase;
    }

    private BoundVar CreatePatBV(IToken tok, Type type, ICodeContext codeContext) {
      var name = FreshTempVarName("_mcc#", codeContext);
      return new BoundVar(new AutoGeneratedToken(tok), name, type);
    }

    private IdPattern CreateFreshId(IToken tok, Type type, ICodeContext codeContext, bool isGhost = false) {
      var name = FreshTempVarName("_mcc#", codeContext);
      return new IdPattern(new AutoGeneratedToken(tok), name, type, null, isGhost);
    }

    private void PrintRBranches(MatchingContext context, List<Expression> matchees, List<RBranch> branches) {
      Console.WriteLine("\t=-------=");
      Console.WriteLine("\tCurrent context:");
      Console.WriteLine("\t> {0}", context.ToString());
      Console.WriteLine("\tCurrent matchees:");

      foreach (Expression matchee in matchees) {
        Console.WriteLine("\t> {0}", Printer.ExprToString(matchee));
      }
      Console.WriteLine("\tCurrent branches:");
      foreach (RBranch branch in branches) {
        Console.WriteLine(branch.ToString());
      }
      Console.WriteLine("\t-=======-");
    }

    /*
     * Implementation of case 3** (some of the head patterns are constants) of pattern-match compilation
     * PairPB contains, for each branches, its head pattern and the rest of the branch.
     */
    private SyntaxContainer CompileRBranchConstant(MatchTempInfo mti, MatchingContext context, Expression currMatchee, List<Expression> matchees, List<Tuple<ExtendedPattern, RBranch>> pairPB) {
      // Decrease the count for each branch (increases back for each occurence later on)
      foreach (var PB in pairPB) {
        mti.UpdateBranchID(PB.Item2.BranchID, -1);
      }

      // Create a list of alternatives
      List<LiteralExpr> alternatives = new List<LiteralExpr>();
      foreach (var PB in pairPB) {
        var pat = PB.Item1;
        LiteralExpr lit = null;
        if (pat is LitPattern lpat) {
          lit = lpat.OptimisticallyDesugaredLit;
        } else if (pat is IdPattern id && id.ResolvedLit != null) {
          lit = id.ResolvedLit;
        }

        if (lit != null && !alternatives.Exists(x => object.Equals(x.Value, lit.Value))) {
          alternatives.Add(lit);
        }
      }

      List<Tuple<LiteralExpr, SyntaxContainer>> currBlocks = new List<Tuple<LiteralExpr, SyntaxContainer>>();
      // For each possible alternatives, filter potential cases and recur
      foreach (var currLit in alternatives) {
        List<RBranch> currBranches = new List<RBranch>();
        foreach (var PB in pairPB) {
          var pat = PB.Item1;
          LiteralExpr lit = null;
          if (pat is LitPattern lpat) {
            lit = lpat.OptimisticallyDesugaredLit;
          }

          if (pat is IdPattern id && id.ResolvedLit != null) {
            lit = id.ResolvedLit;
          }

          if (lit != null) {
            // if pattern matches the current alternative, add it to the branch for this case, otherwise ignore it
            if (object.Equals(lit.Value, currLit.Value)) {
              mti.UpdateBranchID(PB.Item2.BranchID, 1);
              currBranches.Add(CloneRBranch(PB.Item2));
            }
          } else if (pat is IdPattern currPattern) {
            // pattern is a bound variable, clone and let-bind the Lit
            var currBranch = CloneRBranch(PB.Item2);
            LetBindNonWildCard(currBranch, currPattern, (new ClonerKeepParensExpressions()).CloneExpr(currLit));
            mti.UpdateBranchID(PB.Item2.BranchID, 1);
            currBranches.Add(currBranch);
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }
        }
        // Update the current context
        MatchingContext newcontext = context.FillHole(new LitCtx(currLit));

        // Recur on the current alternative
        var currBlock = CompileRBranch(mti, newcontext, matchees.Select(x => x).ToList(), currBranches);
        currBlocks.Add(new Tuple<LiteralExpr, SyntaxContainer>(currLit, currBlock));
      }
      // Create a default case
      List<RBranch> defaultBranches = new List<RBranch>();
      for (int i = 0; i < pairPB.Count; i++) {
        var PB = pairPB.ElementAt(i);
        if (PB.Item1 is IdPattern currPattern && currPattern.ResolvedLit == null && currPattern.Arguments == null) {
          // Pattern is a bound variable, clone and let-bind the Lit
          var currBranch = CloneRBranch(PB.Item2);
          LetBindNonWildCard(currBranch, currPattern, currMatchee);
          mti.UpdateBranchID(PB.Item2.BranchID, 1);
          defaultBranches.Add(currBranch);
        }
      }
      // defaultBranches.Count check is to avoid adding "missing branches" when default is not present
      SyntaxContainer defaultBlock = defaultBranches.Count == 0 ? null : CompileRBranch(mti, context.AbstractHole(), matchees.Select(x => x).ToList(), defaultBranches);

      // Create If-construct joining the alternatives
      var ifcon = MakeIfFromContainers(mti, context, currMatchee, currBlocks, defaultBlock);
      return ifcon;
    }

    /*
     * Implementation of case 3 (some of the head patterns are constructors) of pattern-match compilation
     * Current matchee is a datatype (with type parameter substitution in subst) with constructors in ctors
     * PairPB contains, for each branches, its head pattern and the rest of the branch.
     */
    private SyntaxContainer CompileRBranchConstructor(MatchTempInfo mti, MatchingContext context, Expression currMatchee, Dictionary<TypeParameter, Type> subst, Dictionary<string, DatatypeCtor> ctors, List<Expression> matchees, List<Tuple<ExtendedPattern, RBranch>> pairPB) {
      var newMatchCases = new List<MatchCase>();
      // Update mti -> each branch generates up to |ctors| copies of itself
      foreach (var PB in pairPB) {
        mti.UpdateBranchID(PB.Item2.BranchID, ctors.Count - 1);
      }

      var ctorToFromBoundVar = new HashSet<string>();

      foreach (var ctor in ctors) {
        if (mti.Debug) {
          Console.WriteLine("DEBUG: ===[3]>>>> Ctor {0}", ctor.Key);
        }

        var currBranches = new List<RBranch>();

        // create a bound variable for each formal to use in the MatchCase for this constructor
        // using the currMatchee.tok to get a location closer to the error if something goes wrong
        var freshPatBV = ctor.Value.Formals.ConvertAll(
          x => CreatePatBV(currMatchee.tok, x.Type.Subst(subst), mti.CodeContext));

        // rhs to bind to head-patterns that are bound variables
        var rhsExpr = currMatchee;
        var ctorCounter = 0;

        // -- filter branches for each constructor
        for (int i = 0; i < pairPB.Count; i++) {
          var PB = pairPB.ElementAt(i);
          if (PB.Item1 is IdPattern currPattern) {
            if (ctor.Key.Equals(currPattern.Id) && currPattern.Arguments != null) {
              // ==[3.1]== If pattern is same constructor, push the arguments as patterns and add that branch to new match
              // After making sure the constructor is applied to the right number of arguments
              var currBranch = CloneRBranch(PB.Item2);
              if (!(currPattern.Arguments.Count.Equals(ctor.Value.Formals.Count))) {
                reporter.Error(MessageSource.Resolver, mti.BranchTok[PB.Item2.BranchID], "constructor {0} of arity {1} is applied to {2} argument(s)", ctor.Key, ctor.Value.Formals.Count, currPattern.Arguments.Count);
              }
              for (int j = 0; j < currPattern.Arguments.Count; j++) {
                // mark patterns standing in for ghost field
                currPattern.Arguments[j].IsGhost = currPattern.Arguments[j].IsGhost || ctor.Value.Formals[j].IsGhost;
              }
              currBranch.Patterns.InsertRange(0, currPattern.Arguments);
              currBranches.Add(currBranch);
              ctorCounter++;
            } else if (ctors.ContainsKey(currPattern.Id) && currPattern.Arguments != null) {
              // ==[3.2]== If the pattern is a different constructor, drop the branch
              mti.UpdateBranchID(PB.Item2.BranchID, -1);
            } else if (currPattern.ResolvedLit != null) {
              // TODO
            } else {
              // ==[3.3]== If the pattern is a bound variable, create new bound variables for each of the arguments of the constructor, and let-binds the matchee as original bound variable
              // n.b. this may duplicate the matchee

              // make sure this potential bound var is not applied to anything, in which case it is likely a mispelled constructor
              if (currPattern.Arguments != null && currPattern.Arguments.Count != 0) {
                reporter.Error(MessageSource.Resolver, mti.BranchTok[PB.Item2.BranchID], "bound variable {0} applied to {1} argument(s).", currPattern.Id, currPattern.Arguments.Count);
              }

              var currBranch = CloneRBranch(PB.Item2);

              List<IdPattern> freshArgs = ctor.Value.Formals.ConvertAll(x =>
                CreateFreshId(currPattern.Tok, x.Type.Subst(subst), mti.CodeContext, x.IsGhost));

              currBranch.Patterns.InsertRange(0, freshArgs);
              LetBindNonWildCard(currBranch, currPattern, rhsExpr);
              currBranches.Add(currBranch);
              ctorToFromBoundVar.Add(ctor.Key);
            }
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }
        }
        // Add variables corresponding to the arguments of the current constructor (ctor) to the matchees
        List<IdentifierExpr> freshMatchees = freshPatBV.ConvertAll(x => new IdentifierExpr(x.tok, x));
        List<Expression> cmatchees = matchees.Select(x => x).ToList();
        cmatchees.InsertRange(0, freshMatchees);
        // Update the current context
        MatchingContext ctorctx = new IdCtx(ctor);
        MatchingContext newcontext = context.FillHole(ctorctx);
        var insideContainer = CompileRBranch(mti, newcontext, cmatchees, currBranches);
        if (insideContainer is null) {
          // If no branch matches this constructor, drop the case
          continue;
        } else {
          // Otherwise, add the case the new match created at [3]
          var tok = insideContainer.Tok is null ? new AutoGeneratedToken(currMatchee.tok) : insideContainer.Tok;
          var FromBoundVar = ctorToFromBoundVar.Contains(ctor.Key);
          MatchCase newMatchCase = MakeMatchCaseFromContainer(tok, ctor, freshPatBV, insideContainer, FromBoundVar);
          // newMatchCase.Attributes = (new ClonerKeepParensExpressions()).CloneAttributes(mti.Attributes);
          newMatchCases.Add(newMatchCase);
        }
      }
      // Generate and pack the right kind of Match
      if (mti.isStmt) {
        var newMatchCaseStmts = newMatchCases.Select(x => (MatchCaseStmt)x).ToList();
        foreach (var c in newMatchCaseStmts) {
          if (Attributes.Contains(c.Attributes, "split")) {
            continue;
          }

          var args = new List<Expression>();
          args.Add(new LiteralExpr(mti.Tok, false));
          c.Attributes = new Attributes("split", args, c.Attributes);
        }
        var newMatchStmt = new MatchStmt(mti.Tok, mti.EndTok, currMatchee, newMatchCaseStmts, true, mti.Attributes, context);
        return new CStmt(null, newMatchStmt);
      } else {
        var newMatchExpr = new MatchExpr(mti.Tok, currMatchee, newMatchCases.ConvertAll(x => (MatchCaseExpr)x), true, context);
        return new CExpr(null, newMatchExpr);
      }
    }

    /// <summary>
    /// Create a decision tree with flattened MatchStmt (or MatchExpr) with disjoint cases and if-constructs
    /// Start with a list of n matchees and list of m branches, each with n patterns and a body
    /// 1 - if m = 0, then no original branch exists for the current case, return null
    /// 2 - if n = 0, return the body of the first branch
    /// 3** - if the head-matchee is a base type, but some patterns are constants, create if-else construct for one level and recur
    /// 3 - if some of the head-patterns are constructors (including tuples), create one level of matching at the type of the head-matchee,
    ///     recur for each constructor of that datatype
    /// 4 - Otherwise, all head-patterns are variables, let-bind the head-matchee as the head-pattern in each of the bodypatterns,
    ///     continue processing the matchees
    /// </summary>
    private SyntaxContainer CompileRBranch(MatchTempInfo mti, MatchingContext context, List<Expression> matchees, List<RBranch> branches) {
      if (mti.Debug) {
        Console.WriteLine("DEBUG: In CompileRBranch:");
        PrintRBranches(context, matchees, branches);
      }

      // For each branch, number of matchees (n) is the number of patterns held by the branch
      if (!branches.TrueForAll(x => matchees.Count == x.Patterns.Count)) {
        reporter.Error(MessageSource.Resolver, mti.Tok, "Match is malformed, make sure constructors are fully applied");
      }

      if (branches.Count == 0) {
        // ==[1]== If no branch, then match is not syntactically exhaustive -- return null
        if (mti.Debug) {
          Console.WriteLine("DEBUG: ===[1]=== No Branch");
          Console.WriteLine("\t{0} Potential exhaustiveness failure on context: {1}", mti.Tok.line, context.AbstractAllHoles().ToString());
        }
        // (Semantics) exhaustiveness is checked by the verifier, so no need for a warning here
        // reporter.Warning(MessageSource.Resolver, mti.Tok, "non-exhaustive case-statement");
        return null;
      }

      if (matchees.Count == 0) {
        // ==[2]== No more matchee to process, return the first branch and decrement the count of dropped branches
        if (mti.Debug) {
          Console.WriteLine("DEBUG: ===[2]=== No Matchee");
          Console.WriteLine("\treturn Bid:{0}", branches.First().BranchID);
        }

        for (int i = 1; i < branches.Count; i++) {
          mti.UpdateBranchID(branches.ElementAt(i).BranchID, -1);
        }
        return PackBody(mti.BranchTok[branches.First().BranchID], branches.First());
      }

      // Otherwise, start handling the first matchee
      Expression currMatchee = matchees.First();
      matchees = matchees.Skip(1).ToList();

      // Get the datatype of the matchee
      var currMatcheeType = PartiallyResolveTypeForMemberSelection(currMatchee.tok, currMatchee.Type).NormalizeExpand();
      if (currMatcheeType is TypeProxy) {
        PartiallySolveTypeConstraints(true);
      }
      var dtd = currMatcheeType.AsDatatype;

      // Get all constructors of type matchee
      var subst = new Dictionary<TypeParameter, Type>();
      Dictionary<string, DatatypeCtor> ctors;
      if (dtd == null) {
        ctors = null;
      } else {
        ctors = datatypeCtors[dtd];
        Contract.Assert(ctors != null);  // dtd should have been inserted into datatypeCtors during a previous resolution stage
        subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, currMatcheeType.TypeArgs); // Build the type-parameter substitution map for this use of the datatype
      }

      // Get the head of each patterns
      var patternHeads = branches.ConvertAll(new Converter<RBranch, ExtendedPattern>(getPatternHead));
      var newBranches = branches.ConvertAll(new Converter<RBranch, RBranch>(dropPatternHead));
      var pairPB = patternHeads.Zip(newBranches, (x, y) => new Tuple<ExtendedPattern, RBranch>(x, y)).ToList();

      if (ctors != null && patternHeads.Exists(x => x is IdPattern && ((IdPattern)x).Arguments != null && ctors.ContainsKey(((IdPattern)x).Id))) {
        // ==[3]== If dtd is a datatype and at least one of the pattern is a constructor, create a match on currMatchee
        if (mti.Debug) {
          Console.WriteLine("DEBUG: ===[3]=== Constructor Case");
        }

        return CompileRBranchConstructor(mti, context, currMatchee, subst, ctors, matchees, pairPB);
      } else if (dtd == null && patternHeads.Exists(x => (x is LitPattern || (x is IdPattern id && id.ResolvedLit != null)))) {
        // ==[3**]== If dtd is a base type and at least one of the pattern is a constant, create an If-then-else construct on the constant
        if (mti.Debug) {
          Console.WriteLine("DEBUG: ===[3**]=== Constant Case");
        }

        return CompileRBranchConstant(mti, context, currMatchee, matchees, pairPB);
      } else {
        // ==[4]==  all head patterns are bound variables:
        if (mti.Debug) {
          Console.WriteLine("DEBUG: ===[4]=== Variable Case");
        }

        foreach (Tuple<ExtendedPattern, RBranch> PB in pairPB) {
          if (!(PB.Item1 is IdPattern)) {
            Contract.Assert(false); throw new cce.UnreachableException(); // in Variable case with a constant pattern
          }
          var currPattern = (IdPattern)PB.Item1;

          if (currPattern.Arguments != null) {
            if (dtd == null) {
              Contract.Assert(false); throw new cce.UnreachableException(); // non-nullary constructors of a non-datatype;
            } else {
              reporter.Error(MessageSource.Resolver, currPattern.Tok, "Type mismatch: expected constructor of type {0}.  Got {1}.", dtd.Name, currPattern.Id);
            }
          }
          // Optimization: Don't let-bind if name is a wildcard, either in source or generated
          LetBindNonWildCard(PB.Item2, currPattern, currMatchee);
        }
        if (mti.Debug) {
          Console.WriteLine("DEBUG: return");
        }
        return CompileRBranch(mti, context.AbstractHole(), matchees, pairPB.ToList().ConvertAll(new Converter<Tuple<ExtendedPattern, RBranch>, RBranch>(x => x.Item2)));
      }
    }

    private ExtendedPattern RemoveIllegalSubpatterns(ExtendedPattern pat, bool inDisjunctivePattern) {
      switch (pat) {
        case LitPattern:
          return pat;
        case IdPattern p:
          if (inDisjunctivePattern && p.ResolvedLit == null && p.Arguments == null && !p.IsWildcardPattern) {
            reporter.Error(MessageSource.Resolver, pat.Tok, "Disjunctive patterns may not bind variables");
            return new IdPattern(p.Tok, FreshTempVarName("_", null), null, p.IsGhost);
          }
          var args = p.Arguments?.ConvertAll(a => RemoveIllegalSubpatterns(a, inDisjunctivePattern));
          return new IdPattern(p.Tok, p.Id, p.Type, args, p.IsGhost) { ResolvedLit = p.ResolvedLit };
        case DisjunctivePattern p:
          reporter.Error(MessageSource.Resolver, pat.Tok, "Disjunctive patterns are not allowed inside other patterns");
          return new IdPattern(p.Tok, FreshTempVarName("_", null), null, p.IsGhost);
        default:
          Contract.Assert(false);
          return null;
      }
    }

    private IEnumerable<ExtendedPattern> FlattenDisjunctivePatterns(ExtendedPattern pat) {
      // TODO: Once we rewrite the pattern-matching compiler, we'll handle disjunctive patterns in it, too.
      // For now, we handle top-level disjunctive patterns by duplicating the corresponding cases here, and disjunctive
      // sub-patterns are unsupported.
      return pat is DisjunctivePattern p
        ? p.Alternatives.ConvertAll(a => RemoveIllegalSubpatterns(a, inDisjunctivePattern: true))
        : Enumerable.Repeat(RemoveIllegalSubpatterns(pat, inDisjunctivePattern: false), 1);
    }

    private IEnumerable<NestedMatchCaseExpr> FlattenNestedMatchCaseExpr(NestedMatchCaseExpr c) {
      var cloner = matchBranchCloner;
      foreach (var pat in FlattenDisjunctivePatterns(c.Pat)) {
        yield return new NestedMatchCaseExpr(c.Tok, pat, c.Body, c.Attributes);
      }
    }

    private IEnumerable<NestedMatchCaseStmt> FlattenNestedMatchCaseStmt(NestedMatchCaseStmt c) {
      var cloner = matchBranchCloner;
      foreach (var pat in FlattenDisjunctivePatterns(c.Pat)) {
        yield return new NestedMatchCaseStmt(c.Tok, pat, new List<Statement>(c.Body), c.Attributes);
      }
    }

    private void CompileNestedMatchExpr(NestedMatchExpr e, ResolutionContext resolutionContext) {
      if (e.ResolvedExpression != null) {
        //post-resolve, skip
        return;
      }
      if (DafnyOptions.O.MatchCompilerDebug) {
        Console.WriteLine("DEBUG: CompileNestedMatchExpr for match at line {0}", e.tok.line);
      }

      var cases = e.Cases.SelectMany(FlattenNestedMatchCaseExpr).ToList();
      MatchTempInfo mti = new MatchTempInfo(e.tok, cases.Count, resolutionContext.CodeContext, DafnyOptions.O.MatchCompilerDebug);

      // create Rbranches from MatchCaseExpr and set the branch tokens in mti
      List<RBranch> branches = new List<RBranch>();
      for (int id = 0; id < cases.Count; id++) {
        var branch = cases.ElementAt(id);
        branches.Add(new RBranchExpr(id, branch, branch.Attributes));
        mti.BranchTok[id] = branch.Tok;
      }

      List<Expression> matchees = new List<Expression>();
      matchees.Add(e.Source);
      SyntaxContainer rb = CompileRBranch(mti, new HoleCtx(), matchees, branches);
      if (rb is null) {
        // Happens only if the match has no cases, create a Match with no cases as resolved expression and let ResolveMatchExpr handle it.
        e.ResolvedExpression = new MatchExpr(e.tok, (new ClonerKeepParensExpressions()).CloneExpr(e.Source), new List<MatchCaseExpr>(), e.UsesOptionalBraces);
      } else if (rb is CExpr) {
        // replace e with desugared expression
        var newME = ((CExpr)rb).Body;
        e.ResolvedExpression = newME;
        for (int id = 0; id < mti.BranchIDCount.Length; id++) {
          if (mti.BranchIDCount[id] <= 0) {
            reporter.Warning(MessageSource.Resolver, mti.BranchTok[id], "this branch is redundant");
            scope.PushMarker();
            CheckLinearNestedMatchCase(e.Source.Type, cases.ElementAt(id), resolutionContext);
            ResolveExpression(cases.ElementAt(id).Body, resolutionContext);
            scope.PopMarker();
          }
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException(); // Returned container should be a CExpr
      }

      if (DafnyOptions.O.MatchCompilerDebug) {
        Console.WriteLine("DEBUG: Done CompileNestedMatchExpr at line {0}", mti.Tok.line);
      }

    }

    /// <summary>
    /// Stmt driver for CompileRBranch
    /// Input is an unresolved NestedMatchStmt with potentially nested, overlapping patterns
    /// On output, the NestedMatchStmt has field ResolvedStatement filled with semantically equivalent code
    /// </summary>
    private void CompileNestedMatchStmt(NestedMatchStmt s, ResolutionContext resolutionContext) {
      if (s.ResolvedStatement != null) {
        //post-resolve, skip
        return;
      }

      if (DafnyOptions.O.MatchCompilerDebug) {
        Console.WriteLine("DEBUG: CompileNestedMatchStmt for match at line {0}", s.Tok.line);
      }

      var cases = s.Cases.SelectMany(FlattenNestedMatchCaseStmt).ToList();
      // initialize the MatchTempInfo to record position and duplication information about each branch
      MatchTempInfo mti = new MatchTempInfo(s.Tok, s.EndTok, cases.Count, resolutionContext.CodeContext, DafnyOptions.O.MatchCompilerDebug, s.Attributes);

      // create Rbranches from NestedMatchCaseStmt and set the branch tokens in mti
      List<RBranch> branches = new List<RBranch>();
      for (int id = 0; id < cases.Count; id++) {
        var branch = cases.ElementAt(id);
        branches.Add(new RBranchStmt(id, branch, branch.Attributes));
        mti.BranchTok[id] = branch.Tok;
      }
      List<Expression> matchees = new List<Expression>();
      matchees.Add(s.Source);
      SyntaxContainer rb = CompileRBranch(mti, new HoleCtx(), matchees, branches);
      if (rb is null) {
        // Happens only if the nested match has no cases, create a MatchStmt with no branches.
        s.ResolvedStatement = new MatchStmt(s.Tok, s.EndTok, (new ClonerKeepParensExpressions()).CloneExpr(s.Source), new List<MatchCaseStmt>(), s.UsesOptionalBraces, s.Attributes);
      } else if (rb is CStmt c) {
        // Resolve s as desugared match
        s.ResolvedStatement = c.Body;
        s.ResolvedStatement.Attributes = (new ClonerKeepParensExpressions()).CloneAttributes(s.Attributes);
        for (int id = 0; id < mti.BranchIDCount.Length; id++) {
          if (mti.BranchIDCount[id] <= 0) {
            reporter.Warning(MessageSource.Resolver, mti.BranchTok[id], "this branch is redundant");
            scope.PushMarker();
            CheckLinearNestedMatchCase(s.Source.Type, cases.ElementAt(id), resolutionContext);
            cases.ElementAt(id).Body.ForEach(s => ResolveStatement(s, resolutionContext));
            scope.PopMarker();
          }
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException(); // Returned container should be a StmtContainer
      }

      if (DafnyOptions.O.MatchCompilerDebug) {
        Console.WriteLine("DEBUG: Done CompileNestedMatchStmt at line {0}.", mti.Tok.line);
      }
    }

    private void CheckLinearVarPattern(Type type, IdPattern pat, ResolutionContext resolutionContext) {
      if (pat.Arguments != null) {
        if (pat.Id == BuiltIns.TupleTypeCtorName(1)) {
          reporter.Error(MessageSource.Resolver, pat.Tok, "parentheses are not allowed around a pattern");
        } else {
          reporter.Error(MessageSource.Resolver, pat.Tok, "member {0} does not exist in type {1}", pat.Id, type);
        }
        return;
      }

      if (scope.FindInCurrentScope(pat.Id) != null) {
        reporter.Error(MessageSource.Resolver, pat.Tok, "Duplicate parameter name: {0}", pat.Id);
      } else if (pat.IsWildcardPattern) {
        // Wildcard, ignore
        return;
      } else {
        NameSegment e = new NameSegment(pat.Tok, pat.Id, null);
        ResolveNameSegment(e, true, null, resolutionContext, false, false);
        if (e.ResolvedExpression == null) {
          ScopePushAndReport(scope, new BoundVar(pat.Tok, pat.Id, type), "parameter");
        } else {
          // finds in full scope, not just current scope
          if (e.Resolved is MemberSelectExpr mse) {
            if (mse.Member.IsStatic && mse.Member is ConstantField cf) {
              Expression c = cf.Rhs;
              if (c is LiteralExpr lit) {
                pat.ResolvedLit = lit;
                if (type.Equals(e.ResolvedExpression.Type)) {
                  // OK - type is correct
                } else {
                  // may well be a proxy so add a type constraint
                  ConstrainSubtypeRelation(e.ResolvedExpression.Type, type, pat.Tok,
                    "the type of the pattern ({0}) does not agree with the match expression ({1})", e.ResolvedExpression.Type, type);
                }
              } else {
                reporter.Error(MessageSource.Resolver, pat.Tok, "{0} is not initialized as a constant literal", pat.Id);
                ScopePushAndReport(scope, new BoundVar(pat.Tok, pat.Id, type), "parameter");
              }
            } else {
              // Not a static const, so just a variable
              ScopePushAndReport(scope, new BoundVar(pat.Tok, pat.Id, type), "parameter");
            }
          } else {
            ScopePushAndReport(scope, new BoundVar(pat.Tok, pat.Id, type), "parameter");
          }
        }
      }
    }

    // pat could be
    // 0 - A DisjunctivePattern
    // 1 - An IdPattern (without argument) at base type
    // 2 - A LitPattern at base type
    // 3* - An IdPattern at tuple type representing a tuple
    // 3 - An IdPattern at datatype type representing a constructor of type
    // 4 - An IdPattern at datatype type with no arguments representing a bound variable
    private void CheckLinearExtendedPattern(Type type, ExtendedPattern pat, ResolutionContext resolutionContext) {
      if (type == null) {
        return;
      }

      if (pat is DisjunctivePattern dp) {
        foreach (var alt in dp.Alternatives) {
          // Pushing a scope silences the “duplicate parameter” error in
          // `CheckLinearVarPattern`.  This is acceptable because disjunctive
          // patterns are not allowed to bind variables (the corresponding
          // error is raised in `RemoveDisjunctivePatterns`).
          scope.PushMarker();
          CheckLinearExtendedPattern(type, alt, resolutionContext);
          scope.PopMarker();
        }
      } else if (!type.IsDatatype) { // Neither tuple nor datatype
        if (pat is IdPattern id) {
          if (id.Arguments != null) {
            // pat is a tuple or constructor
            if (id.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
              reporter.Error(MessageSource.Resolver, pat.Tok, $"tuple type does not match type {type.ToString()}");
            } else {
              reporter.Error(MessageSource.Resolver, pat.Tok, $"member {id.Id} does not exist in type {type.ToString()}");
            }
          } else { // pat is a simple variable or a constant
            /* =[1]= */
            CheckLinearVarPattern(type, (IdPattern)pat, resolutionContext);
          }
          return;
        } else if (pat is LitPattern) { // pat is a literal
          /* =[2]= */
          return;
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
      } else if (type.AsDatatype is TupleTypeDecl) {
        var udt = type.NormalizeExpand() as UserDefinedType;
        if (!(pat is IdPattern)) {
          reporter.Error(MessageSource.Resolver, pat.Tok, "pattern doesn't correspond to a tuple");
          return;
        }

        IdPattern idpat = (IdPattern)pat;
        if (idpat.Arguments == null) {
          // simple variable
          CheckLinearVarPattern(udt, idpat, resolutionContext);
          return;
        }

        //We expect the number of arguments in the type of the matchee and the provided pattern to match, except if the pattern is a bound variable
        if (udt.TypeArgs.Count != idpat.Arguments.Count) {
          if (idpat.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
            reporter.Error(MessageSource.Resolver, pat.Tok,
              $"the case pattern is a {idpat.Arguments.Count}-element tuple, while the match expression is a {udt.TypeArgs.Count}-element tuple");
          } else {
            reporter.Error(MessageSource.Resolver, pat.Tok,
              $"case pattern {idpat.Id} has {idpat.Arguments.Count} arguments whereas the match expression has {udt.TypeArgs.Count}");
          }
        }

        var pairTP = udt.TypeArgs.Zip(idpat.Arguments, (x, y) => new Tuple<Type, ExtendedPattern>(x, y));

        foreach (var tp in pairTP) {
          var t = PartiallyResolveTypeForMemberSelection(pat.Tok, tp.Item1).NormalizeExpand();
          CheckLinearExtendedPattern(t, tp.Item2, resolutionContext);
        }
        return;
      } else { // matching a datatype value
        if (!(pat is IdPattern)) {
          Contract.Assert(pat is LitPattern);
          reporter.Error(MessageSource.Resolver, pat.Tok, "Constant pattern used in place of datatype");
          return;
        }
        IdPattern idpat = (IdPattern)pat;

        var dtd = type.AsDatatype;
        Dictionary<string, DatatypeCtor> ctors = datatypeCtors[dtd];
        if (ctors == null) {
          Contract.Assert(false); throw new cce.UnreachableException();  // Datatype not found
        }
        DatatypeCtor ctor = null;
        // Check if the head of the pattern is a constructor or a variable
        if (ctors.TryGetValue(idpat.Id, out ctor)) {
          /* =[3]= */
          idpat.Ctor = ctor;
          if (ctor != null && idpat.Arguments == null && ctor.Formals.Count == 0) {
            // nullary constructor without () -- so convert it to a constructor
            idpat.MakeAConstructor();
          }
          if (idpat.Arguments == null) {
            // pat is a variable
            return;
          } else if (ctor.Formals != null && ctor.Formals.Count == idpat.Arguments.Count) {
            if (ctor.Formals.Count == 0) {
              // if nullary constructor
              return;
            } else {
              // if non-nullary constructor
              var subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, type.NormalizeExpand().TypeArgs);
              var argTypes = ctor.Formals.ConvertAll<Type>(x => x.Type.Subst(subst));
              var pairFA = argTypes.Zip(idpat.Arguments, (x, y) => new Tuple<Type, ExtendedPattern>(x, y));
              foreach (var fa in pairFA) {
                // get DatatypeDecl of Formal, recursive call on argument
                CheckLinearExtendedPattern(fa.Item1, fa.Item2, resolutionContext);
              }
            }
          } else {
            // else applied to the wrong number of arguments
            reporter.Error(MessageSource.Resolver, idpat.Tok, "constructor {0} of arity {2} is applied to {1} argument(s)", idpat.Id, (idpat.Arguments == null ? 0 : idpat.Arguments.Count), ctor.Formals.Count);
          }
        } else {
          /* =[4]= */
          // pattern is a variable OR error (handled in CheckLinearVarPattern)
          CheckLinearVarPattern(type, idpat, resolutionContext);
        }
      }
    }

    private void CheckLinearNestedMatchCase(Type type, NestedMatchCase mc, ResolutionContext resolutionContext) {
      CheckLinearExtendedPattern(type, mc.Pat, resolutionContext);
    }

    /*
    *  Ensures that all ExtendedPattern held in NestedMatchCase are linear
    *  Uses provided type to determine if IdPatterns are datatypes (of the provided type) or variables
    */
    private void CheckLinearNestedMatchExpr(Type dtd, NestedMatchExpr me, ResolutionContext resolutionContext) {
      foreach (NestedMatchCaseExpr mc in me.Cases) {
        scope.PushMarker();
        ResolveAttributes(mc, resolutionContext);
        CheckLinearNestedMatchCase(dtd, mc, resolutionContext);
        scope.PopMarker();
      }
    }

    private void CheckLinearNestedMatchStmt(Type dtd, NestedMatchStmt ms, ResolutionContext resolutionContext) {
      foreach (NestedMatchCaseStmt mc in ms.Cases) {
        scope.PushMarker();
        ResolveAttributes(mc, resolutionContext);
        CheckLinearNestedMatchCase(dtd, mc, resolutionContext);
        scope.PopMarker();
      }
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
    private void ResolveConcreteUpdateStmt(ConcreteUpdateStatement s, ResolutionContext resolutionContext) {
      Contract.Requires(resolutionContext != null);

      // First, resolve all LHS's and expression-looking RHS's.
      int errorCountBeforeCheckingLhs = reporter.Count(ErrorLevel.Error);

      var lhsNameSet = new HashSet<string>();  // used to check for duplicate identifiers on the left (full duplication checking for references and the like is done during verification)
      foreach (var lhs in s.Lhss) {
        var ec = reporter.Count(ErrorLevel.Error);
        ResolveExpression(lhs, resolutionContext);
        if (ec == reporter.Count(ErrorLevel.Error)) {
          if (lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne) {
            reporter.Error(MessageSource.Resolver, lhs, "cannot assign to a range of array elements (try the 'forall' statement)");
          }
        }
      }

      // Resolve RHSs
      if (s is AssignSuchThatStmt) {
        ResolveAssignSuchThatStmt((AssignSuchThatStmt)s, resolutionContext);
      } else if (s is UpdateStmt) {
        ResolveUpdateStmt((UpdateStmt)s, resolutionContext, errorCountBeforeCheckingLhs);
      } else if (s is AssignOrReturnStmt) {
        ResolveAssignOrReturnStmt((AssignOrReturnStmt)s, resolutionContext);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
      ResolveAttributes(s, resolutionContext);
    }
    /// <summary>
    /// Resolve the RHSs and entire UpdateStmt (LHSs should already have been checked by the caller).
    /// errorCountBeforeCheckingLhs is passed in so that this method can determined if any resolution errors were found during
    /// LHS or RHS checking, because only if no errors were found is update.ResolvedStmt changed.
    /// </summary>
    private void ResolveUpdateStmt(UpdateStmt update, ResolutionContext resolutionContext, int errorCountBeforeCheckingLhs) {
      Contract.Requires(update != null);
      Contract.Requires(resolutionContext != null);
      IToken firstEffectfulRhs = null;
      MethodCallInformation methodCallInfo = null;
      var j = 0;
      foreach (var rhs in update.Rhss) {
        bool isEffectful;
        if (rhs is TypeRhs) {
          var tr = (TypeRhs)rhs;
          ResolveTypeRhs(tr, update, resolutionContext);
          isEffectful = tr.InitCall != null;
        } else if (rhs is HavocRhs) {
          isEffectful = false;
        } else {
          var er = (ExprRhs)rhs;
          if (er.Expr is ApplySuffix) {
            var a = (ApplySuffix)er.Expr;
            var cRhs = ResolveApplySuffix(a, resolutionContext, true);
            isEffectful = cRhs != null;
            methodCallInfo = methodCallInfo ?? cRhs;
          } else {
            ResolveExpression(er.Expr, resolutionContext);
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
          CallStmt a = new CallStmt(methodCallInfo.Tok, update.EndTok, resolvedLhss, methodCallInfo.Callee, methodCallInfo.ActualParameters);
          a.OriginalInitialLhs = update.OriginalInitialLhs;
          update.ResolvedStatements.Add(a);
        }
      }

      foreach (var a in update.ResolvedStatements) {
        ResolveStatement(a, resolutionContext);
      }
    }

    private void ResolveAssignSuchThatStmt(AssignSuchThatStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);

      var lhsSimpleVariables = new HashSet<IVariable>();
      foreach (var lhs in s.Lhss) {
        if (lhs.Resolved != null) {
          CheckIsLvalue(lhs.Resolved, resolutionContext);
        } else {
          Contract.Assert(reporter.ErrorCount > 0);
        }
        if (lhs.Resolved is IdentifierExpr ide) {
          if (lhsSimpleVariables.Contains(ide.Var)) {
            // syntactically forbid duplicate simple-variables on the LHS
            reporter.Error(MessageSource.Resolver, lhs, $"variable '{ide.Var.Name}' occurs more than once as left-hand side of :|");
          } else {
            lhsSimpleVariables.Add(ide.Var);
          }
        }
        // to ease in the verification of the existence check, only allow local variables as LHSs
        if (s.AssumeToken == null && !(lhs.Resolved is IdentifierExpr)) {
          reporter.Error(MessageSource.Resolver, lhs, "an assign-such-that statement (without an 'assume' clause) currently only supports local-variable LHSs");
        }
      }

      ResolveExpression(s.Expr, resolutionContext);
      ConstrainTypeExprBool(s.Expr, "type of RHS of assign-such-that statement must be boolean (got {0})");
    }

    private Expression VarDotMethod(IToken tok, string varname, string methodname) {
      return new ApplySuffix(tok, null, new ExprDotName(tok, new IdentifierExpr(tok, varname), methodname, null), new List<ActualBinding>(), tok);
    }

    private Expression makeTemp(String prefix, AssignOrReturnStmt s, ResolutionContext resolutionContext, Expression ex) {
      var temp = FreshTempVarName(prefix, resolutionContext.CodeContext);
      var locvar = new LocalVariable(s.Tok, s.Tok, temp, ex.Type, false);
      var id = new IdentifierExpr(s.Tok, temp);
      var idlist = new List<Expression>() { id };
      var lhss = new List<LocalVariable>() { locvar };
      var rhss = new List<AssignmentRhs>() { new ExprRhs(ex) };
      var up = new UpdateStmt(s.Tok, s.Tok, idlist, rhss);
      s.ResolvedStatements.Add(new VarDeclStmt(s.Tok, s.Tok, lhss, up));
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
      if (s.Rhss != null && s.Rhss.Count != 0) {
        ResolveExpression(s.Rhs, resolutionContext);
        firstType = s.Rhs.Type;
      } else if (s.Rhs is ApplySuffix asx) {
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
        ResolveExpression(s.Rhs, resolutionContext);
        firstType = s.Rhs.Type;
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
      var lhss = new List<LocalVariable>() { new LocalVariable(s.Tok, s.Tok, temp, new InferredTypeProxy(), false) };
      // "var temp ;"
      s.ResolvedStatements.Add(new VarDeclStmt(s.Tok, s.Tok, lhss, null));
      var lhss2 = new List<Expression>() { new IdentifierExpr(s.Tok, temp) };
      for (int k = (expectExtract ? 1 : 0); k < s.Lhss.Count; ++k) {
        lhss2.Add(s.Lhss[k]);
      }
      List<AssignmentRhs> rhss2 = new List<AssignmentRhs>() { new ExprRhs(s.Rhs) };
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
      UpdateStmt up = new UpdateStmt(s.Tok, s.Tok, lhss2, rhss2);
      if (expectExtract) {
        up.OriginalInitialLhs = s.Lhss.Count == 0 ? null : s.Lhss[0];
      }
      s.ResolvedStatements.Add(up);

      if (s.KeywordToken != null) {
        var notFailureExpr = new UnaryOpExpr(s.Tok, UnaryOpExpr.Opcode.Not, VarDotMethod(s.Tok, temp, "IsFailure"));
        Statement ss = null;
        if (s.KeywordToken.Token.val == "expect") {
          // "expect !temp.IsFailure(), temp"
          ss = new ExpectStmt(s.Tok, s.Tok, notFailureExpr, new IdentifierExpr(s.Tok, temp), s.KeywordToken.Attrs);
        } else if (s.KeywordToken.Token.val == "assume") {
          ss = new AssumeStmt(s.Tok, s.Tok, notFailureExpr, s.KeywordToken.Attrs);
        } else if (s.KeywordToken.Token.val == "assert") {
          ss = new AssertStmt(s.Tok, s.Tok, notFailureExpr, null, null, s.KeywordToken.Attrs);
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
          new IfStmt(s.Tok, s.Tok, false, VarDotMethod(s.Tok, temp, "IsFailure"),
            // THEN: { out := temp.PropagateFailure(); return; }
            new BlockStmt(s.Tok, s.Tok, new List<Statement>() {
              new UpdateStmt(s.Tok, s.Tok,
                new List<Expression>() { ident },
                new List<AssignmentRhs>() {new ExprRhs(VarDotMethod(s.Tok, temp, "PropagateFailure"))}
                ),
              new ReturnStmt(s.Tok, s.Tok, null),
            }),
            // ELSE: no else block
            null
          ));
      }

      if (expectExtract) {
        // "y := temp.Extract();"
        var lhs = s.Lhss[0];
        s.ResolvedStatements.Add(
          new UpdateStmt(s.Tok, s.Tok,
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

    void ResolveAlternatives(List<GuardedAlternative> alternatives, AlternativeLoopStmt loopToCatchBreaks, ResolutionContext resolutionContext) {
      Contract.Requires(alternatives != null);
      Contract.Requires(resolutionContext != null);

      // first, resolve the guards
      foreach (var alternative in alternatives) {
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(alternative.Guard, resolutionContext);
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
        ResolveAttributes(alternative, resolutionContext);
        foreach (Statement ss in alternative.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
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
    void ResolveCallStmt(CallStmt s, ResolutionContext resolutionContext, Type receiverType) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);
      bool isInitCall = receiverType != null;

      var callee = s.Method;
      Contract.Assert(callee != null);  // follows from the invariant of CallStmt
      if (!isInitCall && callee is Constructor) {
        reporter.Error(MessageSource.Resolver, s, "a constructor is allowed to be called only when an object is being allocated");
      }

      // resolve left-hand sides (the right-hand sides are resolved below)
      foreach (var lhs in s.Lhs) {
        Contract.Assume(lhs.Type != null);  // a sanity check that LHSs have already been resolved
      }

      bool tryToResolve = false;
      if (callee.Outs.Count != s.Lhs.Count) {
        if (isInitCall) {
          reporter.Error(MessageSource.Resolver, s, "a method called as an initialization method must not have any result arguments");
        } else {
          reporter.Error(MessageSource.Resolver, s, "wrong number of method result arguments (got {0}, expected {1})", s.Lhs.Count, callee.Outs.Count);
          tryToResolve = true;
        }
      } else {
        if (isInitCall) {
          if (callee.IsStatic) {
            reporter.Error(MessageSource.Resolver, s.Tok, "a method called as an initialization method must not be 'static'");
          } else {
            tryToResolve = true;
          }
        } else if (!callee.IsStatic) {
          if (!scope.AllowInstance && s.Receiver is ThisExpr) {
            // The call really needs an instance, but that instance is given as 'this', which is not
            // available in this context.  For more details, see comment in the resolution of a
            // FunctionCallExpr.
            reporter.Error(MessageSource.Resolver, s.Receiver, "'this' is not allowed in a 'static' context");
          } else if (s.Receiver is StaticReceiverExpr) {
            reporter.Error(MessageSource.Resolver, s.Receiver, "call to instance method requires an instance");
          } else {
            tryToResolve = true;
          }
        } else {
          tryToResolve = true;
        }
      }

      if (tryToResolve) {
        var typeMap = s.MethodSelect.TypeArgumentSubstitutionsAtMemberDeclaration();
        // resolve arguments
        ResolveActualParameters(s.Bindings, callee.Ins, s.Tok, callee, resolutionContext, typeMap,
          callee.IsStatic ? null : s.Receiver);
        // type check the out-parameter arguments (in-parameters were type checked as part of ResolveActualParameters)
        for (int i = 0; i < callee.Outs.Count && i < s.Lhs.Count; i++) {
          var outFormal = callee.Outs[i];
          var it = outFormal.Type;
          Type st = it.Subst(typeMap);
          var lhs = s.Lhs[i];
          var what = GetLocationInformation(outFormal, callee.Outs.Count(), i, "method out-parameter");

          AddAssignableConstraint(
            s.Tok, lhs.Type, st,
            $"incorrect return type {what} (expected {{1}}, got {{0}})");
        }
        for (int i = 0; i < s.Lhs.Count; i++) {
          var lhs = s.Lhs[i];
          // LHS must denote a mutable field.
          CheckIsLvalue(lhs.Resolved, resolutionContext);
        }

        // Resolution termination check
        ModuleDefinition callerModule = resolutionContext.CodeContext.EnclosingModule;
        ModuleDefinition calleeModule = ((ICodeContext)callee).EnclosingModule;
        if (callerModule == calleeModule) {
          // intra-module call; add edge in module's call graph
          var caller = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) as ICallable;
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
      if (Contract.Exists(callee.Decreases.Expressions, e => e is WildcardExpr) && !resolutionContext.CodeContext.AllowsNontermination) {
        reporter.Error(MessageSource.Resolver, s.Tok, "a call to a possibly non-terminating method is allowed only if the calling method is also declared (with 'decreases *') to be possibly non-terminating");
      }
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    void CheckIsLvalue(Expression lhs, ResolutionContext resolutionContext) {
      Contract.Requires(lhs != null);
      Contract.Requires(resolutionContext != null);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        if (!ll.Var.IsMutable) {
          reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable variable");
        }
      } else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        var field = ll.Member as Field;
        if (field == null || !field.IsUserMutable) {
          if (resolutionContext.InFirstPhaseConstructor && field is ConstantField cf && !cf.IsStatic && cf.Rhs == null) {
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
        ConstrainSubtypeRelation(ResolvedArrayType(ll.Seq.tok, 1, new InferredTypeProxy(), resolutionContext, true), ll.Seq.Type, ll.Seq,
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

    void ResolveBlockStatement(BlockStmt blockStmt, ResolutionContext resolutionContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(resolutionContext != null);

      if (blockStmt is DividedBlockStmt) {
        var div = (DividedBlockStmt)blockStmt;
        Contract.Assert(currentMethod is Constructor);  // divided bodies occur only in class constructors
        Contract.Assert(!resolutionContext.InFirstPhaseConstructor);  // divided bodies are never nested
        foreach (Statement ss in div.BodyInit) {
          ResolveStatementWithLabels(ss, resolutionContext with { InFirstPhaseConstructor = true });
        }
        foreach (Statement ss in div.BodyProper) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      } else {
        foreach (Statement ss in blockStmt.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      }
    }

    void ResolveStatementWithLabels(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

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
      ResolveStatement(stmt, resolutionContext);
      enclosingStatementLabels.PopMarker();
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

    Type ResolveTypeRhs(TypeRhs rr, Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (rr.Type == null) {
        if (rr.ArrayDimensions != null) {
          // ---------- new T[EE]    OR    new T[EE] (elementInit)
          Contract.Assert(rr.Bindings == null && rr.Path == null && rr.InitCall == null);
          ResolveType(stmt.Tok, rr.EType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          int i = 0;
          foreach (Expression dim in rr.ArrayDimensions) {
            Contract.Assert(dim != null);
            ResolveExpression(dim, resolutionContext);
            ConstrainToIntegerType(dim, false, string.Format("new must use an integer-based expression for the array size (got {{0}}{0})", rr.ArrayDimensions.Count == 1 ? "" : " for index " + i));
            i++;
          }
          rr.Type = ResolvedArrayType(stmt.Tok, rr.ArrayDimensions.Count, rr.EType, resolutionContext, false);
          if (rr.ElementInit != null) {
            ResolveExpression(rr.ElementInit, resolutionContext);
            // Check
            //     int^N -> rr.EType  :>  rr.ElementInit.Type
            builtIns.CreateArrowTypeDecl(rr.ArrayDimensions.Count);  // TODO: should this be done already in the parser?
            var args = new List<Type>();
            for (int ii = 0; ii < rr.ArrayDimensions.Count; ii++) {
              args.Add(builtIns.Nat());
            }
            var arrowType = new ArrowType(rr.ElementInit.tok, builtIns.ArrowTypeDecls[rr.ArrayDimensions.Count], args, rr.EType);
            var lambdaType = rr.ElementInit.Type.AsArrowType;
            if (lambdaType != null && lambdaType.TypeArgs[0] is InferredTypeProxy) {
              (lambdaType.TypeArgs[0] as InferredTypeProxy).KeepConstraints = true;
            }
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
              ResolveExpression(v, resolutionContext);
              AddAssignableConstraint(v.tok, rr.EType, v.Type, "initial value must be assignable to array's elements (expected '{0}', got '{1}')");
            }
          }
        } else {
          bool callsConstructor = false;
          if (rr.Bindings == null) {
            ResolveType(stmt.Tok, rr.EType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            var cl = (rr.EType as UserDefinedType)?.ResolvedClass as NonNullTypeDecl;
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
            var ret = ResolveTypeLenient(rr.Tok, rr.Path, resolutionContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null, true);
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
            var cl = (rr.EType as UserDefinedType)?.ResolvedClass as NonNullTypeDecl;
            if (cl == null || rr.EType.IsTraitType) {
              reporter.Error(MessageSource.Resolver, stmt, "new can be applied only to class types (got {0})", rr.EType);
            } else {
              // ---------- new C.Init(EE)
              Contract.Assert(initCallName != null);
              var prevErrorCount = reporter.Count(ErrorLevel.Error);

              // We want to create a MemberSelectExpr for the initializing method.  To do that, we create a throw-away receiver of the appropriate
              // type, create an dot-suffix expression around this receiver, and then resolve it in the usual way for dot-suffix expressions.
              var lhs = new ImplicitThisExpr_ConstructorCall(initCallTok) { Type = rr.EType };
              var callLhs = new ExprDotName(((UserDefinedType)rr.EType).tok, lhs, initCallName, ret == null ? null : ret.LastComponent.OptTypeArguments);
              ResolveDotSuffix(callLhs, true, rr.Bindings.ArgumentBindings, resolutionContext, true);
              if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
                Contract.Assert(callLhs.ResolvedExpression is MemberSelectExpr);  // since ResolveApplySuffix succeeded and call.Lhs denotes an expression (not a module or a type)
                var methodSel = (MemberSelectExpr)callLhs.ResolvedExpression;
                if (methodSel.Member is Method) {
                  rr.InitCall = new CallStmt(initCallTok, stmt.EndTok, new List<Expression>(), methodSel, rr.Bindings.ArgumentBindings);
                  ResolveCallStmt(rr.InitCall, resolutionContext, rr.EType);
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
              if (!callsConstructor && !cl.IsObjectTrait && !udt.IsArrayType && (cl.HasConstructor || cl.EnclosingModuleDefinition != currentClass.EnclosingModuleDefinition)) {
                reporter.Error(MessageSource.Resolver, stmt, "when allocating an object of {1}type '{0}', one of its constructor methods must be called", cl.Name,
                  cl.HasConstructor ? "" : "imported ");
              }
            }
          }
          rr.Type = rr.EType;
        }
      }
      return rr.Type;
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

    /// <summary>
    /// Resolve "memberName" in what currently is known as "receiverType". If "receiverType" is an unresolved
    /// proxy type, try to solve enough type constraints and use heuristics to figure out which type contains
    /// "memberName" and return that enclosing type as "tentativeReceiverType". However, try not to make
    /// type-inference decisions about "receiverType"; instead, lay down the further constraints that need to
    /// be satisfied in order for "tentativeReceiverType" to be where "memberName" is found.
    /// Consequently, if "memberName" is found and returned as a "MemberDecl", it may still be the case that
    /// "receiverType" is an unresolved proxy type and that, after solving more type constraints, "receiverType"
    /// eventually gets set to a type more specific than "tentativeReceiverType".
    /// </summary>
    MemberDecl ResolveMember(IToken tok, Type receiverType, string memberName, out NonProxyType tentativeReceiverType) {
      Contract.Requires(tok != null);
      Contract.Requires(receiverType != null);
      Contract.Requires(memberName != null);
      Contract.Ensures(Contract.Result<MemberDecl>() == null || Contract.ValueAtReturn(out tentativeReceiverType) != null);

      receiverType = PartiallyResolveTypeForMemberSelection(tok, receiverType, memberName);

      if (receiverType is TypeProxy) {
        reporter.Error(MessageSource.Resolver, tok, "type of the receiver is not fully determined at this program point", receiverType);
        tentativeReceiverType = null;
        return null;
      }
      Contract.Assert(receiverType is NonProxyType);  // there are only two kinds of types: proxies and non-proxies

      foreach (var valuet in valuetypeDecls) {
        if (valuet.IsThisType(receiverType)) {
          MemberDecl member;
          if (valuet.Members.TryGetValue(memberName, out member)) {
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
            tentativeReceiverType = (NonProxyType)receiverType;
            return member;
          }
          break;
        }
      }

      var ctype = receiverType.NormalizeExpand() as UserDefinedType;
      var cd = ctype?.AsTopLevelTypeWithMembersBypassInternalSynonym;
      if (cd != null) {
        Contract.Assert(ctype.TypeArgs.Count == cd.TypeArgs.Count);  // follows from the fact that ctype was resolved
        MemberDecl member;
        if (!classMembers[cd].TryGetValue(memberName, out member)) {
          if (memberName == "_ctor") {
            reporter.Error(MessageSource.Resolver, tok, "{0} {1} does not have an anonymous constructor", cd.WhatKind, cd.Name);
          } else {
            reporter.Error(MessageSource.Resolver, tok, "member '{0}' does not exist in {2} '{1}'", memberName, cd.Name, cd.WhatKind);
          }
        } else if (!VisibleInScope(member)) {
          reporter.Error(MessageSource.Resolver, tok, "member '{0}' has not been imported in this scope and cannot be accessed here", memberName);
        } else {
          tentativeReceiverType = ctype;
          return member;
        }
        tentativeReceiverType = null;
        return null;
      }

      reporter.Error(MessageSource.Resolver, tok, "type {0} does not have a member {1}", receiverType, memberName);
      tentativeReceiverType = null;
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
        Console.WriteLine("DEBUG: Member selection{3}:  {1} :> {0} :> {2}", t,
          Util.Comma(proxy.SupertypesKeepConstraints, su => su.ToString()),
          Util.Comma(proxy.SubtypesKeepConstraints, su => su.ToString()),
          memberName == null ? "" : " (" + memberName + ")");
      }

      // Look for a join of head symbols among the proxy's subtypes
      Type joinType = null;
      if (JoinOfAllSubtypes(proxy, ref joinType, new HashSet<TypeProxy>()) && joinType != null) {
        DetermineRootLeaf(joinType, out _, out _, out var headIsRoot, out _);
        if (joinType.IsDatatype) {
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> join is a datatype: {0}", joinType);
          }
          ConstrainSubtypeRelation(t, joinType, tok, "Member selection requires a supertype of {0} (got something more like {1})", t, joinType);
          return joinType;
        } else if (headIsRoot) {
          // we're good to go -- by picking "join" (whose type parameters have been replaced by fresh proxies), we're not losing any generality
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> improved to {0} through join", joinType);
          }
          AssignProxyAndHandleItsConstraints(proxy, joinType, true);
          return proxy.NormalizeExpand();  // we return proxy.T instead of join, in case the assignment gets hijacked
        } else if (memberName == "_#apply" || memberName == "requires" || memberName == "reads") {
          var generalArrowType = joinType.AsArrowType;  // go all the way to the base type, to get to the general arrow type, if any0
          if (generalArrowType != null) {
            // pick the supertype "generalArrowType" of "join"
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> improved to {0} through join and function application", generalArrowType);
            }
            ConstrainSubtypeRelation(generalArrowType, t, tok, "Function application requires a subtype of {0} (got something more like {1})", generalArrowType, t);
            return generalArrowType;
          }
        } else if (memberName != null) {
          // If "join" has a member called "memberName" and no supertype of "join" does, then we'll pick this join
          if (joinType.IsRefType) {
            var joinExpanded = joinType.NormalizeExpand();  // go all the way to the base type, to get to the class
            if (!joinExpanded.IsObjectQ) {
              var cl = ((UserDefinedType)joinExpanded).ResolvedClass as ClassDecl;
              if (cl != null) {
                // TODO: the following could be improved by also supplying an upper bound of the search (computed as a join of the supertypes)
                var plausibleMembers = new HashSet<MemberDecl>();
                FindAllMembers(cl, memberName, plausibleMembers);
                if (plausibleMembers.Count == 1) {
                  var mbr = plausibleMembers.First();
                  if (mbr.EnclosingClass == cl) {
                    if (DafnyOptions.O.TypeInferenceDebug) {
                      Console.WriteLine("  ----> improved to {0} through member-selection join", joinType);
                    }
                    var joinRoot = joinType.NormalizeExpand();  // blow passed any constraints
                    ConstrainSubtypeRelation(joinRoot, t, tok, "Member selection requires a subtype of {0} (got something more like {1})", joinRoot, t);
                    return joinType;
                  } else {
                    // pick the supertype "mbr.EnclosingClass" of "cl"
                    Contract.Assert(mbr.EnclosingClass is TraitDecl);  // a proper supertype of a ClassDecl must be a TraitDecl
                    var typeMapping = cl.ParentFormalTypeParametersToActuals;
                    TopLevelDecl td = mbr.EnclosingClass;
                    foreach (var tt in cl.TraitAncestors()) {
                      // If there is a match, the list of Type actuals is unique
                      // (a class cannot inherit both Trait<T1> and Trait<T2> with T1 != T2).
                      if (tt == (TraitDecl)mbr.EnclosingClass) {
                        td = tt;
                      }
                    }
                    List<Type> proxyTypeArgs = td.TypeArgs.ConvertAll(t0 => typeMapping.ContainsKey(t0) ? typeMapping[t0] : (Type)new InferredTypeProxy());
                    var joinMapping = TypeParameter.SubstitutionMap(cl.TypeArgs, joinType.TypeArgs);
                    proxyTypeArgs = proxyTypeArgs.ConvertAll(t0 => t0.Subst(joinMapping));
                    proxyTypeArgs = proxyTypeArgs.ConvertAll(t0 => t0.AsTypeParameter == null ? t0 : (Type)new InferredTypeProxy());
                    var pickItFromHere = new UserDefinedType(tok, mbr.EnclosingClass.Name, mbr.EnclosingClass, proxyTypeArgs);
                    if (DafnyOptions.O.TypeInferenceDebug) {
                      Console.WriteLine("  ----> improved to {0} through join and member lookup", pickItFromHere);
                    }
                    ConstrainSubtypeRelation(pickItFromHere, t, tok, "Member selection requires a subtype of {0} (got something more like {1})", pickItFromHere, t);
                    return pickItFromHere;
                  }
                }
              }
            }
          }
        }
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("  ----> found no improvement, because join does not determine type enough");
        }
      }

      // Compute the meet of the proxy's supertypes
      Type meet = null;
      if (MeetOfAllSupertypes(proxy, ref meet, new HashSet<TypeProxy>(), false) && meet != null) {
        // If the meet does have the member, then this looks promising. It could be that the
        // type would get further constrained later to pick some subtype (in particular, a
        // subclass that overrides the member) of this meet. But this is the best we can do
        // now.
        if (meet is TypeProxy) {
          if (proxy == meet.Normalize()) {
            // can this really ever happen?
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> found no improvement (other than the proxy itself)");
            }
            return t;
          } else {
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> (merging, then trying to improve further) assigning proxy {0}.T := {1}", proxy, meet);
            }
            Contract.Assert(proxy != meet);
            proxy.T = meet;
            Contract.Assert(t.NormalizeExpand() == meet);
            return PartiallyResolveTypeForMemberSelection(tok, t, memberName, strength + 1);
          }
        }
        if (!(meet is ArtificialType)) {
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> improved to {0} through meet", meet);
          }
          if (memberName != null) {
            AssignProxyAndHandleItsConstraints(proxy, meet, true);
            return proxy.NormalizeExpand(); // we return proxy.T instead of meet, in case the assignment gets hijacked
          } else {
            return meet;
          }
        }
      }

      // as a last resort, act on any artificial type nearby the proxy
      var artificialSuper = proxy.InClusterOfArtificial(AllXConstraints);
      if (artificialSuper != null) {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("  ----> use artificial supertype: {0}", artificialSuper);
        }
        return artificialSuper;
      }

      // we weren't able to do it
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("  ----> found no improvement using simple things, trying harder once more");
      }
      return PartiallyResolveTypeForMemberSelection(tok, t, memberName, strength + 1);
    }

    private Type/*?*/ GetBaseTypeFromProxy(TypeProxy proxy, Dictionary<TypeProxy, Type/*?*/> determinedProxies) {
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
      cl.ParentTraitHeads.ForEach(trait => FindAllMembers(trait, memberName, foundSoFar));
    }

    /// <summary>
    /// Attempts to compute the join of "join", "t", and all of "t"'s known subtype( constraint)s.  The join
    /// ignores type parameters.  It is assumed that "join" on entry already includes the join of all proxies
    /// in "visited". The empty join is represented by "null".
    /// The return is "true" if the join exists.
    /// </summary>
    bool JoinOfAllSubtypes(Type t, ref Type joinType, ISet<TypeProxy> visited) {
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
          if (!JoinOfAllSubtypes(s, ref joinType, visited)) {
            return false;
          }
        }
        if (joinType == null) {
          // also consider "Assignable" constraints
          foreach (var c in AllXConstraints) {
            if (c.ConstraintName == "Assignable" && c.Types[0].Normalize() == proxy) {
              var s = c.Types[1].NormalizeExpandKeepConstraints();
              if (!JoinOfAllSubtypes(s, ref joinType, visited)) {
                return false;
              }
            }
          }
        }
        return true;
      }

      if (joinType == null) {
        // stick with what we've got
        joinType = t;
        return true;
      } else if (Type.IsHeadSupertypeOf(joinType, t)) {
        // stick with what we've got
        return true;
      } else if (Type.IsHeadSupertypeOf(t, joinType)) {
        joinType = Type.HeadWithProxyArgs(t);
        return true;
      } else {
        joinType = Type.Join(joinType, Type.HeadWithProxyArgs(t), builtIns);  // the only way this can succeed is if we obtain a (non-null or nullable) trait
        Contract.Assert(joinType == null ||
                        joinType.IsObjectQ || joinType.IsObject ||
                        (joinType is UserDefinedType udt && (udt.ResolvedClass is TraitDecl || (udt.ResolvedClass is NonNullTypeDecl nntd && nntd.Class is TraitDecl))));
        return joinType != null;
      }
    }

    /// <summary>
    /// Attempts to compute the meet of "meet", all of "t"'s known supertype( constraint)s, and, if "includeT"
    /// and "t" has no supertype( constraint)s, "t".
    /// The meet ignores type parameters. (Really?? --KRML)
    /// It is assumed that "meet" on entry already includes the meet of all proxies
    /// in "visited". The empty meet is represented by "null".
    /// The return is "true" if the meet exists.
    /// </summary>
    bool MeetOfAllSupertypes(Type t, ref Type meet, ISet<TypeProxy> visited, bool includeT) {
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
          if (!MeetOfAllSupertypes(s, ref meet, visited, true)) {
            return false;
          }
        }
        if (!delegatedToOthers) {
          // also consider "Assignable" constraints
          foreach (var c in AllXConstraints) {
            if (c.ConstraintName == "Assignable" && c.Types[1].Normalize() == proxy) {
              var s = c.Types[0].NormalizeExpandKeepConstraints();
              delegatedToOthers = true;
              if (!MeetOfAllSupertypes(s, ref meet, visited, true)) {
                return false;
              }
            }
          }
        }
        if (delegatedToOthers) {
          return true;
        } else if (!includeT) {
          return true;
        } else if (meet == null || meet.Normalize() == proxy) {
          meet = proxy;
          return true;
        } else {
          return false;
        }
      }

      if (meet == null) {
        meet = Type.HeadWithProxyArgs(t);
        return true;
      } else if (Type.IsHeadSupertypeOf(t, meet)) {
        // stick with what we've got
        return true;
      } else if (Type.IsHeadSupertypeOf(meet, t)) {
        meet = Type.HeadWithProxyArgs(t);
        return true;
      } else {
        meet = Type.Meet(meet, Type.HeadWithProxyArgs(t), builtIns);
        return meet != null;
      }
    }

    /// <summary>
    /// Check that the type uses formal type parameters in a way that is agreeable with their variance specifications.
    /// "context == Co" says that "type" is allowed to vary in the positive direction.
    /// "context == Contra" says that "type" is allowed to vary in the negative direction.
    /// "context == Non" says that "type" must not vary at all.
    /// * "lax" says that the context is not strict -- type parameters declared to be strict must not be used in a lax context
    /// </summary>
    public void CheckVariance(Type type, ICallable enclosingTypeDefinition, TypeParameter.TPVariance context, bool lax) {
      Contract.Requires(type != null);
      Contract.Requires(enclosingTypeDefinition != null);

      type = type.Normalize();  // we keep constraints, since subset types have their own type-parameter variance specifications; we also keep synonys, since that gives rise to better error messages
      if (type is BasicType) {
        // fine
      } else if (type is MapType) {
        var t = (MapType)type;
        // If its an infinite map, the domain's context is lax
        CheckVariance(t.Domain, enclosingTypeDefinition, context, lax || !t.Finite);
        CheckVariance(t.Range, enclosingTypeDefinition, context, lax);
      } else if (type is SetType) {
        var t = (SetType)type;
        // If its an infinite set, the argument's context is lax
        CheckVariance(t.Arg, enclosingTypeDefinition, context, lax || !t.Finite);
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        CheckVariance(t.Arg, enclosingTypeDefinition, context, lax);
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedClass is TypeParameter tp) {
          if (tp.Variance != TypeParameter.TPVariance.Non && tp.Variance != context) {
            reporter.Error(MessageSource.Resolver, t.tok, "formal type parameter '{0}' is not used according to its variance specification", tp.Name);
          } else if (tp.StrictVariance && lax) {
            string hint;
            if (tp.VarianceSyntax == TypeParameter.TPVarianceSyntax.NonVariant_Strict) {
              hint = string.Format(" (perhaps try declaring '{0}' as '-{0}' or '!{0}')", tp.Name);
            } else {
              Contract.Assert(tp.VarianceSyntax == TypeParameter.TPVarianceSyntax.Covariant_Strict);
              hint = string.Format(" (perhaps try changing the declaration from '+{0}' to '*{0}')", tp.Name);
            }
            reporter.Error(MessageSource.Resolver, t.tok, "formal type parameter '{0}' is not used according to its variance specification (it is used left of an arrow){1}", tp.Name, hint);
          }
        } else {
          var resolvedClass = t.ResolvedClass;
          Contract.Assert(resolvedClass != null);  // follows from that the given type was successfully resolved
          Contract.Assert(resolvedClass.TypeArgs.Count == t.TypeArgs.Count);
          if (lax) {
            // we have to be careful about uses of the type being defined
            var cg = enclosingTypeDefinition.EnclosingModule.CallGraph;
            var t0 = resolvedClass as ICallable;
            if (t0 != null && cg.GetSCCRepresentative(t0) == cg.GetSCCRepresentative(enclosingTypeDefinition)) {
              reporter.Error(MessageSource.Resolver, t.tok, "using the type being defined ('{0}') here would cause a logical inconsistency by defining a type whose cardinality exceeds itself (like the Continuum Transfunctioner, you might say its power would then be exceeded only by its mystery)", resolvedClass.Name);
            }
          }
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            Type p = t.TypeArgs[i];
            var tpFormal = resolvedClass.TypeArgs[i];
            CheckVariance(p, enclosingTypeDefinition,
              context == TypeParameter.TPVariance.Non ? context :
              context == TypeParameter.TPVariance.Co ? tpFormal.Variance :
              TypeParameter.Negate(tpFormal.Variance),
              lax || !tpFormal.StrictVariance);
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

      if (cl is ClassDecl cls && cls.NonNullTypeDecl != null) {
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

    /// <summary>
    /// "IsTwoState" implies that "old" and "fresh" expressions are allowed.
    /// </summary>
    public void ResolveExpression(Expression expr, ResolutionContext resolutionContext) {

#if TEST_TYPE_SYNONYM_TRANSPARENCY
      ResolveExpressionX(expr, resolutionContext);
      // For testing purposes, change the type of "expr" to a type synonym (mwo-ha-ha-ha!)
      var t = expr.Type;
      Contract.Assert(t != null);
      var sd = new TypeSynonymDecl(expr.tok, "type#synonym#transparency#test", new TypeParameter.TypeParameterCharacteristics(false),
        new List<TypeParameter>(), resolutionContext.CodeContext.EnclosingModule, t, null);
      var ts = new UserDefinedType(expr.tok, "type#synonym#transparency#test", sd, new List<Type>(), null);
      expr.DebugTest_ChangeType(ts);
    }
    public void ResolveExpressionX(Expression expr, ResolutionContext resolutionContext) {
#endif
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(expr.Type != null);
      if (expr.Type != null) {
        // expression has already been resolved
        return;
      }

      // The following cases will resolve the subexpressions and will attempt to assign a type of expr.  However, if errors occur
      // and it cannot be determined what the type of expr is, then it is fine to leave expr.Type as null.  In that case, the end
      // of this method will assign proxy type to the expression, which reduces the number of error messages that are produced
      // while type checking the rest of the program.

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.Type = e.E.Type;
        AddXConstraint(e.E.tok, "NumericOrBitvector", e.E.Type, "type of unary - must be of a numeric or bitvector type (instead got {0})");
        // Note, e.ResolvedExpression will be filled in during CheckTypeInference, at which time e.Type has been determined

      } else if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;

        if (e is StaticReceiverExpr) {
          StaticReceiverExpr eStatic = (StaticReceiverExpr)e;
          this.ResolveType(eStatic.tok, eStatic.UnresolvedType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          eStatic.Type = eStatic.UnresolvedType;
        } else {
          if (e.Value == null) {
            e.Type = new InferredTypeProxy();
            AddXConstraint(e.tok, "IsNullableRefType", e.Type, "type of 'null' is a reference type, but it is used as {0}");
          } else if (e.Value is BigInteger) {
            var proxy = new InferredTypeProxy();
            e.Type = proxy;
            ConstrainSubtypeRelation(new IntVarietiesSupertype(), e.Type, e.tok, "integer literal used as if it had type {0}", e.Type);
          } else if (e.Value is BaseTypes.BigDec) {
            var proxy = new InferredTypeProxy();
            e.Type = proxy;
            ConstrainSubtypeRelation(new RealVarietiesSupertype(), e.Type, e.tok, "type of real literal is used as {0}", e.Type);
          } else if (e.Value is bool) {
            e.Type = Type.Bool;
          } else if (e is CharLiteralExpr) {
            e.Type = Type.Char;
          } else if (e is StringLiteralExpr) {
            e.Type = Type.String();
            ResolveType(e.tok, e.Type, resolutionContext, ResolveTypeOptionEnum.DontInfer, null);
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
          if (currentClass == null) {
            Contract.Assert(reporter.HasErrors);
          } else {
            expr.Type = GetThisType(expr.tok, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting
          }
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
          ResolveDatatypeValue(resolutionContext, dtv, (DatatypeDecl)d, null);
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Type elementType = new InferredTypeProxy() { KeepConstraints = true };
        foreach (Expression ee in e.Elements) {
          ResolveExpression(ee, resolutionContext);
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
          ResolveExpression(p.A, resolutionContext);
          Contract.Assert(p.A.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(domainType, p.A.Type, p.A.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.A.Type, domainType);
          ResolveExpression(p.B, resolutionContext);
          Contract.Assert(p.B.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(rangeType, p.B.Type, p.B.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.B.Type, rangeType);
        }
        expr.Type = new MapType(e.Finite, domainType, rangeType);
      } else if (expr is NameSegment) {
        var e = (NameSegment)expr;
        ResolveNameSegment(e, true, null, resolutionContext, false);

        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of type ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        ResolveDotSuffix(e, true, null, resolutionContext, false);
        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of type ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        ResolveApplySuffix(e, resolutionContext, false);

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        ResolveExpression(e.Obj, resolutionContext);
        Contract.Assert(e.Obj.Type != null);  // follows from postcondition of ResolveExpression
        NonProxyType tentativeReceiverType;
        var member = ResolveMember(expr.tok, e.Obj.Type, e.MemberName, out tentativeReceiverType);
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (member is Function) {
          var fn = member as Function;
          e.Member = fn;
          if (fn is TwoStateFunction && !resolutionContext.IsTwoState) {
            reporter.Error(MessageSource.Resolver, e.tok, "a two-state function can be used only in a two-state context");
          }
          // build the type substitution map
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          Dictionary<TypeParameter, Type> subst;
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            subst = new Dictionary<TypeParameter, Type>();
          } else {
            subst = TypeParameter.SubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
          }
          foreach (var tp in fn.TypeArgs) {
            Type prox = new InferredTypeProxy();
            subst[tp] = prox;
            e.TypeApplication_JustMember.Add(prox);
          }
          subst = BuildTypeArgumentSubstitute(subst);
          e.Type = SelectAppropriateArrowType(fn.tok,
            fn.Formals.ConvertAll(f => f.Type.Subst(subst)),
            fn.ResultType.Subst(subst),
            fn.Reads.Count != 0, fn.Req.Count != 0);
          AddCallGraphEdge(resolutionContext.CodeContext, fn, e, false);
        } else if (member is Field) {
          var field = (Field)member;
          e.Member = field;
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          if (e.Obj is StaticReceiverExpr && !field.IsStatic) {
            reporter.Error(MessageSource.Resolver, expr, "a field must be selected via an object, not just a class name");
          }
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            e.Type = field.Type;
          } else {
            Contract.Assert(ctype.ResolvedClass != null); // follows from postcondition of ResolveMember
            // build the type substitution map
            var subst = TypeParameter.SubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            e.Type = field.Type.Subst(subst);
          }
          AddCallGraphEdgeForField(resolutionContext.CodeContext, field, e);
        } else {
          reporter.Error(MessageSource.Resolver, expr, "member {0} in type {1} does not refer to a field or a function", e.MemberName, tentativeReceiverType);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        ResolveSeqSelectExpr(e, resolutionContext);

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, resolutionContext);
        Contract.Assert(e.Array.Type != null);  // follows from postcondition of ResolveExpression
        Contract.Assert(e.Array.Type.TypeArgs != null);  // if it is null, should make a 1-element list with a Proxy
        Type elementType = e.Array.Type.TypeArgs.Count > 0 ?
          e.Array.Type.TypeArgs[0] :
          new InferredTypeProxy();
        ConstrainSubtypeRelation(ResolvedArrayType(e.Array.tok, e.Indices.Count, elementType, resolutionContext, true), e.Array.Type, e.Array,
          "array selection requires an array{0} (got {1})", e.Indices.Count, e.Array.Type);
        int i = 0;
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          ResolveExpression(idx, resolutionContext);
          Contract.Assert(idx.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainToIntegerType(idx, true, "array selection requires integer- or bitvector-based numeric indices (got {0} for index " + i + ")");
          i++;
        }
        e.Type = elementType;

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        ResolveExpression(e.Seq, resolutionContext);
        Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Index, resolutionContext);
        ResolveExpression(e.Value, resolutionContext);
        AddXConstraint(expr.tok, "SeqUpdatable", e.Seq.Type, e.Index, e.Value, "update requires a sequence, map, or multiset (got {0})");
        expr.Type = new InferredTypeProxy(); // drop type constraints
        ConstrainSubtypeRelation(
          super: expr.Type, sub: e.Seq.Type, // expr.Type generalizes e.Seq.Type by dropping constraints
          exprForToken: expr,
          msg: "Update expression used with type '{0}'", e.Seq.Type);
      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        ResolveExpression(e.Root, resolutionContext);
        var ty = PartiallyResolveTypeForMemberSelection(expr.tok, e.Root.Type);
        if (!ty.IsDatatype) {
          reporter.Error(MessageSource.Resolver, expr, "datatype update expression requires a root expression of a datatype (got {0})", ty);
        } else {
          var (ghostLet, compiledLet) = ResolveDatatypeUpdate(expr.tok, e.Root, ty.AsDatatype, e.Updates, resolutionContext,
            out var members, out var legalSourceConstructors);
          Contract.Assert((ghostLet == null) == (compiledLet == null));
          if (ghostLet != null) {
            e.ResolvedExpression = ghostLet; // this might be replaced by e.ResolvedCompiledExpression in CheckIsCompilable
            e.ResolvedCompiledExpression = compiledLet;
            e.Members = members;
            e.LegalSourceConstructors = legalSourceConstructors;
            expr.Type = ghostLet.Type;
          }
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, resolutionContext);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        ResolveExpression(e.Function, resolutionContext);
        foreach (var arg in e.Args) {
          ResolveExpression(arg, resolutionContext);
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
        var elementType = e.ExplicitElementType ?? new InferredTypeProxy();
        ResolveType(e.tok, elementType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        ResolveExpression(e.N, resolutionContext);
        ConstrainToIntegerType(e.N, false, "sequence construction must use an integer-based expression for the sequence size (got {0})");
        ResolveExpression(e.Initializer, resolutionContext);
        var arrowType = new ArrowType(e.tok, builtIns.ArrowTypeDecls[1], new List<Type>() { builtIns.Nat() }, elementType);
        var hintString = " (perhaps write '_ =>' in front of the expression you gave in order to make it an arrow type)";
        ConstrainSubtypeRelation(arrowType, e.Initializer.Type, e.Initializer, "sequence-construction initializer expression expected to have type '{0}' (instead got '{1}'){2}",
          arrowType, e.Initializer.Type, new LazyString_OnTypeEquals(elementType, e.Initializer.Type, hintString));
        expr.Type = new SeqType(elementType);

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var elementType = new InferredTypeProxy();
        AddXConstraint(e.E.tok, "MultiSetConvertible", e.E.Type, elementType, "can only form a multiset from a seq or set (got {0})");
        expr.Type = new MultiSetType(elementType);

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "old", resolutionContext);
        ResolveExpression(e.E, new ResolutionContext(resolutionContext.CodeContext, false) with { InOld = true });
        expr.Type = e.E.Type;

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "unchanged", resolutionContext);
        foreach (var fe in e.Frame) {
          ResolveFrameExpression(fe, FrameExpressionUse.Unchanged, resolutionContext);
        }
        expr.Type = Type.Bool;

      } else if (expr is FreshExpr) {
        var e = (FreshExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "fresh", resolutionContext);
        // the type of e.E must be either an object or a set/seq of objects
        AddXConstraint(expr.tok, "Freshable", e.E.Type, "the argument of a fresh expression must denote an object or a set or sequence of objects (instead got {0})");
        expr.Type = Type.Bool;

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        ResolveExpression(e.E, resolutionContext);
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
          case UnaryOpExpr.Opcode.Allocated:
            // the argument is allowed to have any type at all
            expr.Type = Type.Bool;
            if (2 <= DafnyOptions.O.Allocated &&
              ((resolutionContext.CodeContext is Function && !resolutionContext.InOld) || resolutionContext.CodeContext is ConstantField || CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl)) {
              var declKind = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl redir ? redir.WhatKind : ((MemberDecl)resolutionContext.CodeContext).WhatKind;
              reporter.Error(MessageSource.Resolver, expr, "a {0} definition is not allowed to depend on the set of allocated references", declKind);
            }
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }

        // We do not have enough information to compute `e.ResolvedOp` yet.
        // For binary operators the computation happens in `CheckTypeInference`.
        // For unary operators it happens lazily in the getter of `e.ResolvedOp`.
      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(e.tok, e.ToType, resolutionContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          if (e.ToType.IsNumericBased(Type.NumericPersuasion.Int)) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a real-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsBitVectorType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a bitvector-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsCharType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a char type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsBigOrdinalType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to an ORDINAL type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsRefType) {
            AddAssignableConstraint(expr.tok, e.ToType, e.E.Type, "type cast to reference type '{0}' must be from an expression assignable to it (got '{1}')");
          } else {
            reporter.Error(MessageSource.Resolver, expr, "type conversions are not supported to this type (got {0})", e.ToType);
          }
          e.Type = e.ToType;
        } else {
          e.Type = new InferredTypeProxy();
        }

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(e.tok, e.ToType, resolutionContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        AddAssignableConstraint(expr.tok, e.ToType, e.E.Type, "type test for type '{0}' must be from an expression assignable to it (got '{1}')");
        e.Type = Type.Bool;

      } else if (expr is BinaryExpr) {

        BinaryExpr e = (BinaryExpr)expr;
        ResolveExpression(e.E0, resolutionContext);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.E1, resolutionContext);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression

        switch (e.Op) {
          case BinaryExpr.Opcode.Iff:
          case BinaryExpr.Opcode.Imp:
          case BinaryExpr.Opcode.Exp:
          case BinaryExpr.Opcode.And:
          case BinaryExpr.Opcode.Or: {
              ConstrainSubtypeRelation(Type.Bool, e.E0.Type, expr, "first argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
              var secondArgumentDescription = e.E1.tok is QuantifiedVariableRangeToken
                ? "range of quantified variable" : "second argument to {0}";
              ConstrainSubtypeRelation(Type.Bool, e.E1.Type, expr, secondArgumentDescription + " must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E1.Type);
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
            AddXConstraint(expr.tok, "Disjointable", disjointArgumentsType, "arguments must be of a set or multiset type (got {0})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le: {
              if (e.Op == BinaryExpr.Opcode.Lt && (PartiallyResolveTypeForMemberSelection(e.E0.tok, e.E0.Type).IsIndDatatype || e.E0.Type.IsTypeParameter || PartiallyResolveTypeForMemberSelection(e.E1.tok, e.E1.Type).IsIndDatatype)) {
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
              if (e.Op == BinaryExpr.Opcode.Gt && (PartiallyResolveTypeForMemberSelection(e.E0.tok, e.E0.Type).IsIndDatatype || PartiallyResolveTypeForMemberSelection(e.E1.tok, e.E1.Type).IsIndDatatype || e.E1.Type.IsTypeParameter)) {
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
              AddXConstraint(e.tok, "Plussable", expr.Type, "type of + must be of a numeric type, a bitvector type, ORDINAL, char, a sequence type, or a set-like or map-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to + ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to + ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.Sub: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Minusable", expr.Type, "type of - must be of a numeric type, bitvector type, ORDINAL, char, or a set-like or map-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to - ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              // The following handles map subtraction, but does not in an unfortunately restrictive way.
              // First, it would be nice to delay the decision of it this is a map subtraction or not. This settles
              // for the simple way to decide based on what is currently known about the result type, which is also
              // done, for example, when deciding if "<" denotes rank ordering on datatypes.
              // Second, for map subtraction, it would be nice to allow the right-hand operand to be either a set or
              // an iset. That would also lead to further complexity in the code, so this code restricts the right-hand
              // operand to be a set.
              var eType = PartiallyResolveTypeForMemberSelection(expr.tok, expr.Type).AsMapType;
              if (eType != null) {
                // allow "map - set == map"
                var expected = new SetType(true, eType.Domain);
                ConstrainSubtypeRelation(expected, e.E1.Type, expr.tok, "map subtraction expects right-hand operand to have type {0} (instead got {1})", expected, e.E1.Type);
              } else {
                ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to - ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
              }
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
            var subjectDescription = e.E1.tok is QuantifiedVariableDomainToken
              ? "domain of quantified variable" : "second argument to \"" + BinaryExpr.OpcodeString(e.Op) + "\"";
            AddXConstraint(expr.tok, "Innable", e.E1.Type, e.E0.Type, subjectDescription + " must be a set, multiset, or sequence with elements of type {1}, or a map with domain {1} (instead got {0})");
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
        ResolveExpression(e.E0, resolutionContext);
        ResolveExpression(e.E1, resolutionContext);
        ResolveExpression(e.E2, resolutionContext);
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
            ResolveExpression(rhs, resolutionContext);
          }
          scope.PushMarker();
          if (e.LHSs.Count != e.RHSs.Count) {
            reporter.Error(MessageSource.Resolver, expr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, rhsType, resolutionContext);
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
            ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            AddTypeDependencyEdges(resolutionContext.CodeContext, v.Type);
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, resolutionContext);
            ConstrainTypeExprBool(rhs, "type of RHS of let-such-that expression must be boolean (got {0})");
          }
        }
        ResolveExpression(e.Body, resolutionContext);
        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = e.Body.Type;
      } else if (expr is LetOrFailExpr) {
        var e = (LetOrFailExpr)expr;
        ResolveLetOrFailExpr(e, resolutionContext);
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (resolutionContext.CodeContext is Function) {
          ((Function)resolutionContext.CodeContext).ContainsQuantifier = true;
        }
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          var option = new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies);
          ResolveType(v.tok, v.Type, resolutionContext, option, null);
        }
        if (e.Range != null) {
          ResolveExpression(e.Range, resolutionContext);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.Range, "range of quantifier must be of type bool (instead got {0})");
        }
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Term, "body of quantifier must be of type bool (instead got {0})");
        // Since the body is more likely to infer the types of the bound variables, resolve it
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = Type.Bool;

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, resolutionContext);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = new SetType(e.Finite, e.Term.Type);

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        Contract.Assert(e.BoundVars.Count == 1 || (1 < e.BoundVars.Count && e.TermLeft != null));
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, resolutionContext);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        if (e.TermLeft != null) {
          ResolveExpression(e.TermLeft, resolutionContext);
          Contract.Assert(e.TermLeft.Type != null);  // follows from postcondition of ResolveExpression
        }
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = new MapType(e.Finite, e.TermLeft != null ? e.TermLeft.Type : e.BoundVars[0].Type, e.Term.Type);

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }

        if (e.Range != null) {
          ResolveExpression(e.Range, resolutionContext);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.Range, "Precondition must be boolean (got {0})");
        }
        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, FrameExpressionUse.Reads, resolutionContext);
        }
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);
        scope.PopMarker();
        expr.Type = SelectAppropriateArrowType(e.tok, e.BoundVars.ConvertAll(v => v.Type), e.Body.Type, e.Reads.Count != 0, e.Range != null);
      } else if (expr is WildcardExpr) {
        expr.Type = new SetType(true, builtIns.ObjectQ());
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);

        ResolveStatement(e.S, resolutionContext);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var r = e.S as UpdateStmt;
          if (r != null && r.ResolvedStatements.Count == 1) {
            var call = r.ResolvedStatements[0] as CallStmt;
            if (call.Method is TwoStateLemma && !resolutionContext.IsTwoState) {
              reporter.Error(MessageSource.Resolver, call, "two-state lemmas can only be used in two-state contexts");
            }
          }
        }

        ResolveExpression(e.E, resolutionContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        expr.Type = e.E.Type;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        ResolveExpression(e.Test, resolutionContext);
        Contract.Assert(e.Test.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Thn, resolutionContext);
        Contract.Assert(e.Thn.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Els, resolutionContext);
        Contract.Assert(e.Els.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Test, "guard condition in if-then-else expression must be a boolean (instead got {0})");
        expr.Type = new InferredTypeProxy();
        ConstrainSubtypeRelation(expr.Type, e.Thn.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);
        ConstrainSubtypeRelation(expr.Type, e.Els.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);

      } else if (expr is MatchExpr) {
        ResolveMatchExpr((MatchExpr)expr, resolutionContext);
      } else if (expr is NestedMatchExpr) {
        NestedMatchExpr e = (NestedMatchExpr)expr;
        ResolveNestedMatchExpr(e, resolutionContext);
        if (e.ResolvedExpression != null && e.ResolvedExpression.Type != null) {
          // i.e. no error was thrown during compiling of the NextedMatchExpr or during resolution of the ResolvedExpression
          expr.Type = e.ResolvedExpression.Type;
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (expr.Type == null) {
        // some resolution error occurred
        expr.Type = new InferredTypeProxy();
      }
    }

    Label/*?*/ ResolveDominatingLabelInExpr(IToken tok, string/*?*/ labelName, string expressionDescription, ResolutionContext resolutionContext) {
      Contract.Requires(tok != null);
      Contract.Requires(expressionDescription != null);
      Contract.Requires(resolutionContext != null);

      Label label = null;
      if (!resolutionContext.IsTwoState) {
        reporter.Error(MessageSource.Resolver, tok, $"{expressionDescription} expressions are not allowed in this context");
      } else if (labelName != null) {
        label = dominatingStatementLabels.Find(labelName);
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
    /// See ConstrainToIntegerType description for the overload above.
    /// </summary>
    void ConstrainToIntegerType(IToken tok, Type type, bool allowBitVector, TypeConstraint.ErrorMsg errorMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(errorMsg != null);
      // We do two constraints: the first can aid in determining types, but allows bit-vectors; the second excludes bit-vectors.
      // However, we reuse the error message, so that only one error gets reported.
      ConstrainSubtypeRelation(new IntVarietiesSupertype(), type, errorMsg);
      if (!allowBitVector) {
        AddXConstraint(tok, "IntegerType", type, errorMsg);
      }
    }

    void EagerAddAssignableConstraint(IToken tok, Type lhs, Type rhs, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsgFormat != null);
      var lhsNormalized = lhs.Normalize();
      var rhsNormalized = rhs.Normalize();
      if (lhsNormalized is TypeProxy lhsProxy && !(rhsNormalized is TypeProxy)) {
        Contract.Assert(lhsProxy.T == null); // otherwise, lhs.Normalize() above would have kept on going
        AssignProxyAndHandleItsConstraints(lhsProxy, rhsNormalized, true);
      } else {
        AddAssignableConstraint(tok, lhs, rhs, errMsgFormat);
      }
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
    ///
    /// Actually, the method returns two expressions (or returns "(null, null)"). The first expression is the desugaring to be
    /// used when the DatatypeUpdateExpr is used in a ghost context. The second is to be used for a compiled context. In either
    /// case, "legalSourceConstructors" contains both ghost and compiled constructors.
    ///
    /// The reason for computing both desugarings here is that it's too early to tell if the DatatypeUpdateExpr is being used in
    /// a ghost or compiled context. This is a consequence of doing the deguaring so early. But it's also convenient to do the
    /// desugaring during resolution, because then the desugaring can be constructed as a non-resolved expression on which ResolveExpression
    /// is called--this is easier than constructing an already-resolved expression.
    /// </summary>
    (Expression, Expression) ResolveDatatypeUpdate(IToken tok, Expression root, DatatypeDecl dt, List<Tuple<IToken, string, Expression>> memberUpdates,
      ResolutionContext resolutionContext, out List<MemberDecl> members, out List<DatatypeCtor> legalSourceConstructors) {
      Contract.Requires(tok != null);
      Contract.Requires(root != null);
      Contract.Requires(dt != null);
      Contract.Requires(memberUpdates != null);
      Contract.Requires(resolutionContext != null);

      legalSourceConstructors = null;
      members = new List<MemberDecl>();

      // First, compute the list of candidate result constructors, that is, the constructors
      // that have all of the mentioned destructors. Issue errors for duplicated names and for
      // names that are not destructors in the datatype.
      var candidateResultCtors = dt.Ctors;  // list of constructors that have all the so-far-mentioned destructors
      var memberNames = new HashSet<string>();
      var rhsBindings = new Dictionary<string, Tuple<BoundVar/*let variable*/, IdentifierExpr/*id expr for let variable*/, Expression /*RHS in given syntax*/>>();
      var subst = TypeParameter.SubstitutionMap(dt.TypeArgs, root.Type.NormalizeExpand().TypeArgs);
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
            members.Add(member);
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
                var xName = FreshTempVarName(string.Format("dt_update#{0}#", destructor_str), resolutionContext.CodeContext);
                var xVar = new BoundVar(new AutoGeneratedToken(tok), xName, destructor.Type.Subst(subst));
                var x = new IdentifierExpr(new AutoGeneratedToken(tok), xVar);
                rhsBindings.Add(destructor_str, new Tuple<BoundVar, IdentifierExpr, Expression>(xVar, x, entry.Item3));
              }
            }
          }
        }
      }
      if (candidateResultCtors.Count == 0) {
        return (null, null);
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
        return (null, null);
      }

      // The legal source constructors are the candidate result constructors. (Yep, two names for the same thing.)
      legalSourceConstructors = candidateResultCtors;
      Contract.Assert(1 <= legalSourceConstructors.Count);

      var desugaringForGhostContext = DesugarDatatypeUpdate(tok, root, dt, candidateResultCtors, rhsBindings, resolutionContext);
      var nonGhostConstructors = candidateResultCtors.Where(ctor => !ctor.IsGhost).ToList();
      if (nonGhostConstructors.Count == candidateResultCtors.Count) {
        return (desugaringForGhostContext, desugaringForGhostContext);
      }
      var desugaringForCompiledContext = DesugarDatatypeUpdate(tok, root, dt, nonGhostConstructors, rhsBindings, resolutionContext);
      return (desugaringForGhostContext, desugaringForCompiledContext);
    }

    /// <summary>
    // Rewrite the datatype update root.(x := X, y := Y, ...) to:
    ///     var d := root;
    ///     var x := X;  // EXCEPT: don't do this for ghost fields
    ///     var y := Y;
    ///     ..
    ///     if d.CandidateResultConstructor0 then
    ///       CandidateResultConstructor0(x, y, ..., d.f0, d.f1, ...)  // for a ghost field x, use the expression X directly
    ///     else if d.CandidateResultConstructor1 then
    ///       CandidateResultConstructor0(x, y, ..., d.g0, d.g1, ...)
    ///     ...
    ///     else
    ///       CandidateResultConstructorN(x, y, ..., d.k0, d.k1, ...)
    /// </summary>
    private Expression DesugarDatatypeUpdate(IToken tok, Expression root, DatatypeDecl dt, List<DatatypeCtor> candidateResultCtors,
      Dictionary<string, Tuple<BoundVar, IdentifierExpr, Expression>> rhsBindings, ResolutionContext resolutionContext) {

      if (candidateResultCtors.Count == 0) {
        return root;
      }
      Expression rewrite = null;
      // Create a unique name for d', the variable we introduce in the let expression
      var dName = FreshTempVarName("dt_update_tmp#", resolutionContext.CodeContext);
      var dVar = new BoundVar(new AutoGeneratedToken(tok), dName, root.Type);
      var d = new IdentifierExpr(new AutoGeneratedToken(tok), dVar);
      Expression body = null;
      candidateResultCtors.Reverse();
      foreach (var crc in candidateResultCtors) {
        // Build the arguments to the datatype constructor, using the updated value in the appropriate slot
        var ctorArguments = new List<Expression>();
        var actualBindings = new List<ActualBinding>();
        foreach (var f in crc.Formals) {
          Expression ctorArg;
          if (rhsBindings.TryGetValue(f.Name, out var info)) {
            ctorArg = info.Item2 ?? info.Item3;
          } else {
            ctorArg = new ExprDotName(tok, d, f.Name, null);
          }
          ctorArguments.Add(ctorArg);
          var bindingName = new Token(tok.line, tok.col) {
            Filename = tok.Filename,
            val = f.Name
          };
          actualBindings.Add(new ActualBinding(bindingName, ctorArg));
        }
        var ctor_call = new DatatypeValue(tok, crc.EnclosingDatatype.Name, crc.Name, actualBindings);
        // in the following line, resolve to root.Type, so that type parameters get filled in appropriately
        ResolveDatatypeValue(resolutionContext, ctor_call, dt, root.Type.NormalizeExpand());

        if (body == null) {
          body = ctor_call;
        } else {
          // body = if d.crc? then ctor_call else body
          var guard = new ExprDotName(tok, d, crc.QueryField.Name, null);
          body = new ITEExpr(tok, false, guard, ctor_call, body);
        }
      }
      Contract.Assert(body != null); // because there was at least one element in candidateResultCtors

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
      ResolveExpression(rewrite, resolutionContext);
      return rewrite;
    }

    /// <summary>
    /// Resolves a NestedMatchExpr by
    /// 1 - checking that all of its patterns are linear
    /// 2 - desugaring it into a decision tree of MatchExpr and ITEEXpr (for constant matching)
    /// 3 - resolving the generated (sub)expression.
    /// </summary>
    void ResolveNestedMatchExpr(NestedMatchExpr me, ResolutionContext resolutionContext) {
      Contract.Requires(me != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(me.ResolvedExpression == null);

      bool debug = DafnyOptions.O.MatchCompilerDebug;

      ResolveExpression(me.Source, resolutionContext);
      Contract.Assert(me.Source.Type != null);  // follows from postcondition of ResolveExpression

      if (me.Source.Type is TypeProxy) {
        PartiallySolveTypeConstraints(true);
        if (debug) {
          Console.WriteLine("DEBUG: Type of {0} was still a proxy, solving type constraints results in type {1}", Printer.ExprToString(me.Source), me.Source.Type.ToString());
        }

        if (me.Source.Type is TypeProxy) {
          reporter.Error(MessageSource.Resolver, me.tok, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
          return;
        }
      }

      var errorCount = reporter.Count(ErrorLevel.Error);
      var sourceType = PartiallyResolveTypeForMemberSelection(me.Source.tok, me.Source.Type).NormalizeExpand();
      if (reporter.Count(ErrorLevel.Error) != errorCount) {
        return;
      }

      errorCount = reporter.Count(ErrorLevel.Error);
      if (debug) {
        Console.WriteLine("DEBUG: {0} ResolveNestedMatchExpr  1 - Checking Linearity of patterns", me.tok.line);
      }

      CheckLinearNestedMatchExpr(sourceType, me, resolutionContext);
      if (reporter.Count(ErrorLevel.Error) != errorCount) {
        return;
      }

      errorCount = reporter.Count(ErrorLevel.Error);
      if (debug) {
        Console.WriteLine("DEBUG: {0} ResolveNestedMatchExpr  2 - Compiling Nested Match", me.tok.line);
      }

      CompileNestedMatchExpr(me, resolutionContext);
      if (reporter.Count(ErrorLevel.Error) != errorCount) {
        return;
      }

      if (debug) {
        Console.WriteLine("DEBUG: {0} ResolveNestedMatchExpr  3 - Resolving Expression", me.tok.line);
      }

      ResolveExpression(me.ResolvedExpression, resolutionContext);

      if (debug) {
        Console.WriteLine("DEBUG: {0} ResolveNestedMatchExpr   DONE");
      }
    }

    void ResolveMatchExpr(MatchExpr me, ResolutionContext resolutionContext) {
      Contract.Requires(me != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(me.OrigUnresolved == null);
      bool debug = DafnyOptions.O.MatchCompilerDebug;
      if (debug) {
        Console.WriteLine("DEBUG: {0} In ResolvedMatchExpr");
      }

      // first, clone the original match expression
      me.OrigUnresolved = (MatchExpr)new ClonerKeepParensExpressions().CloneExpr(me);
      ResolveExpression(me.Source, resolutionContext);

      Contract.Assert(me.Source.Type != null);  // follows from postcondition of ResolveExpression

      var sourceType = PartiallyResolveTypeForMemberSelection(me.Source.tok, me.Source.Type).NormalizeExpand();
      if (debug) {
        Console.WriteLine("DEBUG: {0} ResolvedMatchExpr - Done Resolving Source");
      }

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
        if (debug) {
          Console.WriteLine("DEBUG: {1} ResolvedMatchExpr - Resolving Body: {0}", Printer.ExprToString(mc.Body), mc.Body.tok.line);
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
      if (debug) {
        Console.WriteLine("DEBUG: {0} ResolvedMatchExpr - DONE", me.tok.line);
      }
    }

    void ResolveCasePattern<VT>(CasePattern<VT> pat, Type sourceType, ResolutionContext resolutionContext) where VT : IVariable {
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
          if (datatypeCtors[dtd].TryGetValue(pat.Id, out ctor)) {
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
        AddTypeDependencyEdges(resolutionContext.CodeContext, v.Type);
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

    Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args,
      ResolutionContext resolutionContext, bool allowMethodCall, bool complain = true) {
      return ResolveNameSegment(expr, isLastNameSegment, args, resolutionContext, allowMethodCall, complain, out _);
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
    ///  5. If !isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module
    ///
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the NameSegment is not directly enclosed in another NameSegment or ExprDotName expression.</param>
    /// <param name="args">If the NameSegment is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="resolutionContext"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a MemberSelectExpr whose .Member is a Method.</param>
    /// <param name="shadowedModule">If the name being resolved shadows an imported module, then that module is reported
    /// through this parameter.  This happens when module <c>Option</c> in <c>import opened Option</c> also contains a
    /// <c>datatype Option</c>, in which case <c>Option</c> refers to the datatype, not the module
    /// (https://github.com/dafny-lang/dafny/issues/1996).</param>
    Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args, ResolutionContext resolutionContext, bool allowMethodCall, bool complain, out ModuleDecl shadowedModule) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      shadowedModule = null;

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
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
      // For 2 and 5:
      Tuple<DatatypeCtor, bool> pair;
      // For 3:
      TopLevelDecl decl;

      var name = resolutionContext.InReveal ? "reveal_" + expr.Name : expr.Name;
      v = scope.Find(name);
      if (v != null) {
        // ----- 0. local variable, parameter, or bound variable
        if (expr.OptTypeArguments != null) {
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "variable '{0}' does not take any type parameters", name);
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        }
        r = new IdentifierExpr(expr.tok, v);
      } else if (currentClass is TopLevelDeclWithMembers cl && classMembers.TryGetValue(cl, out members) && members.TryGetValue(name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, UserDefinedType.FromTopLevelDecl(expr.tok, currentClass, currentClass.TypeArgs), (TopLevelDeclWithMembers)member.EnclosingClass, true);
        } else {
          if (!scope.AllowInstance) {
            if (complain) {
              reporter.Error(MessageSource.Resolver, expr.tok, "'this' is not allowed in a 'static' context"); //TODO: Rephrase this
            } else {
              expr.ResolvedExpression = null;
              return null;
            }
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = GetThisType(expr.tok, currentClass);  // resolve here
        }
        r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
      } else if (isLastNameSegment && moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 2. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }
      } else if (moduleInfo.TopLevels.TryGetValue(name, out decl)) {
        // ----- 3. Member of the enclosing module

        // Record which imported module, if any, was shadowed by `name` in the current module.
        shadowedModule = moduleInfo.ShadowedImportedModules.GetValueOrDefault(name);

        if (decl is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)decl;
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.Name, ad.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          // We have found a module name or a type name, neither of which is an expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          if (!isLastNameSegment) {
            if (decl is ClassDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
              // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
              // the name of the class, C. Report an error and continue.
              if (complain) {
                reporter.Error(MessageSource.Resolver, expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              } else {
                expr.ResolvedExpression = null;
                return null;
              }
            }
          }
          r = CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
        }

      } else if (moduleInfo.StaticMembers.TryGetValue(name, out member)) {
        // ----- 4. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (member is AmbiguousMemberDecl) {
          var ambiguousMember = (AmbiguousMemberDecl)member;
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ambiguousMember.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass, true);
          r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
        }

      } else if (!isLastNameSegment && moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 5. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }

      } else {
        // ----- None of the above
        if (complain) {
          reporter.Error(MessageSource.Resolver, expr.tok, "unresolved identifier: {0}", name);
        } else {
          expr.ResolvedExpression = null;
          return null;
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        var rt = r.Type;
        var nt = rt.UseInternalSynonym();
        expr.Type = nt;
      }
      return rWithArgs;
    }

    private bool ResolveDatatypeConstructor(NameSegment expr, List<ActualBinding>/*?*/ args, ResolutionContext resolutionContext, bool complain, Tuple<DatatypeCtor, bool> pair, string name, ref Expression r, ref Expression rWithArgs) {
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);

      if (pair.Item2) {
        // there is more than one constructor with this name
        if (complain) {
          reporter.Error(MessageSource.Resolver, expr.tok, "the name '{0}' denotes a datatype constructor, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", expr.Name,
            pair.Item1.EnclosingDatatype.Name);
        } else {
          expr.ResolvedExpression = null;
          return true;
        }
      } else {
        if (expr.OptTypeArguments != null) {
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
          } else {
            expr.ResolvedExpression = null;
            return true;
          }
        }
        var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
        bool ok = ResolveDatatypeValue(resolutionContext, rr, pair.Item1.EnclosingDatatype, null, complain);
        if (!ok) {
          expr.ResolvedExpression = null;
          return true;
        }
        if (args == null) {
          r = rr;
        } else {
          r = rr; // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
          rWithArgs = rr;
        }
      }
      return false;
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
    void ResolveNameSegment_Type(NameSegment expr, ResolutionContext resolutionContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, option, defaultTypeArguments);
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
        r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.resolutionContext, allowMethodCall);
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
          r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.resolutionContext, allowMethodCall);
        }
#endif
      } else {
        // ----- None of the above
        reporter.Error(MessageSource.Resolver, expr.tok, "Undeclared top-level type or type parameter: {0} (did you forget to qualify a name or declare a module import 'opened'?)", expr.Name);
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
        if (decl is ModuleDecl md && md.Signature.IsAbstract) {
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
    /// <param name="resolutionContext"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a Resolver_MethodCall.</param>
    Expression ResolveDotSuffix(ExprDotName expr, bool isLastNameSegment, List<ActualBinding> args, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      // resolve the LHS expression
      // LHS should not be reveal lemma
      ModuleDecl shadowedImport = null;
      ResolutionContext nonRevealOpts = resolutionContext with { InReveal = false };
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment((NameSegment)expr.Lhs, false, null, nonRevealOpts, false, true, out shadowedImport);
      } else if (expr.Lhs is ExprDotName) {
        ResolveDotSuffix((ExprDotName)expr.Lhs, false, null, nonRevealOpts, false);
      } else {
        ResolveExpression(expr.Lhs, nonRevealOpts);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"
      MemberDecl member = null;

      var name = resolutionContext.InReveal ? "reveal_" + expr.SuffixName : expr.SuffixName;
      if (!expr.Lhs.WasResolved()) {
        return null;
      }
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
            var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
            ResolveDatatypeValue(resolutionContext, rr, pair.Item1.EnclosingDatatype, null);

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
              if (decl is ClassDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
                // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
                // the name of the class, C. Report an error and continue.
                reporter.Error(MessageSource.Resolver, expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
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
            var receiver = new StaticReceiverExpr(expr.Lhs.tok, (ClassDecl)member.EnclosingClass, false);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "unresolved identifier: {0}", name);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 3. Look up name in type
        // expand any synonyms
        var ty = new UserDefinedType(expr.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs).NormalizeExpand();
        if (ty.IsDatatype) {
          // ----- LHS is a datatype
          var dt = ty.AsDatatype;
          Dictionary<string, DatatypeCtor> members;
          DatatypeCtor ctor;
          if (datatypeCtors.TryGetValue(dt, out members) && members.TryGetValue(name, out ctor)) {
            if (expr.OptTypeArguments != null) {
              reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
            }
            var rr = new DatatypeValue(expr.tok, ctor.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
            ResolveDatatypeValue(resolutionContext, rr, ctor.EnclosingDatatype, ty);
            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        }
        var cd = r == null ? ty.AsTopLevelTypeWithMembersBypassInternalSynonym : null;
        if (cd != null) {
          // ----- LHS is a type with members
          Dictionary<string, MemberDecl> members;
          if (classMembers.TryGetValue(cd, out members) && members.TryGetValue(name, out member)) {
            if (!VisibleInScope(member)) {
              reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' has not been imported in this scope and cannot be accessed here", name);
            }
            if (!member.IsStatic) {
              reporter.Error(MessageSource.Resolver, expr.tok, "accessing member '{0}' requires an instance expression", name); //TODO Unify with similar error messages
              // nevertheless, continue creating an expression that approximates a correct one
            }
            var receiver = new StaticReceiverExpr(expr.Lhs.tok, (UserDefinedType)ty.NormalizeExpand(), (TopLevelDeclWithMembers)member.EnclosingClass, false);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        }
        if (r == null) {
          reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' does not exist in {2} '{1}'", name, ri.Decl.Name, ri.Decl.WhatKind);
        }
      } else if (lhs != null) {
        // ----- 4. Look up name in the type of the Lhs
        NonProxyType tentativeReceiverType;
        member = ResolveMember(expr.tok, expr.Lhs.Type, name, out tentativeReceiverType);
        if (member != null) {
          Expression receiver;
          if (!member.IsStatic) {
            receiver = expr.Lhs;
            AddAssignableConstraint(expr.tok, tentativeReceiverType, receiver.Type, "receiver type ({1}) does not have a member named " + name);
            r = ResolveExprDotCall(expr.tok, receiver, tentativeReceiverType, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          } else {
            receiver = new StaticReceiverExpr(expr.tok, (UserDefinedType)tentativeReceiverType, (TopLevelDeclWithMembers)member.EnclosingClass, false, lhs);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        CheckForAmbiguityInShadowedImportedModule(shadowedImport, name, expr.tok, useCompileSignatures, isLastNameSegment);
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return rWithArgs;
    }

    /// <summary>
    /// Check whether the name we just resolved may have been resolved differently if we didn't allow member `M.M` of
    /// module `M` to shadow `M` when the user writes `import opened M`.  Raising an error in that case allowed us to
    /// change the behavior of `import opened` without silently changing the meaning of existing programs.
    /// (https://github.com/dafny-lang/dafny/issues/1996)
    ///
    /// Note the extra care for the constructor case, which is needed because the constructors of datatype `M.M` are
    /// exposed through both `M` and `M.M`, without ambiguity.
    /// </summary>
    private void CheckForAmbiguityInShadowedImportedModule(ModuleDecl moduleDecl, string name,
      IToken tok, bool useCompileSignatures, bool isLastNameSegment) {
      if (moduleDecl != null && NameConflictsWithModuleContents(moduleDecl, name, useCompileSignatures, isLastNameSegment)) {
        reporter.Error(MessageSource.Resolver, tok,
          "Reference to member '{0}' is ambiguous: name '{1}' shadows an import-opened module of the same name, and "
          + "both have a member '{0}'. To solve this issue, give a different name to the imported module using "
          + "`import opened XYZ = ...` instead of `import opened ...`.",
          name, moduleDecl.Name);
      }
    }

    private bool NameConflictsWithModuleContents(ModuleDecl moduleDecl, string name, bool useCompileSignatures, bool isLastNameSegment) {
      var sig = GetSignature(moduleDecl.AccessibleSignature(useCompileSignatures));
      return (
        (isLastNameSegment
         && sig.Ctors.GetValueOrDefault(name) is { Item1: var constructor, Item2: var ambiguous }
         && !ambiguous && constructor.EnclosingDatatype.Name != moduleDecl.Name)
        || sig.TopLevels.ContainsKey(name)
        || sig.StaticMembers.ContainsKey(name)
      );
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
    ResolveTypeReturn ResolveDotSuffix_Type(ExprDotName expr, ResolutionContext resolutionContext, bool allowDanglingDotName, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(expr.Lhs is NameSegment || expr.Lhs is ExprDotName);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<ResolveTypeReturn>() == null || allowDanglingDotName);

      // resolve the LHS expression
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment_Type((NameSegment)expr.Lhs, resolutionContext, option, defaultTypeArguments);
      } else {
        ResolveDotSuffix_Type((ExprDotName)expr.Lhs, resolutionContext, false, option, defaultTypeArguments);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, option, defaultTypeArguments);
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
            r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.resolutionContext, allowMethodCall);
          }
#endif
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "module '{0}' does not declare a type '{1}'", ri.Decl.Name, expr.SuffixName);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 2. Look up name in type
        var ty = new UserDefinedType(ri.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs);
        if (allowDanglingDotName && ty.IsRefType) {
          return new ResolveTypeReturn(ty, expr);
        }
        if (r == null) {
          reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' does not exist in type '{1}' or cannot be part of type name", expr.SuffixName, ri.Decl.Name);
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

    Expression ResolveExprDotCall(IToken tok, Expression receiver, Type receiverTypeBound/*?*/,
      MemberDecl member, List<ActualBinding> args, List<Type> optTypeArguments, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(receiver.WasResolved());
      Contract.Requires(member != null);
      Contract.Requires(resolutionContext != null && resolutionContext.CodeContext != null);

      var rr = new MemberSelectExpr(tok, receiver, member.Name);
      rr.Member = member;

      // Now, fill in rr.Type.  This requires taking into consideration the type parameters passed to the receiver's type as well as any type
      // parameters used in this NameSegment/ExprDotName.
      // Add to "subst" the type parameters given to the member's class/datatype
      rr.TypeApplication_AtEnclosingClass = new List<Type>();
      rr.TypeApplication_JustMember = new List<Type>();
      Dictionary<TypeParameter, Type> subst;
      var rType = (receiverTypeBound ?? receiver.Type).NormalizeExpand();
      if (rType is UserDefinedType udt && udt.ResolvedClass != null) {
        subst = TypeParameter.SubstitutionMap(udt.ResolvedClass.TypeArgs, udt.TypeArgs);
        if (member.EnclosingClass == null) {
          // this can happen for some special members, like real.Floor
        } else {
          rr.TypeApplication_AtEnclosingClass.AddRange(rType.AsParentType(member.EnclosingClass).TypeArgs);
        }
      } else {
        var vtd = AsValuetypeDecl(rType);
        if (vtd != null) {
          Contract.Assert(vtd.TypeArgs.Count == rType.TypeArgs.Count);
          subst = TypeParameter.SubstitutionMap(vtd.TypeArgs, rType.TypeArgs);
          rr.TypeApplication_AtEnclosingClass.AddRange(rType.TypeArgs);
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
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.Type = field.Type.Subst(subst);
        AddCallGraphEdgeForField(resolutionContext.CodeContext, field, rr);
      } else if (member is Function) {
        var fn = (Function)member;
        if (fn is TwoStateFunction && !resolutionContext.IsTwoState) {
          reporter.Error(MessageSource.Resolver, tok, "two-state function ('{0}') can only be called in a two-state context", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != fn.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "function '{0}' expects {1} type argument{2} (got {3})",
            member.Name, fn.TypeArgs.Count, Util.Plural(fn.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < fn.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication_JustMember.Add(ta);
          subst.Add(fn.TypeArgs[i], ta);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.Type = SelectAppropriateArrowType(fn.tok,
          fn.Formals.ConvertAll(f => f.Type.Subst(subst)),
          fn.ResultType.Subst(subst),
          fn.Reads.Count != 0, fn.Req.Count != 0);
        AddCallGraphEdge(resolutionContext.CodeContext, fn, rr, IsFunctionReturnValue(fn, args, resolutionContext));
      } else {
        // the member is a method
        var m = (Method)member;
        if (!allowMethodCall) {
          // it's a method and method calls are not allowed in the given context
          reporter.Error(MessageSource.Resolver, tok, "expression is not allowed to invoke a {0} ({1})", member.WhatKind, member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != m.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "method '{0}' expects {1} type argument{2} (got {3})",
            member.Name, m.TypeArgs.Count, Util.Plural(m.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < m.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication_JustMember.Add(ta);
          subst.Add(m.TypeArgs[i], ta);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.ResolvedOutparameterTypes = m.Outs.ConvertAll(f => f.Type.Subst(subst));
        rr.Type = new InferredTypeProxy();  // fill in this field, in order to make "rr" resolved
      }
      return rr;
    }

    private bool IsFunctionReturnValue(Function fn, List<ActualBinding> args, ResolutionContext resolutionContext) {
      bool isFunctionReturnValue = true;
      // if the call is in post-condition and it is calling itself, and the arguments matches
      // formal parameters, then it denotes function return value.
      if (args != null && resolutionContext.InFunctionPostcondition && resolutionContext.CodeContext == fn) {
        foreach (var binding in args) {
          if (binding.Actual is NameSegment ns) {
            IVariable v = scope.Find(ns.Name);
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

    class MethodCallInformation {
      public readonly IToken Tok;
      public readonly MemberSelectExpr Callee;
      public readonly List<ActualBinding> ActualParameters;

      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Tok != null);
        Contract.Invariant(Callee != null);
        Contract.Invariant(Callee.Member is Method);
        Contract.Invariant(ActualParameters != null);
      }

      public MethodCallInformation(IToken tok, MemberSelectExpr callee, List<ActualBinding> actualParameters) {
        Contract.Requires(tok != null);
        Contract.Requires(callee != null);
        Contract.Requires(callee.Member is Method);
        Contract.Requires(actualParameters != null);
        this.Tok = tok;
        this.Callee = callee;
        this.ActualParameters = actualParameters;
      }
    }

    MethodCallInformation ResolveApplySuffix(ApplySuffix e, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(e != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<MethodCallInformation>() == null || allowMethodCall);
      Expression r = null;  // upon success, the expression to which the ApplySuffix resolves
      var errorCount = reporter.Count(ErrorLevel.Error);
      if (e.Lhs is NameSegment) {
        r = ResolveNameSegment((NameSegment)e.Lhs, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else if (e.Lhs is ExprDotName) {
        r = ResolveDotSuffix((ExprDotName)e.Lhs, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else {
        ResolveExpression(e.Lhs, resolutionContext);
      }
      if (e.Lhs.Type == null) {
        // some error had been detected during the attempted resolution of e.Lhs
        e.Lhs.Type = new InferredTypeProxy();
      }
      Label atLabel = null;
      if (e.AtTok != null) {
        atLabel = dominatingStatementLabels.Find(e.AtTok.val);
        if (atLabel == null) {
          reporter.Error(MessageSource.Resolver, e.AtTok, "no label '{0}' in scope at this time", e.AtTok.val);
        }
      }
      if (r == null) {
        var improvedType = PartiallyResolveTypeForMemberSelection(e.Lhs.tok, e.Lhs.Type, "_#apply");
        var fnType = improvedType.AsArrowType;
        if (fnType == null) {
          var lhs = e.Lhs.Resolved;
          if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
            reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a function", ((Resolver_IdentifierExpr)lhs).Decl.Name);
          } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            var ri = (Resolver_IdentifierExpr)lhs;
            reporter.Error(MessageSource.Resolver, e.tok, "name of {0} ({1}) is used as a function", ri.Decl.WhatKind, ri.Decl.Name);
          } else {
            if (lhs is MemberSelectExpr mse && mse.Member is Method) {
              if (atLabel != null) {
                Contract.Assert(mse != null); // assured by the parser
                if (mse.Member is TwoStateLemma) {
                  mse.AtLabel = atLabel;
                } else {
                  reporter.Error(MessageSource.Resolver, e.AtTok, "an @-label can only be applied to a two-state lemma");
                }
              }
              if (allowMethodCall) {
                Contract.Assert(!e.Bindings.WasResolved); // we expect that .Bindings has not yet been processed, so we use just .ArgumentBindings in the next line
                var tok = DafnyOptions.O.Get(DafnyConsolePrinter.ShowSnippets) ? new RangeToken(e.Lhs.tok, e.CloseParen) : e.tok;
                var cRhs = new MethodCallInformation(tok, mse, e.Bindings.ArgumentBindings);
                return cRhs;
              } else {
                reporter.Error(MessageSource.Resolver, e.tok, "{0} call is not allowed to be used in an expression context ({1})", mse.Member.WhatKind, mse.Member.Name);
              }
            } else if (lhs != null) {  // if e.Lhs.Resolved is null, then e.Lhs was not successfully resolved and an error has already been reported
              reporter.Error(MessageSource.Resolver, e.tok, "non-function expression (of type {0}) is called with parameters", e.Lhs.Type);
            }
          }
          // resolve the arguments, even in the presence of the errors above
          foreach (var binding in e.Bindings.ArgumentBindings) {
            ResolveExpression(binding.Actual, resolutionContext);
          }
        } else {
          var mse = e.Lhs is NameSegment || e.Lhs is ExprDotName ? e.Lhs.Resolved as MemberSelectExpr : null;
          var callee = mse == null ? null : mse.Member as Function;
          if (atLabel != null && !(callee is TwoStateFunction)) {
            reporter.Error(MessageSource.Resolver, e.AtTok, "an @-label can only be applied to a two-state function");
            atLabel = null;
          }
          if (callee != null) {
            // produce a FunctionCallExpr instead of an ApplyExpr(MemberSelectExpr)
            var rr = new FunctionCallExpr(e.Lhs.tok, callee.Name, mse.Obj, e.tok, e.CloseParen, e.Bindings, atLabel) {
              Function = callee,
              TypeApplication_AtEnclosingClass = mse.TypeApplication_AtEnclosingClass,
              TypeApplication_JustFunction = mse.TypeApplication_JustMember
            };
            var typeMap = BuildTypeArgumentSubstitute(mse.TypeArgumentSubstitutionsAtMemberDeclaration());
            ResolveActualParameters(rr.Bindings, callee.Formals, e.tok, callee, resolutionContext, typeMap, callee.IsStatic ? null : mse.Obj);
            rr.Type = callee.ResultType.Subst(typeMap);
            if (errorCount == reporter.Count(ErrorLevel.Error)) {
              Contract.Assert(!(mse.Obj is StaticReceiverExpr) || callee.IsStatic);  // this should have been checked already
              Contract.Assert(callee.Formals.Count == rr.Args.Count);  // this should have been checked already
            }
            // further bookkeeping
            if (callee is ExtremePredicate) {
              ((ExtremePredicate)callee).Uses.Add(rr);
            }
            AddCallGraphEdge(resolutionContext.CodeContext, callee, rr, IsFunctionReturnValue(callee, e.Bindings.ArgumentBindings, resolutionContext));
            r = rr;
          } else {
            List<Formal> formals;
            if (callee != null) {
              formals = callee.Formals;
            } else {
              formals = new List<Formal>();
              for (var i = 0; i < fnType.Args.Count; i++) {
                var argType = fnType.Args[i];
                var formal = new ImplicitFormal(e.tok, "_#p" + i, argType, true, false);
                formals.Add(formal);
              }
            }
            ResolveActualParameters(e.Bindings, formals, e.tok, fnType, resolutionContext, new Dictionary<TypeParameter, Type>(), null);
            r = new ApplyExpr(e.Lhs.tok, e.Lhs, e.Args, e.CloseParen);
            r.Type = fnType.Result;
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

    /// <summary>
    /// Resolve the actual arguments given in "bindings". Then, check that there is exactly one
    /// actual for each formal, and impose assignable constraints.
    /// "typeMap" is applied to the type of each formal.
    /// This method should be called only once. That is, bindings.arguments is required to be null on entry to this method.
    /// </summary>
    void ResolveActualParameters(ActualBindings bindings, List<Formal> formals, IToken callTok, object context, ResolutionContext resolutionContext,
      Dictionary<TypeParameter, Type> typeMap, Expression/*?*/ receiver) {
      Contract.Requires(bindings != null);
      Contract.Requires(formals != null);
      Contract.Requires(callTok != null);
      Contract.Requires(context is Method || context is Function || context is DatatypeCtor || context is ArrowType);
      Contract.Requires(typeMap != null);
      Contract.Requires(!bindings.WasResolved);

      string whatKind;
      string name;
      if (context is Method cMethod) {
        whatKind = cMethod.WhatKind;
        name = $"{whatKind} '{cMethod.Name}'";
      } else if (context is Function cFunction) {
        whatKind = cFunction.WhatKind;
        name = $"{whatKind} '{cFunction.Name}'";
      } else if (context is DatatypeCtor cCtor) {
        whatKind = "datatype constructor";
        name = $"{whatKind} '{cCtor.Name}'";
      } else {
        var cArrowType = (ArrowType)context;
        whatKind = "function application";
        name = $"function type '{cArrowType}'";
      }

      // If all arguments are passed positionally, use simple error messages that talk about the count of arguments.
      var onlyPositionalArguments = bindings.ArgumentBindings.TrueForAll(binding => binding.FormalParameterName == null);
      var simpleErrorReported = false;
      if (onlyPositionalArguments) {
        var requiredParametersCount = formals.Count(f => f.DefaultValue == null);
        var actualsCounts = bindings.ArgumentBindings.Count;
        if (requiredParametersCount <= actualsCounts && actualsCounts <= formals.Count) {
          // the situation is plausible
        } else if (requiredParametersCount == formals.Count) {
          // this is the common, classical case of no default parameter values; generate a straightforward error message
          reporter.Error(MessageSource.Resolver, callTok, $"wrong number of arguments ({name} expects {formals.Count}, got {actualsCounts})");
          simpleErrorReported = true;
        } else if (actualsCounts < requiredParametersCount) {
          reporter.Error(MessageSource.Resolver, callTok, $"wrong number of arguments ({name} expects at least {requiredParametersCount}, got {actualsCounts})");
          simpleErrorReported = true;
        } else {
          reporter.Error(MessageSource.Resolver, callTok, $"wrong number of arguments ({name} expects at most {formals.Count}, got {actualsCounts})");
          simpleErrorReported = true;
        }
      }

      // resolve given arguments and populate the "namesToActuals" map
      var namesToActuals = new Dictionary<string, ActualBinding>();
      formals.ForEach(f => namesToActuals.Add(f.Name, null)); // a name mapping to "null" says it hasn't been filled in yet
      var stillAcceptingPositionalArguments = true;
      var bindingIndex = 0;
      foreach (var binding in bindings.ArgumentBindings) {
        var arg = binding.Actual;
        // insert the actual into "namesToActuals" under an appropriate name, unless there is an error
        if (binding.FormalParameterName != null) {
          var pname = binding.FormalParameterName.val;
          stillAcceptingPositionalArguments = false;
          if (!namesToActuals.TryGetValue(pname, out var b)) {
            reporter.Error(MessageSource.Resolver, binding.FormalParameterName, $"the binding named '{pname}' does not correspond to any formal parameter");
          } else if (b == null) {
            // all is good
            namesToActuals[pname] = binding;
          } else if (b.FormalParameterName == null) {
            reporter.Error(MessageSource.Resolver, binding.FormalParameterName, $"the parameter named '{pname}' is already given positionally");
          } else {
            reporter.Error(MessageSource.Resolver, binding.FormalParameterName, $"duplicate binding for parameter name '{pname}'");
          }
        } else if (!stillAcceptingPositionalArguments) {
          reporter.Error(MessageSource.Resolver, arg.tok, "a positional argument is not allowed to follow named arguments");
        } else if (bindingIndex < formals.Count) {
          // use the name of formal corresponding to this positional argument, unless the parameter is named-only
          var formal = formals[bindingIndex];
          var pname = formal.Name;
          if (formal.IsNameOnly) {
            reporter.Error(MessageSource.Resolver, arg.tok,
              $"nameonly parameter '{pname}' must be passed using a name binding; it cannot be passed positionally");
          }
          Contract.Assert(namesToActuals[pname] == null); // we expect this, since we've only filled parameters positionally so far
          namesToActuals[pname] = binding;
        } else {
          // too many positional arguments
          if (onlyPositionalArguments) {
            // error was reported before the "foreach" loop
            Contract.Assert(simpleErrorReported);
          } else if (formals.Count < bindingIndex) {
            // error was reported on a previous iteration of this "foreach" loop
          } else {
            reporter.Error(MessageSource.Resolver, callTok,
              $"wrong number of arguments ({name} expects {formals.Count}, got {bindings.ArgumentBindings.Count})");
          }
        }

        // resolve argument
        ResolveExpression(arg, resolutionContext);
        bindingIndex++;
      }

      var actuals = new List<Expression>();
      var formalIndex = 0;
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (var formal in formals) {
        var b = namesToActuals[formal.Name];
        if (b != null) {
          actuals.Add(b.Actual);
          substMap.Add(formal, b.Actual);
          var what = GetLocationInformation(formal,
            bindings.ArgumentBindings.Count(), bindings.ArgumentBindings.IndexOf(b),
            whatKind + (context is Method ? " in-parameter" : " parameter"));

          AddAssignableConstraint(
            callTok, formal.Type.Subst(typeMap), b.Actual.Type,
            $"incorrect argument type {what} (expected {{0}}, found {{1}})");
        } else if (formal.DefaultValue != null) {
          // Note, in the following line, "substMap" is passed in, but it hasn't been fully filled in until the
          // end of this foreach loop. Still, that's soon enough, because DefaultValueExpression won't use it
          // until FillInDefaultValueExpressions at the end of Pass 1 of the Resolver.
          var n = new DefaultValueExpression(callTok, formal, receiver, substMap, typeMap);
          allDefaultValueExpressions.Add(n);
          actuals.Add(n);
          substMap.Add(formal, n);
        } else {
          // parameter has no value
          if (onlyPositionalArguments) {
            // a simple error message has already been reported
            Contract.Assert(simpleErrorReported);
          } else {
            var formalDescription = whatKind + (context is Method ? " in-parameter" : " parameter");
            var nameWithIndex = formal.HasName && formal is not ImplicitFormal ? "'" + formal.Name + "'" : "";
            if (formals.Count > 1 || nameWithIndex == "") {
              nameWithIndex += nameWithIndex == "" ? "" : " ";
              nameWithIndex += $"at index {formalIndex}";
            }
            var message = $"{formalDescription} {nameWithIndex} requires an argument of type {formal.Type}";
            reporter.Error(MessageSource.Resolver, callTok, message);
          }
        }
        formalIndex++;
      }

      bindings.AcceptArgumentExpressionsAsExactParameterList(actuals);
    }

    private static string GetLocationInformation(Formal parameter, int bindingCount, int bindingIndex, string formalDescription) {
      var displayName = parameter.HasName && parameter is not ImplicitFormal;
      var description = "";
      if (bindingCount > 1) {
        description += $"at index {bindingIndex} ";
      }

      description += $"for {formalDescription}";

      if (displayName) {
        description += $" '{parameter.Name}'";
      }

      return description;
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

    /// <summary>
    /// the return value is false iff there is an error in resolving the datatype value;
    /// if there is an error then an error message is emitted iff complain is true
    /// </summary>
    private bool ResolveDatatypeValue(ResolutionContext resolutionContext, DatatypeValue dtv, DatatypeDecl dt, Type ty, bool complain = true) {
      Contract.Requires(resolutionContext != null);
      Contract.Requires(dtv != null);
      Contract.Requires(dt != null);
      Contract.Requires(ty == null || (ty.AsDatatype == dt && ty.TypeArgs.Count == dt.TypeArgs.Count));

      var ok = true;
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
        ok = false;
        if (complain) {
          reporter.Error(MessageSource.Resolver, dtv.tok, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
        }
      } else {
        Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
        dtv.Ctor = ctor;
      }
      if (complain && ctor != null) {
        ResolveActualParameters(dtv.Bindings, ctor.Formals, dtv.tok, ctor, resolutionContext, subst, null);
      } else {
        // still resolve the expressions
        foreach (var binding in dtv.Bindings.ArgumentBindings) {
          ResolveExpression(binding.Actual, resolutionContext);
        }
        dtv.Bindings.AcceptArgumentExpressionsAsExactParameterList();
      }

      if (CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is ICallable caller && caller.EnclosingModule == dt.EnclosingModuleDefinition) {
        caller.EnclosingModule.CallGraph.AddEdge(caller, dt);
      }
      return ok && ctor.Formals.Count == dtv.Arguments.Count;
    }

    public static string GhostPrefix(bool isGhost) {
      return isGhost ? "ghost " : "";
    }

    public void ResolveFunctionCallExpr(FunctionCallExpr e, ResolutionContext resolutionContext) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type == null);  // should not have been type checked before

      ResolveReceiver(e.Receiver, resolutionContext);
      Contract.Assert(e.Receiver.Type != null);  // follows from postcondition of ResolveExpression

      NonProxyType tentativeReceiverType;
      var member = ResolveMember(e.tok, e.Receiver.Type, e.Name, out tentativeReceiverType);
#if !NO_WORK_TO_BE_DONE
      var ctype = (UserDefinedType)tentativeReceiverType;
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
        if (function is ExtremePredicate) {
          ((ExtremePredicate)function).Uses.Add(e);
        }
        if (function is TwoStateFunction && !resolutionContext.IsTwoState) {
          reporter.Error(MessageSource.Resolver, e.tok, "a two-state function can be used only in a two-state context");
        }
        if (e.Receiver is StaticReceiverExpr && !function.IsStatic) {
          reporter.Error(MessageSource.Resolver, e, "an instance function must be selected via an object, not just a class name");
        }
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
        var typeMap = new Dictionary<TypeParameter, Type>();
        for (int i = 0; i < ctype.TypeArgs.Count; i++) {
          typeMap.Add(ctype.ResolvedClass.TypeArgs[i], ctype.TypeArgs[i]);
        }
        var typeThatEnclosesMember = ctype.AsParentType(member.EnclosingClass);
        e.TypeApplication_AtEnclosingClass = new List<Type>();
        for (int i = 0; i < typeThatEnclosesMember.TypeArgs.Count; i++) {
          e.TypeApplication_AtEnclosingClass.Add(typeThatEnclosesMember.TypeArgs[i]);
        }
        e.TypeApplication_JustFunction = new List<Type>();
        foreach (TypeParameter p in function.TypeArgs) {
          var ty = new ParamTypeProxy(p);
          typeMap.Add(p, ty);
          e.TypeApplication_JustFunction.Add(ty);
        }
        Dictionary<TypeParameter, Type> subst = BuildTypeArgumentSubstitute(typeMap);

        // type check the arguments
        ResolveActualParameters(e.Bindings, function.Formals, e.tok, function, resolutionContext, subst, function.IsStatic ? null : e.Receiver);

        e.Type = function.ResultType.Subst(subst).NormalizeExpand();

        AddCallGraphEdge(resolutionContext.CodeContext, function, e, IsFunctionReturnValue(function, e.Bindings.ArgumentBindings, resolutionContext));
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

    internal void AddCallGraphEdge(ICodeContext callingContext, ICallable function, Expression e, bool isFunctionReturnValue) {
      Contract.Requires(callingContext != null);
      Contract.Requires(function != null);
      Contract.Requires(e != null);
      // Resolution termination check
      ModuleDefinition callerModule = callingContext.EnclosingModule;
      ModuleDefinition calleeModule = function is SpecialFunction ? null : function.EnclosingModule;
      if (callerModule == calleeModule) {
        // intra-module call; add edge in module's call graph
        var caller = CodeContextWrapper.Unwrap(callingContext) as ICallable;
        if (caller == null) {
          // don't add anything to the call graph after all
        } else {
          callerModule.CallGraph.AddEdge(caller, function);
          if (caller is Function && e is FunctionCallExpr ee) {
            ((Function)caller).AllCalls.Add(ee);
          }
          // if the call denotes the function return value in the function postconditions, then we don't
          // mark it as recursive.
          if (caller == function && function is Function && !isFunctionReturnValue) {
            ((Function)function).IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
          }
        }
      }
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
        return FreeVariables(((NestedMatchExpr)expr).ResolvedExpression);
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

    void ResolveReceiver(Expression expr, ResolutionContext resolutionContext) {
      Contract.Requires(expr != null);
      Contract.Ensures(expr.Type != null);

      if (expr is ThisExpr && !expr.WasResolved()) {
        // Allow 'this' here, regardless of scope.AllowInstance.  The caller is responsible for
        // making sure 'this' does not really get used when it's not available.
        Contract.Assume(currentClass != null);  // this is really a precondition, in this case
        expr.Type = GetThisType(expr.tok, currentClass);
      } else {
        ResolveExpression(expr, resolutionContext);
      }
    }

    void ResolveSeqSelectExpr(SeqSelectExpr e, ResolutionContext resolutionContext) {
      Contract.Requires(e != null);
      if (e.Type != null) {
        // already resolved
        return;
      }

      ResolveExpression(e.Seq, resolutionContext);
      Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression

      if (e.SelectOne) {
        AddXConstraint(e.tok, "Indexable", e.Seq.Type, "element selection requires a sequence, array, multiset, or map (got {0})");
        ResolveExpression(e.E0, resolutionContext);
        AddXConstraint(e.E0.tok, "ContainerIndex", e.Seq.Type, e.E0.Type, "incorrect type for selection into {0} (got {1})");
        Contract.Assert(e.E1 == null);
        e.Type = new InferredTypeProxy() { KeepConstraints = true };
        AddXConstraint(e.tok, "ContainerResult",
          e.Seq.Type, e.Type,
          new SeqSelectOneErrorMsg(e.tok, e.Seq.Type, e.Type));
      } else {
        AddXConstraint(e.tok, "MultiIndexable", e.Seq.Type, "multi-selection of elements requires a sequence or array (got {0})");
        if (e.E0 != null) {
          ResolveExpression(e.E0, resolutionContext);
          AddXConstraint(e.E0.tok, "ContainerIndex", e.Seq.Type, e.E0.Type, "incorrect type for selection into {0} (got {1})");
          ConstrainSubtypeRelation(NewIntegerBasedProxy(e.tok), e.E0.Type, e.E0, "wrong number of indices for multi-selection");
        }
        if (e.E1 != null) {
          ResolveExpression(e.E1, resolutionContext);
          AddXConstraint(e.E1.tok, "ContainerIndex", e.Seq.Type, e.E1.Type, "incorrect type for selection into {0} (got {1})");
          ConstrainSubtypeRelation(NewIntegerBasedProxy(e.tok), e.E1.Type, e.E1, "wrong number of indices for multi-selection");
        }
        var resultType = new InferredTypeProxy() { KeepConstraints = true };
        e.Type = new SeqType(resultType);
        AddXConstraint(e.tok, "ContainerResult", e.Seq.Type, resultType, "multi-selection has type {0} which is incompatible with expected type {1}");
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
        CheckCoCalls(e.ResolvedExpression, destructionLevel, coContext, coCandidates);
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
      } else if (expr is NestedMatchExpr) {
        var e = (NestedMatchExpr)expr;
        return GuaranteedCoCtorsAux(e.ResolvedExpression);

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

      public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
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

    public Resolver resolver;

    public SubsetConstraintGhostChecker(Resolver resolver) {
      this.resolver = resolver;
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
                ExpressionTester.CheckIsCompilable(this.resolver, errorCollector, constraint,
                  new CodeContextWrapper(subsetTypeDecl, true));
                if (errorCollector.Collected) {
                  finalToken = new NestedToken(finalToken, errorCollector.FirstCollectedToken,
                    "The constraint is not compilable because " + errorCollector.FirstCollectedMessage
                  );
                }
              }
              this.resolver.Reporter.Error(MessageSource.Resolver, finalToken,
                $"{boundVar.Type} is a subset type and its constraint is not compilable, hence it cannot yet be used as the type of a bound variable in {what}.");
            }
          }
        }
      }
      return base.Traverse(e, field, parent);
    }
  }
}
