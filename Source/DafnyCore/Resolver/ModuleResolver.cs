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
using JetBrains.Annotations;
using Microsoft.Boogie;
using static Microsoft.Dafny.ResolutionErrors;

namespace Microsoft.Dafny {
  public record ModuleResolutionResult(
    ModuleDecl ResolvedDeclaration,
    BatchErrorReporter ErrorReporter,
    Dictionary<ModuleDefinition, ModuleSignature> Signatures,
    Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> ClassMembers
    );

  public interface ICanResolveNewAndOld {
    void GenResolve(INewOrOldResolver resolver, ResolutionContext context);
  }

  interface ICanResolve {
    void Resolve(ModuleResolver resolver, ResolutionContext context);
  }

  public enum FrameExpressionUse { Reads, Modifies, Unchanged }

  public partial class ModuleResolver : INewOrOldResolver {
    public ProgramResolver ProgramResolver { get; }
    public DafnyOptions Options { get; }
    public readonly SystemModuleManager SystemModuleManager;

    public ErrorReporter reporter;
    public ModuleSignature moduleInfo = null;

    public ErrorReporter Reporter => reporter;
    public Scope<IVariable> Scope => scope;

    public List<TypeConstraint.ErrorMsg> TypeConstraintErrorsToBeReported { get; } = new();

    private bool RevealedInScope(Declaration d) {
      Contract.Requires(d != null);
      Contract.Requires(moduleInfo != null);
      Contract.Requires(moduleInfo.VisibilityScope != null);

      return d.IsRevealedInScope(moduleInfo.VisibilityScope);
    }

    internal bool VisibleInScope(Declaration d) {
      Contract.Requires(d != null);
      Contract.Requires(moduleInfo != null);
      Contract.Requires(moduleInfo.VisibilityScope != null);

      return d.IsVisibleInScope(moduleInfo.VisibilityScope);
    }

    public string FreshTempVarName(string prefix, ICodeContext context) {
      var gen = context.CodeGenIdGenerator;
      var freshTempVarName = gen.FreshId(prefix);
      return freshTempVarName;
    }

    public readonly HashSet<RevealableTypeDecl> revealableTypes = new();
    //types that have been seen by the resolver - used for constraining type inference during exports

    public Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> moduleClassMembers = new();

    public void AddClassMembers(TopLevelDeclWithMembers key, Dictionary<string, MemberDecl> members) {
      moduleClassMembers[key] = members;
    }

    public Dictionary<string, MemberDecl> GetClassMembers(TopLevelDeclWithMembers key) {
      if (moduleClassMembers.TryGetValue(key, out var result)) {
        return result;
      }
      return ProgramResolver.GetClassMembers(key);
    }

    private Dictionary<TypeParameter, Type> SelfTypeSubstitution;

    public ModuleResolver(ProgramResolver programResolver, DafnyOptions options) {
      this.ProgramResolver = programResolver;
      Options = options;

      allTypeParameters = new Scope<TypeParameter>(Options);
      scope = new Scope<IVariable>(Options);
      EnclosingStatementLabels = new Scope<Statement>(Options);
      DominatingStatementLabels = new Scope<Label>(Options);

      SystemModuleManager = programResolver.SystemModuleManager;
      reporter = new BatchErrorReporter(Options);
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(SystemModuleManager != null);
    }

    public void FillInAdditionalInformation(ModuleDefinition module) {
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

    public void FillInDecreasesClauses(ModuleDefinition module) {
      // fill in default decreases clauses:  for functions and methods, and for loops
      new InferDecreasesClause(this).FillInDefaultDecreasesClauses(module);

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

    public void ComputeIsRecursiveBit(CompilationData compilation, ModuleDefinition module, IEnumerable<IRewriter> rewriters) {
      // compute IsRecursive bit for mutually recursive functions and methods
      foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls)) {
        if (clbl is Function) {
          var fn = (Function)clbl;
          if (!fn.IsRecursive) {
            // note, self-recursion has already been determined
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

    public ModuleResolutionResult ResolveModuleDeclaration(CompilationData compilation, ModuleDecl decl) {
      Dictionary<ModuleDefinition, ModuleSignature> signatures = new();
      if (decl is LiteralModuleDecl literalModuleDecl) {
        var signature = literalModuleDecl.Resolve(this, compilation);
        signatures[literalModuleDecl.ModuleDef] = signature;
      } else if (decl is AliasModuleDecl alias) {
        if (ResolveExport(alias, alias.EnclosingModuleDefinition, alias.TargetQId, alias.Exports, out var p, reporter)) {
          alias.Signature ??= p;
        } else {
          alias.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
        }
      } else if (decl is AbstractModuleDecl abs) {
        if (ResolveExport(abs, abs.EnclosingModuleDefinition, abs.QId, abs.Exports, out var originalSignature, reporter)) {
          abs.OriginalSignature = originalSignature;
          abs.Signature = MakeAbstractSignature(originalSignature, abs.FullSanitizedName, abs.Height, signatures);
        } else {
          abs.Signature = new ModuleSignature(); // there was an error, give it a valid but empty signature
        }
      } else if (decl is ModuleExportDecl) {
      } else {
        Contract.Assert(false); // Unknown kind of ModuleDecl
      }

      return new ModuleResolutionResult(decl, (BatchErrorReporter)reporter, signatures, moduleClassMembers);
    }

    // Resolve the exports and detect cycles.
    public void ResolveModuleExport(LiteralModuleDecl literalDecl, ModuleSignature sig) {
      ModuleDefinition m = literalDecl.ModuleDef;
      literalDecl.DefaultExport = sig;
      Graph<ModuleExportDecl> exportDependencies = new Graph<ModuleExportDecl>();
      foreach (TopLevelDecl toplevel in m.TopLevelDecls) {
        if (toplevel is ModuleExportDecl exportDecl) {
          exportDependencies.AddVertex(exportDecl);
          foreach (IOrigin s in exportDecl.Extends) {
            if (sig.ExportSets.TryGetValue(s.val, out var extend)) {
              exportDecl.ExtendDecls.Add(extend);
              exportDependencies.AddEdge(exportDecl, extend);
            } else {
              reporter.Error(MessageSource.Resolver, s, s.val + " must be an export of " + m.Name + " to be extended");
            }
          }
        }
      }

      // detect cycles in the extend
      var cycleError = false;
      foreach (var cycle in exportDependencies.AllCycles()) {
        ReportCycleError(reporter, cycle, m => m.Tok, m => m.Name, "module export contains a cycle");
        cycleError = true;
      }

      if (cycleError) {
        return;
      } // give up on trying to resolve anything else

      // fill in the exports for the extends.
      List<ModuleExportDecl> sortedExportDecls = exportDependencies.TopologicallySortedComponents();
      ModuleExportDecl defaultExport = null;

      sig.TopLevels.TryGetValue("_default", out var defaultClass);
      Contract.Assert(defaultClass is DefaultClassDecl);
      defaultClass.AddVisibilityScope(m.VisibilityScope, true);

      foreach (var exportDecl in sortedExportDecls) {

        defaultClass.AddVisibilityScope(exportDecl.ThisScope, true);

        foreach (var eexports in exportDecl.ExtendDecls.Select(e => e.Exports)) {
          exportDecl.Exports.AddRange(eexports);
        }

        if (exportDecl.ExtendDecls.Count == 0 && exportDecl.Exports.Count == 0) {
          // This is an empty export.  This is allowed, but unusual.  It could pop up, for example, if
          // someone temporary comments out everything that the export set provides/reveals.  However,
          // if the name of the export set coincides with something else that's declared at the top
          // level of the module, then this export declaration is more likely an error--the user probably
          // forgot the "provides" or "reveals" keyword.

          // Top-level functions and methods are actually recorded as members of the _default class.  We look up the
          // export-set name there.  If the export-set name happens to coincide with some other top-level declaration,
          // then an error will already have been produced ("duplicate name of top-level declaration").
          if (GetClassMembers((DefaultClassDecl)defaultClass)?.TryGetValue(exportDecl.Name, out var member) == true) {
            reporter.Warning(MessageSource.Resolver, ErrorRegistry.NoneId, exportDecl.Tok,
              "this export set is empty (did you perhaps forget the 'provides' or 'reveals' keyword?)");
          }
        }

        foreach (ExportSignature export in exportDecl.Exports) {

          // check to see if it is a datatype or a member or
          // static function or method in the enclosing module or its imports

          Declaration decl = null;
          string name = export.Id;

          if (export.ClassId != null) {
            if (!sig.TopLevels.TryGetValue(export.ClassId, out var cldecl)) {
              reporter.Error(MessageSource.Resolver, export.ClassIdTok, "'{0}' is not a top-level type declaration",
                export.ClassId);
              continue;
            }

            if (cldecl is ClassLikeDecl { NonNullTypeDecl: { } }) {
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
          } else if (sig.TopLevels.TryGetValue(name, out var tdecl)) {
            if (tdecl is ClassLikeDecl { NonNullTypeDecl: { } nn }) {
              // cldecl is a possibly-null type (syntactically given with a question mark at the end)
              reporter.Error(MessageSource.Resolver, export.Tok,
                export.Opaque
                  ? "Type '{1}' can only be revealed, not provided"
                  : "Types '{0}' and '{1}' are exported together, which is accomplished by revealing the name '{0}'",
                nn.Name, name);
              continue;
            }

            // Member of the enclosing module
            decl = tdecl;
          } else if (sig.StaticMembers.TryGetValue(name, out var member)) {
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
            nntd.AddVisibilityScope(exportDecl.ThisScope, export.Opaque);
            if (!export.Opaque) {
              nntd.Class.AddVisibilityScope(exportDecl.ThisScope, export.Opaque);
              // add the anonymous constructor, if any
              var anonymousConstructor = nntd.Class.Members.Find(mdecl => mdecl.Name == "_ctor");
              if (anonymousConstructor != null) {
                anonymousConstructor.AddVisibilityScope(exportDecl.ThisScope, false);
              }
            }
          } else {
            decl.AddVisibilityScope(exportDecl.ThisScope, export.Opaque);
          }
        }
      }

      foreach (ModuleExportDecl exportDecl in sortedExportDecls) {
        if (exportDecl.IsDefault) {
          if (defaultExport == null) {
            defaultExport = exportDecl;
          } else {
            reporter.Error(MessageSource.Resolver, m.Tok, "more than one default export set declared in module {0}",
              m.Name);
          }
        }

        // fill in export signature
        ModuleSignature signature = exportDecl.Signature;
        if (signature != null) {
          signature.ModuleDef = m;
        }

        foreach (var top in sig.TopLevels) {
          if (!top.Value.CanBeExported() || !top.Value.IsVisibleInScope(signature.VisibilityScope)) {
            continue;
          }

          signature.TopLevels.TryAdd(top.Key, top.Value);

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
          signature.StaticMembers.TryAdd(mem.Key, (MemberDecl)mem.Value);
        }
      }

      // set the default export set, if it exists
      if (defaultExport != null) {
        literalDecl.DefaultExport = defaultExport.Signature;
      } else if (sortedExportDecls.Count > 0) {
        literalDecl.DefaultExport = null;
      }

      // final pass to propagate visibility of exported imports
      var sigs = sortedExportDecls.Select(d => d.Signature).Append(sig);

      foreach (var s in sigs) {
        foreach (var decl in s.TopLevels) {
          if (decl.Value is ModuleDecl modDecl and not ModuleExportDecl) {
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

        if (e.Opaque && (decl is DatatypeDecl or TypeSynonymDecl or NewtypeDecl)) {
          // Datatypes and type synonyms are marked as _provided when they appear in any provided export.  If a
          // declaration is never provided, then either it isn't visible outside the module at all or its whole
          // definition is.  Datatype and type-synonym declarations undergo some inference from their definitions.
          // Such inference should not be done for provided declarations, since different views of the module
          // would then get different inferred properties.
          decl.Attributes = new Attributes("_provided", new List<Expression>(), decl.Attributes);
          reporter.Info(MessageSource.Resolver, decl.Tok, "{:_provided}");
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

    public void CheckModuleExportConsistency(CompilationData compilation, ModuleDefinition m) {
      //check for export consistency by resolving internal modules
      //this should be effect-free, as it only operates on clones

      var oldModuleInfo = moduleInfo;
      foreach (var exportDecl in m.TopLevelDecls.OfType<ModuleExportDecl>()) {

        var prevErrors = reporter.Count(ErrorLevel.Error);

        foreach (var export in exportDecl.Exports) {
          if (export.Decl is MemberDecl member) {
            // For classes and traits, the visibility test is performed on the corresponding non-null type
            var enclosingType = member.EnclosingClass is ClassLikeDecl cl && cl.NonNullTypeDecl != null
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
        var exportView = cloner.CloneModuleDefinition(m, m.EnclosingModule, m.NameNode);
        if (Options.DafnyPrintExportedViews.Contains(exportDecl.FullName)) {
          var wr = Options.OutputWriter;
          wr.WriteLine("/* ===== export set {0}", exportDecl.FullName);
          var pr = new Printer(wr, Options);
          pr.PrintTopLevelDecls(compilation, exportView.TopLevelDecls, 0, null);
          wr.WriteLine("*/");
        }

        if (reporter.Count(ErrorLevel.Error) != prevErrors) {
          continue;
        }

        reporter = new ErrorReporterWrapper(reporter,
          $"Raised while checking export set {exportDecl.Name}: ");
        var testSig = exportView.RegisterTopLevelDecls(this, true);
        exportView.Resolve(testSig, this, exportDecl.Name);
        var wasError = reporter.Count(ErrorLevel.Error) > 0;
        reporter = (BatchErrorReporter)((ErrorReporterWrapper)reporter).WrappedReporter;

        if (wasError) {
          reporter.Error(MessageSource.Resolver, exportDecl.Tok, "This export set is not consistent: {0}", exportDecl.Name);
        } else {
          exportDecl.EffectiveModule = exportView;
        }
      }

      moduleInfo = oldModuleInfo;
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
            if (infoValue is ClassLikeDecl) {
              var cd = (ClassLikeDecl)infoValue;
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

    public static void ResolveOpenedImports(ModuleSignature sig, ModuleDefinition moduleDef, ErrorReporter reporter, ModuleResolver resolver) {
      var declarations = sig.TopLevels.Values.ToList<TopLevelDecl>();
      var importedSigs = new HashSet<ModuleSignature>() { sig };

      var topLevelDeclReplacements = new List<TopLevelDecl>();
      foreach (var importDeclaration in declarations.OfType<ModuleDecl>().Where(d => d.Opened)) {
        ResolveOpenedImportsWorker(reporter, sig, moduleDef, importDeclaration, importedSigs, out var topLevelDeclReplacement);
        if (topLevelDeclReplacement != null) {
          topLevelDeclReplacements.Add(topLevelDeclReplacement);
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
          resolver.AddClassMembers(cl, cl.Members.ToDictionary(m => m.Name));
        }
      }
    }

    private static TopLevelDecl ResolveAlias(TopLevelDecl dd, ErrorReporter reporter) {
      while (dd is AliasModuleDecl amd) {
        dd = amd.TargetQId.ResolveTarget(reporter);
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
    private static void ResolveOpenedImportsWorker(ErrorReporter reporter, ModuleSignature importerSignature, ModuleDefinition importer,
      ModuleDecl import, ISet<ModuleSignature> importedSigs,
      out TopLevelDecl topLevelDeclReplacement) {

      topLevelDeclReplacement = null;
      var importSignature = GetSignatureExt(import.AccessibleSignature(false));

      if (!importedSigs.Add(importSignature)) {
        return;
      }

      // top-level declarations:
      foreach (var kv in importSignature.TopLevels) {
        if (!kv.Value.CanBeExported()) {
          continue;
        }

        if (!importerSignature.TopLevels.TryGetValue(kv.Key, out var sameNameSymbolInImporter)) {
          importerSignature.TopLevels.Add(kv.Key, kv.Value);
        } else if (sameNameSymbolInImporter.EnclosingModuleDefinition == importer) {
          // declarations in the importing module take priority over opened-import declarations
          if (kv.Value.EnclosingModuleDefinition.DafnyName == kv.Key) {
            // As an exception to the rule, for an "import opened M" that contains a top-level symbol "M", unambiguously map the
            // name "M" to that top-level symbol in "sig". To achieve the "unambiguously" part, return the desired mapping to
            // the caller, and let the caller remap the symbol after all opened imports have been processed.
            topLevelDeclReplacement = kv.Value;
          }
        } else {
          bool unambiguous = false;
          // keep just one if they normalize to the same entity
          if (sameNameSymbolInImporter == kv.Value) {
            unambiguous = true;
          } else if (sameNameSymbolInImporter is ModuleDecl || kv.Value is ModuleDecl) {
            var dd = ResolveAlias(sameNameSymbolInImporter, reporter);
            var dk = ResolveAlias(kv.Value, reporter);
            unambiguous = dd == dk;
          } else {
            // It's okay if "d" and "kv.Value" denote the same type. This can happen, for example,
            // if both are type synonyms for "int".
            var scope = Type.GetScope();
            if (sameNameSymbolInImporter.IsVisibleInScope(scope) && kv.Value.IsVisibleInScope(scope)) {
              var dType = UserDefinedType.FromTopLevelDecl(sameNameSymbolInImporter.Tok, sameNameSymbolInImporter);
              var vType = UserDefinedType.FromTopLevelDecl(kv.Value.Tok, kv.Value);
              unambiguous = dType.Equals(vType, true);
            }
          }
          if (!unambiguous) {
            importerSignature.TopLevels[kv.Key] = AmbiguousTopLevelDecl.Create(importer, sameNameSymbolInImporter, kv.Value);
          }
        }
      }

      // constructors:
      foreach (var kv in importSignature.Ctors) {
        if (importerSignature.Ctors.TryGetValue(kv.Key, out var pair)) {
          // The same ctor can be imported from two different imports (e.g "diamond" imports), in which case,
          // they are not duplicates.
          if (!ReferenceEquals(kv.Value.Item1, pair.Item1)) {
            // mark it as a duplicate
            importerSignature.Ctors[kv.Key] = new Tuple<DatatypeCtor, bool>(pair.Item1, true);
          }
        } else {
          // add new
          importerSignature.Ctors.Add(kv.Key, kv.Value);
        }
      }

      // static members:
      foreach (var kv in importSignature.StaticMembers) {
        if (!kv.Value.CanBeExported()) {
          continue;
        }

        if (importerSignature.StaticMembers.TryGetValue(kv.Key, out var md)) {
          importerSignature.StaticMembers[kv.Key] = AmbiguousMemberDecl.Create(importer, md, kv.Value);
        } else {
          // add new
          importerSignature.StaticMembers.Add(kv.Key, kv.Value);
        }
      }
    }

    public void RegisterByMethod(Function f, TopLevelDeclWithMembers cl) {
      Contract.Requires(f != null && f.ByMethodBody != null);

      var tok = f.ByMethodTok;
      var resultVar = f.Result ?? new Formal(tok, "#result", f.ResultType, false, false, null);
      var r = Expression.CreateIdentExpr(resultVar);
      // To construct the receiver, we want to know if the function is static or instance. That information is ordinarily computed
      // by f.IsStatic, which looks at f.HasStaticKeyword and f.EnclosingClass. However, at this time, f.EnclosingClass hasn't yet
      // been set. Instead, we compute here directly from f.HasStaticKeyword and "cl".
      var isStatic = f.HasStaticKeyword || cl is DefaultClassDecl;
      var receiver = isStatic ? (Expression)new StaticReceiverExpr(tok, cl, true) : new ImplicitThisExpr(tok);
      var fn = new ApplySuffix(tok, null,
        new ExprDotName(tok, receiver, f.NameNode, f.TypeArgs.ConvertAll(typeParameter => (Type)new UserDefinedType(f.Tok, typeParameter))),
        new ActualBindings(f.Ins.ConvertAll(Expression.CreateIdentExpr)).ArgumentBindings,
        Token.NoToken);
      var post = new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, r, fn));
      Specification<FrameExpression> reads;
      if (Options.Get(Method.ReadsClausesOnMethods)) {
        // If f.Reads is empty, replace it with an explicit `reads {}` so that we don't replace that
        // with the default `reads *` for methods later.
        // Alternatively, we could have a flag similar to InferredDecreases to distinguish between
        // "not given" and "explicitly empty".
        reads = f.Reads;
        if (!reads.Expressions.Any()) {
          reads = new Specification<FrameExpression>();
          var emptySet = new SetDisplayExpr(tok, true, new List<Expression>());
          reads.Expressions.Add(new FrameExpression(tok, emptySet, null));
        }
      } else {
        reads = new Specification<FrameExpression>();
      }

      var method = new Method(f.Origin.MakeAutoGenerated(), new Name(new AutoGeneratedOrigin(f.NameNode.Tok)), f.HasStaticKeyword, false, f.TypeArgs,
        f.Ins, new List<Formal>() { resultVar },
        f.Req, reads, new Specification<FrameExpression>(new List<FrameExpression>(), null), new List<AttributedExpression>() { post }, f.Decreases,
        f.ByMethodBody, f.Attributes, null, true);
      Contract.Assert(f.ByMethodDecl == null);
      method.InheritVisibility(f);
      method.FunctionFromWhichThisIsByMethodDecl = f;
      f.ByMethodDecl = method;
    }

    private ModuleSignature MakeAbstractSignature(ModuleSignature origin, string name, int height,
      Dictionary<ModuleDefinition, ModuleSignature> moduleSignatures) {
      Contract.Requires(origin != null);
      Contract.Requires(name != null);
      Contract.Requires(moduleSignatures != null);
      var errCount = reporter.Count(ErrorLevel.Error);

      var module = new ModuleDefinition(SourceOrigin.NoToken, new Name(name + ".Abs"), new List<IOrigin>(), ModuleKindEnum.Abstract, true, null, null, null);
      module.Height = height;
      foreach (var kv in origin.TopLevels) {
        if (!(kv.Value is NonNullTypeDecl or DefaultClassDecl)) {
          var clone = CloneDeclarationForAbstractSignature(origin.VisibilityScope, kv.Value, module, moduleSignatures, name);
          module.SourceDecls.Add(clone);
        }
      }

      var defaultClassDecl = new DefaultClassDecl(module, origin.StaticMembers.Values.ToList());
      module.DefaultClass = (DefaultClassDecl)CloneDeclarationForAbstractSignature(origin.VisibilityScope, defaultClassDecl, module, moduleSignatures, name);

      var sig = module.RegisterTopLevelDecls(this, true);
      sig.Refines = origin.Refines;
      sig.IsAbstract = origin.IsAbstract;
      moduleSignatures.Add(module, sig);

      var good = module.Resolve(sig, this);
      if (good && reporter.Count(ErrorLevel.Error) == errCount) {
        module.SuccessfullyResolved = true;
      }

      /* A bug we ran into was that cloning done for abstract modules,
        did not clone the resolved field,
        so the .Flattened field of NestedMatchExpr was not set.
        Also, rewriters.PostResolve was not run, so .Flattened was not set after cloning
        which led to a crash during Boogie generation.
       
        Cloning with resolved fields is not an option, 
        because then internal references of the cloned code can point to the old code.
       
        I(keyboardDrummer) think it would be better altogether if no cloning was done for abstract modules,
        But until that happens here is code that explicitly calls MatchFlattener which sets .Flattened
        Alternatively, we could call all the rewriter.PostResolve methods
      */

      new MatchFlattener(reporter).PostResolve(module);

      return sig;
    }

    TopLevelDecl CloneDeclarationForAbstractSignature(VisibilityScope scope, TopLevelDecl d, ModuleDefinition newParent,
      Dictionary<ModuleDefinition, ModuleSignature> mods, string name) {
      Contract.Requires(d != null);
      Contract.Requires(newParent != null);
      Contract.Requires(mods != null);
      Contract.Requires(name != null);

      if (d is AbstractModuleDecl abstractDecl) {
        var sig = MakeAbstractSignature(abstractDecl.OriginalSignature, name + "." + abstractDecl.Name, abstractDecl.Height, mods);
        var result = new AbstractModuleDecl(abstractDecl.Options, abstractDecl.Origin, abstractDecl.QId, abstractDecl.NameNode,
          newParent, abstractDecl.Opened, abstractDecl.Exports, Guid.NewGuid()) {
          Signature = sig,
          OriginalSignature = abstractDecl.OriginalSignature
        };
        return result;
      } else {
        return new AbstractSignatureCloner(scope).CloneDeclaration(d, newParent);
      }
    }


    public bool ResolveExport(ModuleDecl alias, ModuleDefinition parent, ModuleQualifiedId qid,
      List<IOrigin> exports, out ModuleSignature p, ErrorReporter reporter) {
      Contract.Requires(qid != null);
      Contract.Requires(qid.Path.Count > 0);
      Contract.Requires(exports != null);

      ModuleDecl decl = qid.ResolveTarget(reporter);
      if (decl == null) {
        p = null;
        return false;
      }
      p = decl.Signature;
      if (exports.Count == 0) {
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
            reporter.Error(MessageSource.Resolver, qid.RootToken(), "no default export set declared in module: {0}", decl.Name);
            return false;
          }
          p = m.AccessibleSignature();
        }
      } else {
        ModuleExportDecl pp;
        if (decl.Signature.ExportSets.TryGetValue(exports[0].val, out pp)) {
          p = pp.AccessibleSignature();
        } else {
          reporter.Error(MessageSource.Resolver, exports[0], "no export set '{0}' in module '{1}'", exports[0].val, decl.Name);
          p = null;
          return false;
        }

        foreach (IOrigin export in exports.Skip(1)) {
          if (decl.Signature.ExportSets.TryGetValue(export.val, out pp)) {
            Contract.Assert(Object.ReferenceEquals(p.ModuleDef, pp.Signature.ModuleDef));
            ModuleSignature merged = MergeSignature(p, pp.Signature);
            merged.ModuleDef = pp.Signature.ModuleDef;
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

    public void RevealAllInScope(IEnumerable<TopLevelDecl> declarations, VisibilityScope scope) {
      foreach (TopLevelDecl d in declarations) {
        d.AddVisibilityScope(scope, false);
        if (d is TopLevelDeclWithMembers) {
          var cl = (TopLevelDeclWithMembers)d;
          foreach (var mem in cl.Members) {
            if (!mem.ScopeIsInherited) {
              mem.AddVisibilityScope(scope, false);
            }
          }
          var nnd = (cl as ClassLikeDecl)?.NonNullTypeDecl;
          if (nnd != null) {
            nnd.AddVisibilityScope(scope, false);
          }
        }
      }
    }

    public void ResolveTopLevelDecls_Signatures(ModuleDefinition def, ModuleSignature sig, List<TopLevelDecl> declarations,
      Graph<IndDatatypeDecl> datatypeDependencies, Graph<CoDatatypeDecl> codatatypeDependencies) {
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
          ResolveType(dd.Tok, dd.Rhs, dd, ResolveTypeOptionEnum.AllowPrefix, dd.TypeArgs);
          dd.Rhs.ForeachTypeComponent(ty => {
            var s = ty.AsRedirectingType;
            if (s != null && s != dd) {
              typeRedirectionDependencies.AddEdge(dd, s);
            }
          });
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          ResolveType(dd.Tok, dd.BaseType, dd, ResolveTypeOptionEnum.DontInfer, null);
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
          if (def.ModuleKind == ModuleKindEnum.Concrete && decl is AliasModuleDecl am && decl.Signature.IsAbstract) {
            reporter.Error(MessageSource.Resolver, am.TargetQId.RootToken(),
              "a compiled module ({0}) is not allowed to import an abstract module ({1})", def.Name, am.TargetQId.ToString());
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
        ReportCycleError(reporter, cycle, m => m.Tok, m => m.Name, "trait definitions contain a cycle");
      }
      if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
        // check that only reference types (classes and some traits) inherit from 'object'
        foreach (TopLevelDecl d in declarations.Where(d => d is TopLevelDeclWithMembers and not ClassLikeDecl)) {
          var nonReferenceTypeDecl = (TopLevelDeclWithMembers)d;
          foreach (var parentType in nonReferenceTypeDecl.ParentTraits.Where(t => t.IsRefType)) {
            reporter.Error(MessageSource.Resolver, parentType is UserDefinedType parentUdt ? parentUdt.Tok : nonReferenceTypeDecl.Tok,
              $"{nonReferenceTypeDecl.WhatKind} is not allowed to extend '{parentType}', because it is a reference type");
            break; // one error message per "decl" is enough
          }
        }
      }

      // Now that non-null types and their base types are in place, resolve the bounds of type parameters
      ResolveAllTypeParameterBounds(declarations);

      // perform acyclicity test on type synonyms
      foreach (var cycle in typeRedirectionDependencies.AllCycles()) {
        ReportCycleError(reporter, cycle, rtd => rtd.Tok, rtd => rtd.Name, "cycle among redirecting types (newtypes, subset types, type synonyms)");
      }
    }

    private void ResolveAllTypeParameterBounds(List<TopLevelDecl> declarations) {
      foreach (var decl in declarations) {
        allTypeParameters.PushMarker();
        ResolveTypeParameterBounds(decl.Tok, decl.TypeArgs, decl as ICodeContext ?? new NoContext(decl.EnclosingModuleDefinition));
        if (decl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
          foreach (var member in topLevelDeclWithMembers.Members) {
            if (member is Function function) {
              var ec = reporter.Count(ErrorLevel.Error);
              allTypeParameters.PushMarker();
              ResolveTypeParameterBounds(function.Tok, function.TypeArgs, function);
              allTypeParameters.PopMarker();
              if (reporter.Count(ErrorLevel.Error) == ec && function is ExtremePredicate { PrefixPredicate: { } prefixPredicate }) {
                allTypeParameters.PushMarker();
                ResolveTypeParameterBounds(prefixPredicate.Tok, prefixPredicate.TypeArgs, prefixPredicate);
                allTypeParameters.PopMarker();
              }
            } else if (member is Method m) {
              var ec = reporter.Count(ErrorLevel.Error);
              allTypeParameters.PushMarker();
              ResolveTypeParameterBounds(m.Tok, m.TypeArgs, m);
              allTypeParameters.PopMarker();
              if (reporter.Count(ErrorLevel.Error) == ec && m is ExtremeLemma { PrefixLemma: { } prefixLemma }) {
                allTypeParameters.PushMarker();
                ResolveTypeParameterBounds(prefixLemma.Tok, prefixLemma.TypeArgs, prefixLemma);
                allTypeParameters.PopMarker();
              }
            }
          }
        }
        allTypeParameters.PopMarker();
      }
    }

    /// <summary>
    /// This method pushes the typeParameters to "allTypeParameters" (reporting no errors for any duplicates) and then
    /// type checks the type-bound types of each type parameter.
    /// As a side effect, this method leaves "allTypeParameters" in the state after the pushes.
    /// </summary>
    void ResolveTypeParameterBounds(IOrigin tok, List<TypeParameter> typeParameters, ICodeContext context) {
      foreach (var typeParameter in typeParameters) {
        allTypeParameters.Push(typeParameter.Name, typeParameter);
      }
      foreach (var typeParameter in typeParameters) {
        foreach (var typeBound in typeParameter.TypeBounds) {
          var prevErrorCount = reporter.ErrorCount;
          ResolveType(tok, typeBound, context, ResolveTypeOptionEnum.DontInfer, null);
          if (reporter.ErrorCount == prevErrorCount && !typeBound.IsTraitType) {
            reporter.Error(MessageSource.Resolver, tok, $"type bound must be a trait or a subset type based on a trait (got {typeBound})");
          }
        }
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
      new NativeType("udoublelong", 0, new BigInteger(0x1_0000_0000) * new BigInteger(0x1_0000_0000) * new BigInteger(0x1_0000_0000) * new BigInteger(0x1_0000_0000), 128, NativeType.Selection.UDoubleLong),
      new NativeType("doublelong", new BigInteger(-0x8000_0000_0000_0000)* new BigInteger(0x1_0000_0000) * new BigInteger(0x1_0000_0000), new BigInteger(0x8000_0000_0000_0000)* new BigInteger(0x1_0000_0000) * new BigInteger(0x1_0000_0000), 0, NativeType.Selection.DoubleLong),
    };

    public void ResolveTopLevelDecls_Core(List<TopLevelDecl> declarations,
      Graph<IndDatatypeDecl> datatypeDependencies, Graph<CoDatatypeDecl> codatatypeDependencies,
      string moduleDescription, bool isAnExport) {

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

      if (Options.Get(CommonOptionBag.TypeSystemRefresh)) {
        // Resolve all names and infer types.
        PreTypeResolver.ResolveDeclarations(declarations, this);

        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          // Look for any under-specified pre-types, and fill in all .ResolvedOp fields.
          var u = new UnderspecificationDetector(this);
          u.Check(declarations);
        }

        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var preType2TypeVisitor = new PreTypeToTypeVisitor(SystemModuleManager);
          preType2TypeVisitor.VisitConstantsAndRedirectingTypes(declarations);
          preType2TypeVisitor.VisitDeclarations(declarations);
        }

        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var typeAdjustor = new TypeRefinementVisitor(moduleDescription, SystemModuleManager);
          typeAdjustor.VisitDeclarations(declarations);
          typeAdjustor.Solve(reporter, Options.Get(CommonOptionBag.NewTypeInferenceDebug));
        }

      } else {
        InheritMembers(declarations);

        // Resolve all names and infer types. These two are done together, because name resolution depends on having type information
        // and type inference depends on having resolved names.
        // The task is first performed for (the constraints of) newtype declarations, (the constraints of) subset type declarations, and
        // (the right-hand sides of) const declarations, because type resolution sometimes needs to know the base type of newtypes and subset types
        // and needs to know the type of const fields. Doing these declarations increases the chances the right information will be provided
        // in time.
        // Once the task is done for these newtype/subset-type/const parts, the task continues with everything else.
        ResolveNamesAndInferTypes(declarations, true);
        ResolveNamesAndInferTypes(declarations, false);
      }

      // Check that all types have been determined. During this process, also fill in all .ResolvedOp fields.
      // Note, in the type system refresh, it can happen that the under-specification detector above finds all pre-types to
      // be specified, whereas some (necessarily unused) type arguments are still underspecified. Such will be caught by the
      // CheckTypeInferenceVisitor. (But CheckTypeInferenceVisitor could, for the type system refresh, be modified to
      // not bother setting .ResolvedOp fields, since the under-specification detector above has already set those.)
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        var checkTypeInferenceVisitor = new CheckTypeInferenceVisitor(this);
        checkTypeInferenceVisitor.VisitDeclarations(declarations);
      }

      // Substitute for DefaultValueExpression's
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        FillInDefaultValueExpressions();
      }

      // ---------------------------------- Pass 1 ----------------------------------
      // This pass does the following:
      // * desugar functions used in reads clauses
      // * fills in "reads *" clauses on methods, when --reads-clauses-on-methods is used
      // * compute .BodySurrogate for body-less loops
      // * discovers bounds
      // * builds the module's call graph.
      // * compute and checks ghosts (this makes use of bounds discovery, as done above)
      // * for newtypes, figure out native types
      // * for datatypes, check that shared destructors are in agreement in ghost matters
      // * for methods, check that any reads clause is used correctly
      // * for functions and methods, determine tail recursion
      // ----------------------------------------------------------------------------

      // Discover bounds. These are needed later to determine if certain things are ghost or compiled,
      // and thus this should be done before building the call graph.
      // The BoundsDiscoveryVisitor also desugars FrameExpressions, so that bounds discovery can
      // apply to the desugared versions.
      // This pass also computes body surrogates for body-less loops, which is a bit like desugaring
      // such loops.
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        var boundsDiscoveryVisitor = new BoundsDiscoveryVisitor(this);
        boundsDiscoveryVisitor.VisitDeclarations(declarations);
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount && Options.Get(Method.ReadsClausesOnMethods)) {
        // Set the default of `reads *` if reads clauses on methods is enabled and this isn't a lemma.
        // Note that `reads *` is the right default for backwards-compatibility,
        // but we may want to infer a sensible default like decreases clauses instead in the future.
        foreach (var declaration in ModuleDefinition.AllCallables(declarations)) {
          if (declaration is Method { IsLemmaLike: false, Reads: { Expressions: var readsExpressions } } method &&
              !readsExpressions.Any()) {
            var star = new FrameExpression(method.Tok, new WildcardExpr(method.Tok) { Type = SystemModuleManager.ObjectSetType() }, null);
            readsExpressions.Add(star);
          }
        }
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        CallGraphBuilder.Build(declarations, reporter);
      }

      // The call graph hasn't been completely constructed, because it's missing the edges having to do with
      // extreme predicates/lemmas. However, figuring out whether or not constraints are compilable depends on
      // there being no cycles in the call graph. Therefore, we do an initial check for cycles at this time.
      var cycleErrorHasBeenReported = new HashSet<ICallable>();
      foreach (var decl in declarations) {
        if (decl is RedirectingTypeDecl dd) {
          CheckForCyclesAmongRedirectingTypes(dd, cycleErrorHasBeenReported);
        }
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        ComputeGhostInterestAndMisc(declarations);
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
        FillInPostConditionsAndBodiesOfPrefixLemmas(declarations);
      }

      // An inductive datatype is allowed to be defined as an empty type. For example, in
      //     predicate P(x: int) { false }
      //     type Subset = x: int | P(x) witness *
      //     datatype Record = Record(Subset)
      // Record is an empty type, because Subset is, since P(x) is always false. But if P(x)
      // was instead defined to be true for some x's, then Record would be nonempty. Determining whether or
      // not Record is empty goes well beyond the syntactic checks of the type system.
      //
      // However, if a datatype is empty because of some "obvious" cycle among datatype definitions, then
      // that is both detectable by syntactic checks and likely unintended by the programmer. Therefore,
      // we search for such type declarations and give error messages if something is found.
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        foreach (var dtd in declarations.ConvertAll(decl => decl as IndDatatypeDecl).Where(dtd => dtd != null && dtd.Ctors.Count != 0)) {
          if (AreThereAnyObviousSignsOfEmptiness(UserDefinedType.FromTopLevelDecl(dtd.Tok, dtd), new HashSet<IndDatatypeDecl>())) {
            reporter.Warning(MessageSource.Resolver, ResolutionErrors.ErrorId.r_empty_cyclic_datatype, dtd.Tok,
              $"because of cyclic dependencies among constructor argument types, no instances of datatype '{dtd.Name}' can be constructed");
          }
        }
      }

      // Perform the stratosphere check on inductive datatypes, and compute to what extent the inductive datatypes require equality support
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) { // because SccStratosphereCheck depends on subset-type/newtype base types being successfully resolved
        foreach (var dtd in datatypeDependencies.TopologicallySortedComponents()) {
          if (datatypeDependencies.GetSCCRepresentative(dtd) == dtd) {
            // do the following check once per SCC, so call it on each SCC representative
            SccStratosphereCheck(dtd, datatypeDependencies);
            DetermineEqualitySupport(dtd, datatypeDependencies);
          }
        }
      }

      // Set the SccRepr field of codatatypes
      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        foreach (var repr in codatatypeDependencies.TopologicallySortedComponents()) {
          foreach (var codt in codatatypeDependencies.GetSCC(repr)) {
            codt.SscRepr = repr;
          }
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
                reporter.Info(MessageSource.Resolver, c.CandidateCall.Tok, "co-recursive call");
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

        // Check that type arguments satisfy their required
        //   - type characteristics, and
        //   - type bounds
        TypeCharacteristicChecker.InferAndCheck(declarations, isAnExport, reporter);

        // Check that functions claiming to be abstemious really are, and check that 'older' parameters are used only when allowed
        foreach (var fn in ModuleDefinition.AllFunctions(declarations)) {
          new Abstemious(reporter).Check(fn);
          CheckOlderParameters(fn);
        }

        // Check that extreme predicates are not recursive with non-extreme-predicate functions (and only
        // with extreme predicates of the same polarity), and
        // check that greatest lemmas are not recursive with non-greatest-lemma methods.
        // Also, check that the constraints of newtypes/subset-types do not depend on the type itself.
        // And check that const initializers are not cyclic.
        foreach (var d in declarations) {
          if (d is TopLevelDeclWithMembers { Members: var members }) {
            foreach (var member in members) {
              if (member is ExtremePredicate) {
                var fn = (ExtremePredicate)member;
                // Check here for the presence of any 'ensures' clauses, which are not allowed (because we're not sure
                // of their soundness)
                fn.Req.ForEach(e => ExtremePredicateChecks(e.E, fn, CallingPosition.Positive));
                fn.Decreases.Expressions.ForEach(e => ExtremePredicateChecks(e, fn, CallingPosition.Positive));
                fn.Reads.Expressions.ForEach(e => ExtremePredicateChecks(e.E, fn, CallingPosition.Positive));
                if (fn.Ens.Count != 0) {
                  reporter.Error(MessageSource.Resolver, fn.Ens[0].E.Tok, "a {0} is not allowed to declare any ensures clause", member.WhatKind);
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
            CheckForCyclesAmongRedirectingTypes(dd, cycleErrorHasBeenReported);
          }
        }
      }

      // ---------------------------------- Pass 3 ----------------------------------
      // Further checks
      // ----------------------------------------------------------------------------

      foreach (TopLevelDecl d in declarations) {
        if (d is ClassDecl classDecl) {
          var classIsExtern = !Options.DisallowExterns && Attributes.Contains(classDecl.Attributes, "extern");
          if (Options.ForbidNondeterminism &&
              !classIsExtern &&
              !classDecl.Members.Exists(member => member is Constructor) &&
              classDecl.Members.Exists(member => member is Field && !(member is ConstantField { Rhs: not null }))) {
            // This check should be moved to the resolver once we have a language construct to indicate the type is imported
            // Instead of the extern attribute
            Reporter.Error(MessageSource.Resolver, GeneratorErrors.ErrorId.c_constructorless_class_forbidden,
              classDecl.Tok,
              "since fields are initialized arbitrarily, constructor-less classes are forbidden by the --enforce-determinism option");
          }
        }
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Check that type-parameter variance is respected in type definitions
        foreach (TopLevelDecl d in declarations) {
          if (d is ClassLikeDecl) {
            foreach (var tp in d.TypeArgs) {
              if (tp.Variance != TypeParameter.TPVariance.Non) {
                reporter.Error(MessageSource.Resolver, tp.Tok, "{0} declarations only support non-variant type parameters", d.WhatKind);
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
              ctor.Formals.ForEach(formal => CheckVariance(formal.Type, dd, TypeParameter.TPVariance.Co, false));
            }
          }

          if (d is TopLevelDeclWithMembers topLevelDeclWithMembers) {
            foreach (var parentTrait in topLevelDeclWithMembers.ParentTraits) {
              CheckVariance(parentTrait, topLevelDeclWithMembers, TypeParameter.TPVariance.Co, false);
            }
          }
        }
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Check that class constructors are called when required.
        new ObjectConstructorChecker(reporter).VisitDeclarations(declarations);
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        new HigherOrderHeapAllocationChecker(reporter).VisitDeclarations(declarations);
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        new HigherOrderHeapAllocationCheckerConstructor(reporter).VisitDeclarations(declarations);
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        new CheckMapRangeSupportsEquality(reporter).VisitDeclarations(declarations);
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Check that usage of "this" is restricted before "new;" in constructor bodies,
        // and that a class without any constructor only has fields with known initializers.
        // Also check that static fields (which are necessarily const) have initializers.
        var cdci = new CheckDividedConstructorInit_Visitor(reporter);
        foreach (var cl in ModuleDefinition.AllTypesWithMembers(declarations)) {
          // only reference types (classes and reference-type traits) are allowed to declare mutable fields
          if (cl is not ClassLikeDecl { IsReferenceTypeDecl: true }) {
            foreach (var member in cl.Members.Where(member => member is Field and not SpecialField)) {
              var traitHint = cl is TraitDecl ? " or declaring the trait with 'extends object'" : "";
              reporter.Error(MessageSource.Resolver, member,
                $"mutable fields are allowed only in reference types (consider declaring the field as a 'const'{traitHint})");
            }
          }

          if (cl is not ClassLikeDecl) {
            if (!isAnExport && cl.EnclosingModuleDefinition.ModuleKind == ModuleKindEnum.Concrete) {
              // non-reference, non-trait types (datatype, newtype, opaque) don't have constructors that can initialize fields
              foreach (var member in cl.Members) {
                if (member is ConstantField f && f.Rhs == null && !f.IsExtern(Options, out _, out _)) {
                  CheckIsOkayWithoutRHS(f, false);
                }
              }
            }
            continue;
          }
          if (cl is TraitDecl traitDecl) {
            if (!isAnExport && cl.EnclosingModuleDefinition.ModuleKind == ModuleKindEnum.Concrete) {
              // check for static consts, and check for instance fields in non-reference traits
              foreach (var member in cl.Members) {
                if (member is ConstantField f && f.Rhs == null && !f.IsExtern(Options, out _, out _)) {
                  if (f.IsStatic) {
                    CheckIsOkayWithoutRHS(f, false);
                  } else if (!traitDecl.IsReferenceTypeDecl) {
                    CheckIsOkayWithoutRHS(f, true);
                  }
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
              if (!isAnExport && cl.EnclosingModuleDefinition.ModuleKind == ModuleKindEnum.Concrete && f.Rhs == null && !f.IsExtern(Options, out _, out _)) {
                CheckIsOkayWithoutRHS(f, false);
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
              reporter.Error(MessageSource.Resolver, cl.Tok, "class '{0}' with fields without known initializers, like '{1}' of type '{2}', must declare a constructor",
                cl.Name, fieldWithoutKnownInitializer.Name, fieldWithoutKnownInitializer.Type.Subst(cl.ParentFormalTypeParametersToActuals));
            }
          }
        }
      }

      if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
        // Verifies that, in all compiled places, subset types in comprehensions have a compilable constraint
        new SubsetConstraintGhostChecker(this.Reporter).Traverse(declarations);
      }
    }

    /// <summary>
    /// Compute ghost interests, figure out native types, check agreement among datatype destructors, and determine tail calls.
    /// </summary>
    private void ComputeGhostInterestAndMisc(List<TopLevelDecl> declarations) {
      foreach (TopLevelDecl d in declarations) {
        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          iter.SubExpressions.ForEach(e => CheckExpression(e, this, iter));
          if (iter.Body != null) {
            CheckExpression(iter.Body, this, iter);
          }

        } else if (d is SubsetTypeDecl subsetTypeDecl) {
          Contract.Assert(subsetTypeDecl.Constraint != null);
          CheckExpression(subsetTypeDecl.Constraint, this, new CodeContextWrapper(subsetTypeDecl, true));

          if (subsetTypeDecl.Witness != null) {
            CheckExpression(subsetTypeDecl.Witness, this,
              new CodeContextWrapper(subsetTypeDecl, subsetTypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost));
            if (subsetTypeDecl.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
              var codeContext = new CodeContextWrapper(subsetTypeDecl, subsetTypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost);
              ExpressionTester.CheckIsCompilable(Options, this, subsetTypeDecl.Witness, codeContext);
            }
          }

        } else if (d is NewtypeDecl newtypeDecl) {
          if (newtypeDecl.Var != null) {
            Contract.Assert(newtypeDecl.Constraint != null);
            CheckExpression(newtypeDecl.Constraint, this, new CodeContextWrapper(newtypeDecl, true));
          }

          if (newtypeDecl.Witness != null) {
            CheckExpression(newtypeDecl.Witness, this, new CodeContextWrapper(newtypeDecl, newtypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost));
            if (newtypeDecl.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
              var codeContext = new CodeContextWrapper(newtypeDecl, newtypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost);
              ExpressionTester.CheckIsCompilable(Options, this, newtypeDecl.Witness, codeContext);
            }
          }

          new NativeTypeAnalysis(reporter).FigureOutNativeType(newtypeDecl, Options);

        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          foreach (var member in GetClassMembers(dd)!.Values) {
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
      }

      AnalyzeTypeConstraints.AssignConstraintIsCompilable(declarations, Options);

      // Now that we have filled in the .ConstraintIsCompilable field of all subset types and newtypes, we're ready to
      // visit iterator bodies and members (which will make calls to CheckIsCompilable).
      foreach (TopLevelDecl d in declarations) {
        if (d is IteratorDecl { Body: { } iterBody } iter) {
          ComputeGhostInterest(iter.Body, false, null, iter);
        }
        if (d is TopLevelDeclWithMembers cl) {
          ResolveClassMembers_Pass1(cl);
        }
      }
    }

    private void CheckForCyclesAmongRedirectingTypes(RedirectingTypeDecl dd, HashSet<ICallable> cycleErrorHasBeenReported) {
      var enclosingModule = dd.EnclosingModule;
      if (enclosingModule.CallGraph.GetSCCSize(dd) != 1) {
        var r = enclosingModule.CallGraph.GetSCCRepresentative(dd);
        if (cycleErrorHasBeenReported.Contains(r)) {
          // An error has already been reported for this cycle, so don't report another.
          // Note, the representative, "r", may itself not be a const.
        } else if (dd is NewtypeDecl or SubsetTypeDecl) {
          ReportCallGraphCycleError(dd, $"recursive constraint dependency involving a {dd.WhatKind}");
          cycleErrorHasBeenReported.Add(r);
        }
      }
    }

    private void FillInPostConditionsAndBodiesOfPrefixLemmas(List<TopLevelDecl> declarations) {
      foreach (var com in ModuleDefinition.AllExtremeLemmas(declarations)) {
        var prefixLemma = com.PrefixLemma;
        if (prefixLemma == null) {
          continue; // something went wrong during registration of the prefix lemma (probably a duplicated extreme lemma name)
        }

        var k = prefixLemma.Ins[0];
        var focalPredicates = new HashSet<ExtremePredicate>();
        var focalCodatatypeEquality = new HashSet<CoDatatypeDecl>();
        if (com is GreatestLemma) {
          // compute the postconditions of the prefix lemma
          Contract.Assume(prefixLemma.Ens.Count == 0); // these are not supposed to have been filled in before
          foreach (var p in com.Ens) {
            var coConclusions = new HashSet<Expression>();
            CollectFriendlyCallsInExtremeLemmaSpecification(p.E, true, coConclusions, true, com);
            var subst = new ExtremeLemmaSpecificationSubstituter(coConclusions, new IdentifierExpr(k.Tok, k.Name),
              this.reporter, true);
            var post = subst.CloneExpr(p.E);
            prefixLemma.Ens.Add(new AttributedExpression(post));
            foreach (var e in coConclusions) {
              if (e is FunctionCallExpr fce) {
                GreatestPredicate predicate = (GreatestPredicate)fce.Function;
                focalPredicates.Add(predicate);
                // For every focal predicate P in S, add to S all greatest predicates in the same strongly connected
                // component (in the call graph) as P
                foreach (var node in predicate.EnclosingClass.EnclosingModuleDefinition.CallGraph.GetSCC(predicate)) {
                  if (node is GreatestPredicate greatestPredicate) {
                    focalPredicates.Add(greatestPredicate);
                  }
                }
              } else {
                var binExpr = (BinaryExpr)e; // each "coConclusion" is either a FunctionCallExpr or a BinaryExpr
                focalCodatatypeEquality.Add(binExpr.E0.Type.AsCoDatatype ?? binExpr.E1.Type.AsCoDatatype);
              }
            }
          }
        } else {
          // compute the preconditions of the prefix lemma
          Contract.Assume(prefixLemma.Req.Count == 0); // these are not supposed to have been filled in before
          foreach (var p in com.Req) {
            var antecedents = new HashSet<Expression>();
            CollectFriendlyCallsInExtremeLemmaSpecification(p.E, true, antecedents, false, com);
            var subst = new ExtremeLemmaSpecificationSubstituter(antecedents, new IdentifierExpr(k.Tok, k.Name),
              this.reporter, false);
            var pre = subst.CloneExpr(p.E);
            prefixLemma.Req.Add(new AttributedExpression(pre, p.Label, null));
            foreach (var e in antecedents) {
              var fce = (FunctionCallExpr)e; // we expect "antecedents" to contain only FunctionCallExpr's
              LeastPredicate predicate = (LeastPredicate)fce.Function;
              focalPredicates.Add(predicate);
              // For every focal predicate P in S, add to S all least predicates in the same strongly connected
              // component (in the call graph) as P
              foreach (var node in predicate.EnclosingClass.EnclosingModuleDefinition.CallGraph.GetSCC(predicate)) {
                if (node is LeastPredicate leastPredicate) {
                  focalPredicates.Add(leastPredicate);
                }
              }
            }
          }
        }

        var focalCount = focalPredicates.Count + focalCodatatypeEquality.Count;
        if (focalCount == 0) {
          reporter.Info(MessageSource.Resolver, com.Tok, $"{com.PrefixLemma.Name} has no focal predicates");
        } else {
          var predicates = Util.Comma(focalPredicates, p => p.Name);
          var equalities = Util.Comma(focalCodatatypeEquality, decl => $"{decl.Name}.==");
          var focals = predicates + (predicates.Length != 0 && equalities.Length != 0 ? ", " : "") + equalities;
          reporter.Info(MessageSource.Resolver, com.Tok, $"{com.PrefixLemma.Name} with focal predicate{Util.Plural(focalCount)} {focals}");
        }
        // Compute the statement body of the prefix lemma
        Contract.Assume(prefixLemma.Body == null); // this is not supposed to have been filled in before
        if (com.Body != null) {
          var kMinusOne = new BinaryExpr(com.Tok, BinaryExpr.Opcode.Sub, new IdentifierExpr(k.Tok, k.Name),
            new LiteralExpr(com.Tok, 1));
          var subst = new ExtremeLemmaBodyCloner(com, kMinusOne, focalPredicates, focalCodatatypeEquality, this.reporter);
          var mainBody = subst.CloneBlockStmt(com.Body);
          Expression kk;
          Statement els;
          if (k.Type.IsBigOrdinalType) {
            kk = new MemberSelectExpr(k.Tok, new IdentifierExpr(k.Tok, k.Name), new Name("Offset"));
            // As an "else" branch, we add recursive calls for the limit case.  When automatic induction is on,
            // this get handled automatically, but we still want it in the case when automatic induction has been
            // turned off.
            //     forall k', params | k' < _k && Precondition {
            //       pp(k', params);
            //     }
            Contract.Assume(SystemModuleManager.ORDINAL_Offset != null); // should have been filled in earlier
            var kId = new IdentifierExpr(com.Tok, k);
            var kprimeVar = new BoundVar(com.Tok, "_k'", Type.BigOrdinal);
            var kprime = new IdentifierExpr(com.Tok, kprimeVar);
            var smaller = Expression.CreateLess(kprime, kId);

            var bvs = new List<BoundVar>(); // the following loop populates bvs with k', params
            var substMap = new Dictionary<IVariable, Expression>();
            foreach (var inFormal in prefixLemma.Ins) {
              if (inFormal == k) {
                bvs.Add(kprimeVar);
                substMap.Add(k, kprime);
              } else {
                var bv = new BoundVar(inFormal.Tok, inFormal.Name, inFormal.Type);
                bvs.Add(bv);
                substMap.Add(inFormal, new IdentifierExpr(com.Tok, bv));
              }
            }

            prefixLemma.RecursiveCallParameters(com.Tok, prefixLemma.TypeArgs, prefixLemma.Ins, null,
              substMap, out var recursiveCallReceiver, out var recursiveCallArgs);
            var methodSel = new MemberSelectExpr(com.Tok, recursiveCallReceiver, prefixLemma.NameNode);
            methodSel.Member = prefixLemma; // resolve here
            methodSel.TypeApplicationAtEnclosingClass =
              prefixLemma.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.Tok, tp));
            methodSel.TypeApplicationJustMember =
              prefixLemma.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.Tok, tp));
            methodSel.Type = new InferredTypeProxy();
            var recursiveCall = new CallStmt(com.Origin, new List<Expression>(), methodSel,
              recursiveCallArgs.ConvertAll(e => new ActualBinding(null, e)));
            recursiveCall.IsGhost = prefixLemma.IsGhost; // resolve here

            var range = smaller; // The range will be strengthened later with the call's precondition, substituted
            // appropriately (which can only be done once the precondition has been resolved).
            var attrs = new Attributes("_autorequires", new List<Expression>(), null);
#if VERIFY_CORRECTNESS_OF_TRANSLATION_FORALL_STATEMENT_RANGE
              // don't add the :_trustWellformed attribute
#else
            attrs = new Attributes("_trustWellformed", new List<Expression>(), attrs);
#endif
            attrs = new Attributes("auto_generated", new List<Expression>(), attrs);
            var forallBody = new BlockStmt(mainBody.Origin, new List<Statement>() { recursiveCall });
            var forallStmt = new ForallStmt(mainBody.Origin, bvs, attrs, range,
              new List<AttributedExpression>(), forallBody);
            els = new BlockStmt(mainBody.Origin, new List<Statement>() { forallStmt });
          } else {
            kk = new IdentifierExpr(k.Tok, k.Name);
            els = null;
          }

          var kPositive = new BinaryExpr(com.Tok, BinaryExpr.Opcode.Lt, new LiteralExpr(com.Tok, 0), kk);
          var condBody = new IfStmt(mainBody.Origin, false, kPositive, mainBody, els);
          prefixLemma.Body = new BlockStmt(mainBody.Origin, new List<Statement>() { condBody });
        }

        // The prefix lemma now has all its components, so it's finally time we resolve it
        currentClass = (TopLevelDeclWithMembers)prefixLemma.EnclosingClass;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(currentClass.TypeArgs, false, currentClass);
        ResolveTypeParameters(prefixLemma.TypeArgs, false, prefixLemma);
        prefixLemma.Resolve(this);
        allTypeParameters.PopMarker();
        currentClass = null;
        new CheckTypeInferenceVisitor(this).VisitMethod(prefixLemma);
        CallGraphBuilder.VisitMethod(prefixLemma, reporter);
        new BoundsDiscoveryVisitor(this).VisitMethod(prefixLemma);
      }
    }

    private void CheckIsOkayWithoutRHS(ConstantField f, bool giveNonReferenceTypeTraitHint) {
      var hint = giveNonReferenceTypeTraitHint && !f.IsStatic
        ? " (consider changing the field to be a function, or restricting the enclosing trait to be a reference type by adding 'extends object')"
        : "";
      var statik = f.IsStatic ? "static " : "";

      if (f.IsGhost && !f.Type.IsNonempty) {
        reporter.Error(MessageSource.Resolver, f.Tok,
          $"{statik}ghost const field '{f.Name}' of type '{f.Type}' (which may be empty) must give a defining value{hint}");
      } else if (!f.IsGhost && !f.Type.HasCompilableValue) {
        reporter.Error(MessageSource.Resolver, f.Tok,
          $"{statik}non-ghost const field '{f.Name}' of type '{f.Type}' (which does not have a default compiled value) must give a defining value{hint}");
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

            // check that any reads clause is used correctly
            var readsClausesOnMethodsEnabled = Options.Get(Method.ReadsClausesOnMethods);
            foreach (FrameExpression fe in method.Reads.Expressions) {
              if (method.IsLemmaLike) {
                reporter.Error(MessageSource.Resolver, fe.Tok,
                  "{0}s are not allowed to have reads clauses (they are allowed to read all memory locations)", method.WhatKind);
              } else if (!readsClausesOnMethodsEnabled) {
                reporter.Error(MessageSource.Resolver, fe.Tok,
                  "reads clauses on methods are forbidden without the command-line flag `--reads-clauses-on-methods`");
              } else if (method.IsGhost) {
                DisallowNonGhostFieldSpecifiers(fe);
              }
            }

            // check that any modifies clause is used correctly
            foreach (FrameExpression fe in method.Mod.Expressions) {
              if (method.IsLemmaLike) {
                reporter.Error(MessageSource.Resolver, fe.Tok, "{0}s are not allowed to have modifies clauses", method.WhatKind);
              } else if (method.IsGhost) {
                DisallowNonGhostFieldSpecifiers(fe);
              }
            }

          } else if (member is Function function) {
            CheckForUnnecessaryEqualitySupportDeclarations(function, function.TypeArgs);
            CheckParameterDefaultValuesAreCompilable(function.Ins, function);
            if (function.ByMethodBody == null) {
              if (!function.IsGhost && function.Body != null) {
                ExpressionTester.CheckIsCompilable(Options, this, function.Body, function);
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
                Contract.Assert(reporter.HasErrors);
              }
            }

          } else if (member is ConstantField field && field.Rhs != null && !field.IsGhost) {
            ExpressionTester.CheckIsCompilable(Options, this, field.Rhs, field);
          }

          if (prevErrCnt == reporter.Count(ErrorLevel.Error) && member is ICodeContext) {
            member.SubExpressions.ForEach(e => CheckExpression(e, this, (ICodeContext)member));
          }
        }
      }
    }

    void CheckForUnnecessaryEqualitySupportDeclarations(MemberDecl member, List<TypeParameter> typeParameters) {
      if (member.IsGhost) {
        foreach (var p in typeParameters.Where(p => p.SupportsEquality)) {
          reporter.Warning(MessageSource.Resolver, ErrorRegistry.NoneId, p.Tok,
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
          ExpressionTester.CheckIsCompilable(Options, this, formal.DefaultValue, codeContext);
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
      ReportCycleError(reporter, scc, c => c.Tok, c => c.NameRelativeToModule, msg);
    }

    public static void ReportCycleError<X>(ErrorReporter reporter, List<X> cycle, Func<X, IOrigin> toTok, Func<X, string> toString, string msg) {
      Contract.Requires(cycle != null);
      Contract.Requires(cycle.Count != 0);
      Contract.Requires(toTok != null);
      Contract.Requires(toString != null);
      Contract.Requires(msg != null);

      var start = cycle[0];
      var cy = Util.Comma(" -> ", cycle, toString);
      reporter.Error(MessageSource.Resolver, toTok(start), $"{msg}: {cy} -> {toString(start)}");
    }

    /// <summary>
    /// Check that the 'older' modifier on parameters is used correctly and report any errors of the contrary.
    /// </summary>
    void CheckOlderParameters(Function f) {
      Contract.Requires(f != null);

      if (!f.ResultType.IsBoolType || f is PrefixPredicate || f is ExtremePredicate) {
        // parameters are not allowed to be marked 'older'
        foreach (var formal in f.Ins) {
          if (formal.IsOlder) {
            reporter.Error(MessageSource.Resolver, formal.Tok, "only predicates and two-state predicates are allowed 'older' parameters");
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
    void CheckExpression(Expression expr, ModuleResolver resolver, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Requires(resolver != null);
      Contract.Requires(codeContext != null);
      var v = new CheckLocalityVisitor(resolver, codeContext);
      v.Visit(expr);
    }
    /// <summary>
    /// This method computes ghost interests in the statement portion of StmtExpr's and
    /// checks for hint restrictions in any CalcStmt. In any ghost context, it also
    /// changes the bound variables of all let- and let-such-that expressions to ghost.
    /// It also performs substitutions in DefaultValueExpression's.
    /// </summary>
    void CheckExpression(Statement stmt, ModuleResolver resolver, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolver != null);
      Contract.Requires(codeContext != null);
      var v = new CheckLocalityVisitor(resolver, codeContext);
      v.Visit(stmt);
    }

    #endregion

    void ExtremePredicateChecks(Expression expr, ExtremePredicate context, CallingPosition cp) {
      Contract.Requires(expr != null);
      Contract.Requires(context != null);
      var v = new ExtremePredicateChecks_Visitor(reporter, context);
      v.Visit(expr, cp);
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

    public void ComputeGhostInterest(Statement stmt, bool mustBeErasable, [CanBeNull] string proofContext, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);
      stmt.ResolveGhostness(this, Reporter, mustBeErasable, codeContext, proofContext,
        codeContext is Method, false);
    }

    class ReportOtherAdditionalInformation_Visitor : ResolverBottomUpVisitor {
      public ReportOtherAdditionalInformation_Visitor(ModuleResolver resolver)
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
                resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ensures " + Printer.ExprToString(resolver.Options, p));
              }
            }
          }
        }
      }
    }

    // ------------------------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------

    private TopLevelDeclWithMembers currentClass;
    public Scope<TypeParameter>/*!*/ allTypeParameters;
    public readonly Scope<IVariable>/*!*/ scope;

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
      foreach (var parentTrait in cl.ParentTraits) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(cl.Tok, parentTrait, new NoContext(cl.EnclosingModuleDefinition), ResolveTypeOptionEnum.DontInfer, null);
        if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
          var parentTypeToken = parentTrait is UserDefinedType parentTraitUdt ? parentTraitUdt.Tok : cl.Tok;

          var trait = parentTrait.UseInternalSynonym().IsInternalTypeSynonym ? null : (parentTrait as UserDefinedType)?.AsParentTraitDecl();
          if (trait != null) {
            // disallowing inheritance in multi module case
            bool termination = true;
            if (cl.EnclosingModuleDefinition == trait.EnclosingModuleDefinition ||
                trait.IsObjectTrait ||
                (Attributes.ContainsBool(trait.Attributes, "termination", ref termination) && !termination) ||
                Attributes.Contains(cl.Attributes, "AssumeCrossModuleTermination")) {
              // all is good (or the user takes responsibility for the lack of termination checking)
              if (!cl.ParentTraitHeads.Contains(trait)) {
                cl.ParentTraitHeads.Add(trait);
                parentRelation.AddEdge(cl, trait);
              }
            } else {
              reporter.Error(MessageSource.Resolver, parentTypeToken,
                $"{cl.WhatKind} '{cl.Name}' is in a different module than trait '{trait.FullName}'. A {cl.WhatKind} may only extend a trait " +
                $"in the same module, unless the parent trait is annotated with {{:termination false}} or the {cl.WhatKind} with @AssumeCrossModuleTermination.");
            }
          } else {
            reporter.Error(MessageSource.Resolver, parentTypeToken, $"a {cl.WhatKind} can only extend traits (found '{parentTrait}')");
          }
        }
      }
      allTypeParameters.PopMarker();
      currentClass = null;
    }

    void InheritMembers(List<TopLevelDecl> declarations) {
      // Register the trait members in the classes that inherit them
      foreach (var topLevelDeclWithMembers in declarations.OfType<TopLevelDeclWithMembers>()) {
        RegisterInheritedMembers(topLevelDeclWithMembers);
      }
    }

    /// <summary>
    /// This method idempotently fills in .InheritanceInformation, .ParentFormalTypeParametersToActuals, and the
    /// name->MemberDecl table for "cl" and the transitive parent traits of "cl". It also checks that every (transitive)
    /// parent trait is instantiated with the same type parameters
    /// The method assumes that all types along .ParentTraits have been successfully resolved and .ParentTraitHeads been filled in.
    ///
    /// The "basePreType" parameter is used only with the new resolver. It can be passed in a "null" to indicate that "cl" does not
    /// have a base type or that the given/inferred base type was not legal.
    /// </summary>
    public void RegisterInheritedMembers(TopLevelDeclWithMembers cl, [CanBeNull] DPreType basePreType = null) {
      Contract.Requires(cl != null);

      if (cl.ParentTypeInformation != null) {
        return;
      }
      cl.ParentTypeInformation = new TopLevelDeclWithMembers.InheritanceInformationClass();

      // populate .ParentFormalTypeParametersToActuals with the type arguments given to the base type (this applies only to newtype's)
      TopLevelDeclWithMembers baseTypeDecl = null;
      List<Type> baseTypeArguments = null;
      if (cl is NewtypeDecl newtypeDecl) {
        if (Options.Get(CommonOptionBag.TypeSystemRefresh)) {
          baseTypeDecl = basePreType?.Decl as TopLevelDeclWithMembers;
          baseTypeArguments = basePreType?.Arguments.ConvertAll(preType => PreType2TypeUtil.PreType2Type(preType, false, TypeParameter.TPVariance.Co));
        } else {
          // ignore any subset types, since they have no members and thus we don't need their type-parameter mappings
          var baseType = newtypeDecl.BaseType.NormalizeExpand();
          baseTypeArguments = baseType.TypeArgs;
          if (baseType is UserDefinedType { ResolvedClass: TopLevelDeclWithMembers topLevelDeclWithMembers }) {
            baseTypeDecl = topLevelDeclWithMembers;
          } else if (Options.Get(CommonOptionBag.GeneralNewtypes) || baseType.IsIntegerType || baseType.IsRealType) {
            baseTypeDecl = GetSystemValuetypeDecl(baseType);
          }
        }
        if (baseTypeDecl != null) {
          Contract.Assert(baseTypeArguments.Count == baseTypeDecl.TypeArgs.Count);
          for (var i = 0; i < baseTypeArguments.Count; i++) {
            cl.ParentFormalTypeParametersToActuals.Add(baseTypeDecl.TypeArgs[i], baseTypeArguments[i]);
          }
          RegisterInheritedMembers(baseTypeDecl);
        }
      }

      // populate .ParentTypeInformation and .ParentFormalTypeParametersToActuals for the immediate parent traits
      foreach (var tt in cl.ParentTraits) {
        var udt = (UserDefinedType)tt;
        var trait = (TraitDecl)((udt.ResolvedClass as NonNullTypeDecl)?.ViewAsClass ?? udt.ResolvedClass);
        cl.ParentTypeInformation.Record(trait, udt);
        Contract.Assert(trait.TypeArgs.Count == udt.TypeArgs.Count);
        for (var i = 0; i < trait.TypeArgs.Count; i++) {
          // there may be duplicate parent traits, which haven't been checked for yet, so add mapping only for the first occurrence of each type parameter
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
            reporter.Error(MessageSource.Resolver, cl.Tok,
              "duplicate trait parents with the same head type must also have the same type arguments; got {0}{1} and {2}{3}",
              ty, via0, group[i].Item1, via1);
          }
        }
      }

      // Update the name->MemberDecl table for the class. Report an error if the same name refers to more than one member,
      // except when such duplication is purely that one member, say X, is inherited and the other is an override of X.
      var inheritedMembers = new Dictionary<string, MemberDecl>();
      var membersWithErrors = new List<string>();
      if (baseTypeDecl != null) {
        AddToInheritedMembers(cl, baseTypeDecl, inheritedMembers, membersWithErrors);
      }
      foreach (var trait in cl.ParentTraitHeads) {
        AddToInheritedMembers(cl, trait, inheritedMembers, membersWithErrors);
      }
      // Incorporate the inherited members into the name->MemberDecl mapping of "cl"
      var members = GetClassMembers(cl);
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
      ProcessInheritedTraitMembers(cl, membersWithErrors);
    }

    private void AddToInheritedMembers(TopLevelDeclWithMembers cl, TopLevelDeclWithMembers baseOrParentTypeDecl,
      Dictionary<string, MemberDecl> inheritedMembers, List<string> membersWithErrors) {
      var members = GetClassMembers(baseOrParentTypeDecl)!;
      var sortedKeys = members.Keys.ToList();
      sortedKeys.Sort();
      foreach (var inheritedMemberName in sortedKeys) {
        var inheritedMember = members[inheritedMemberName];
        if (!inheritedMembers.TryGetValue(inheritedMember.Name, out var prevMember)) {
          // all good; record "inheritedMember" as an inherited member
          inheritedMembers.Add(inheritedMember.Name, inheritedMember);
        } else if (inheritedMember == prevMember) {
          // same member, inherited two different ways
        } else if (inheritedMember.Overrides(prevMember)) {
          // we're inheriting "prevMember" and "traitMember" from different parent traits, where "inheritedMember" is an override of "prevMember"
          Contract.Assert(inheritedMember.EnclosingClass != cl && prevMember.EnclosingClass != cl &&
                          inheritedMember.EnclosingClass != prevMember.EnclosingClass); // sanity checks
          // re-map "traitMember.Name" to point to the overriding member
          inheritedMembers[inheritedMember.Name] = inheritedMember;
        } else if (prevMember.Overrides(inheritedMember)) {
          // we're inheriting "prevMember" and "inheritedMember" from different parent traits, where "prevMember" is an override of "inheritedMember"
          Contract.Assert(inheritedMember.EnclosingClass != cl && prevMember.EnclosingClass != cl &&
                          inheritedMember.EnclosingClass != prevMember.EnclosingClass); // sanity checks
          // keep the mapping to "prevMember"
        } else {
          // "prevMember" and "inheritedMember" refer to different members (with the same name)
          membersWithErrors.Add(inheritedMember.Name);
          reporter.Error(MessageSource.Resolver, cl.Tok,
            $"{cl.WhatKindAndName} inherits a member named '{inheritedMember.Name}' from both " +
            $"{prevMember.EnclosingClass.WhatKindAndName} and {inheritedMember.EnclosingClass.WhatKindAndName}");
        }
      }
    }

    [CanBeNull]
    ValuetypeDecl GetSystemValuetypeDecl(Type type) {
      foreach (var systemTopLevelDecl in ProgramResolver.SystemModuleManager.SystemModule.SourceDecls.OfType<ValuetypeDecl>()) {
        if (systemTopLevelDecl.IsThisType(type)) {
          return systemTopLevelDecl;
        }
      }

      if (type.AsBitVectorType is { } bitvectorType) {
        // The declaration for this built-in bitvector type has not yet been added to SourceDecls. We create it here and add it.
        return AddBitvectorTypeDecl(bitvectorType.Name, bitvectorType.Width);
      }

      return null; // not present
    }

    public ValuetypeDecl AddBitvectorTypeDecl(string name, int width) {
      var bvDecl = new ValuetypeDecl(name, ProgramResolver.SystemModuleManager.SystemModule,
        t => t.AsBitVectorType is { Width: var w } && w == width,
        typeArgs => new BitvectorType(Options, width));
      AddRotateMember(bvDecl, "RotateLeft", width);
      AddRotateMember(bvDecl, "RotateRight", width);
      ProgramResolver.SystemModuleManager.SystemModule.SourceDecls.Add(bvDecl);
      var memberDictionary = bvDecl.Members.ToDictionary(member => member.Name, member => member);
      ProgramResolver.AddSystemClass(bvDecl, memberDictionary);
      return bvDecl;
    }

    private void AddRotateMember(ValuetypeDecl bitvectorTypeDecl, string name, int width) {
      var argumentType = ProgramResolver.SystemModuleManager.Nat();
      var formals = new List<Formal> {
        new Formal(Token.NoToken, "w", argumentType, true, false, null)
      };
      var resultType = new BitvectorType(Options, width);
      var rotateMember = new SpecialFunction(SourceOrigin.NoToken, name, ProgramResolver.SystemModuleManager.SystemModule, false, false,
        new List<TypeParameter>(), formals, resultType,
        new List<AttributedExpression>(), new Specification<FrameExpression>(), new List<AttributedExpression>(),
        new Specification<Expression>(new List<Expression>(), null), null, null, null) {
        EnclosingClass = bitvectorTypeDecl
      };
      rotateMember.AddVisibilityScope(ProgramResolver.SystemModuleManager.SystemModule.VisibilityScope, false);
      bitvectorTypeDecl.Members.Add(rotateMember);
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
            ResolveType(member.Tok, ((Field)member).Type, m, ResolveTypeOptionEnum.DontInfer, null);
          } else {
            // In the following, we pass in a NoContext, because any cycle formed by a redirecting-type constraints would have to
            // dereference the heap, and such constraints are not allowed to dereference the heap so an error will be produced
            // even if we don't detect this cycle.
            ResolveType(member.Tok, ((Field)member).Type, new NoContext(cl.EnclosingModuleDefinition), ResolveTypeOptionEnum.DontInfer, null);
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
    void ProcessInheritedTraitMembers(TopLevelDeclWithMembers cl, List<string> suppressNoImplErrorsForTheseMembers) {
      Contract.Requires(cl != null);
      Contract.Requires(cl.ParentTypeInformation != null);

      foreach (var member in GetClassMembers(cl).Values) {
        if (member is PrefixPredicate or PrefixLemma) {
          // these are handled with the corresponding extreme predicate/lemma
          continue;
        }
        if (member.EnclosingClass != cl) {
          if (member.EnclosingClass is not TraitDecl) {
            continue;
          }
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
            } else if (!suppressNoImplErrorsForTheseMembers.Contains(member.Name)) {
              reporter.Error(MessageSource.Resolver, cl.Tok, "{0} '{1}' does not implement trait {2} '{3}.{4}'", cl.WhatKind, cl.Name, member.WhatKind, member.EnclosingClass.Name, member.Name);
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
        if (trait is not TraitDecl) {
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"{traitMember.WhatKindAndName} is inherited from {trait.WhatKindAndName} and is not allowed to be re-declared in {cl.WhatKindAndName}");
        } else if (traitMember.IsStatic) {
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"static {traitMember.WhatKindAndName} is inherited from trait '{trait.Name}' and is not allowed to be re-declared");
        } else if (member.IsStatic) {
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"static member '{member.Name}' overrides non-static member in trait '{trait.Name}'");
        } else if (traitMember is Field) {
          // The class is not allowed to do anything with the field other than silently inherit it.
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"{traitMember.WhatKindAndName} is inherited from trait '{trait.Name}' and is not allowed to be re-declared");
        } else if ((traitMember as Function)?.Body != null || (traitMember as Method)?.Body != null) {
          // the overridden member is a fully defined function or method, so the class is not allowed to do anything with it other than silently inherit it
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"fully defined {traitMember.WhatKindAndName} is inherited from trait '{trait.Name}' and is not allowed to be re-declared");
        } else if (member is Method != traitMember is Method ||
                   member is Lemma != traitMember is Lemma ||
                   member is TwoStateLemma != traitMember is TwoStateLemma ||
                   member is LeastLemma != traitMember is LeastLemma ||
                   member is GreatestLemma != traitMember is GreatestLemma ||
                   member is Function != traitMember is Function ||
                   member is TwoStateFunction != traitMember is TwoStateFunction ||
                   member is LeastPredicate != traitMember is LeastPredicate ||
                   member is GreatestPredicate != traitMember is GreatestPredicate) {
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"{traitMember.WhatKindAndName} in '{trait.Name}' can only be overridden by a {traitMember.WhatKind} (got {member.WhatKind})");
        } else if (member.IsGhost != traitMember.IsGhost) {
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"overridden {traitMember.WhatKindAndName} in '{cl.Name}' has different ghost/compiled status than in trait '{trait.Name}'");
        } else if (!member.IsOpaque && traitMember.IsOpaque) {
          reporter.Error(MessageSource.Resolver, member.Tok,
            $"overridden {traitMember.WhatKindAndName} in '{cl.Name}' must be 'opaque' since the member is 'opaque' in trait '{trait.Name}'");
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
              reporter.Error(MessageSource.Resolver, classMethod.Tok,
                $"not allowed to override a terminating method with a possibly non-terminating method ('{classMethod.Name}')");
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

      var typeMap = CheckOverride_TypeParameters(nw.Tok, old.TypeArgs, nw.TypeArgs, nw.Name, "function", classTypeMap);
      if (nw is ExtremePredicate nwFix && old is ExtremePredicate oldFix && nwFix.KNat != oldFix.KNat) {
        reporter.Error(MessageSource.Resolver, nw,
          "the type of special parameter '_k' of {0} '{1}' ({2}) must be the same as in the overridden {0} ({3})",
          nw.WhatKind, nw.Name, nwFix.KNat ? "nat" : "ORDINAL", oldFix.KNat ? "nat" : "ORDINAL");
      }
      CheckOverride_ResolvedParameters(nw.Tok, old.Ins, nw.Ins, nw.Name, "function", "parameter", typeMap);
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
      var typeMap = CheckOverride_TypeParameters(nw.Tok, old.TypeArgs, nw.TypeArgs, nw.Name, "method", classTypeMap);
      if (nw is ExtremeLemma nwFix && old is ExtremeLemma oldFix && nwFix.KNat != oldFix.KNat) {
        reporter.Error(MessageSource.Resolver, nw,
          "the type of special parameter '_k' of {0} '{1}' ({2}) must be the same as in the overridden {0} ({3})",
          nw.WhatKind, nw.Name, nwFix.KNat ? "nat" : "ORDINAL", oldFix.KNat ? "nat" : "ORDINAL");
      }
      CheckOverride_ResolvedParameters(nw.Tok, old.Ins, nw.Ins, nw.Name, "method", "in-parameter", typeMap);
      CheckOverride_ResolvedParameters(nw.Tok, old.Outs, nw.Outs, nw.Name, "method", "out-parameter", typeMap);
    }

    private Dictionary<TypeParameter, Type> CheckOverride_TypeParameters(IOrigin tok, List<TypeParameter> old, List<TypeParameter> nw,
      string name, string thing, Dictionary<TypeParameter, Type> classTypeMap) {
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
        var checkNames = old.Concat(nw).Any(typeParameter => typeParameter.TypeBounds.Count != 0);
        for (var i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          typeMap.Add(o, new UserDefinedType(tok, n));
          if (checkNames && o.Name != n.Name) { // if checkNames is false, then just treat the parameters positionally.
            reporter.Error(MessageSource.Resolver, n.Tok,
              $"type parameters in this {thing} override are not allowed to be renamed from the names given in the the {thing} it overrides" +
              $" (expected '{o.Name}', got '{n.Name}')");
          } else {
            // Check type characteristics
            if (o.Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.InferredRequired &&
                o.Characteristics.EqualitySupport != n.Characteristics.EqualitySupport) {
              reporter.Error(MessageSource.Resolver, n.Tok, "type parameter '{0}' is not allowed to change the requirement of supporting equality",
                n.Name);
            }
            if (o.Characteristics.HasCompiledValue != n.Characteristics.HasCompiledValue) {
              reporter.Error(MessageSource.Resolver, n.Tok,
                "type parameter '{0}' is not allowed to change the requirement of supporting auto-initialization", n.Name);
            } else if (o.Characteristics.IsNonempty != n.Characteristics.IsNonempty) {
              reporter.Error(MessageSource.Resolver, n.Tok, "type parameter '{0}' is not allowed to change the requirement of being nonempty",
                n.Name);
            }
            if (o.Characteristics.ContainsNoReferenceTypes != n.Characteristics.ContainsNoReferenceTypes) {
              reporter.Error(MessageSource.Resolver, n.Tok, "type parameter '{0}' is not allowed to change the no-reference-type requirement",
                n.Name);
            }
          }
        }
        for (var i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          CheckOverride_TypeBounds(n.Tok, o, n, name, thing, typeMap);
        }
      }
      return typeMap;
    }

    void CheckOverride_TypeBounds(IOrigin tok, TypeParameter old, TypeParameter nw, string name, string thing, Dictionary<TypeParameter, Type> typeMap) {
      if (old.TypeBounds.Count != nw.TypeBounds.Count) {
        reporter.Error(MessageSource.Resolver, tok,
          $"type parameter '{nw.Name}' of {thing} '{name}' is declared with a different number of type bounds than in the " +
          $"{thing} it overrides (expected {old.TypeBounds.Count}, found {nw.TypeBounds.Count})");
        return;
      }

      for (var i = 0; i < old.TypeBounds.Count; i++) {
        var oldBound = old.TypeBounds[i].NormalizeExpandKeepConstraints();
        var newBound = nw.TypeBounds[i].NormalizeExpandKeepConstraints();
        if (!oldBound.Subst(typeMap).Equals(newBound, true)) {
          reporter.Error(MessageSource.Resolver, tok,
            $"type bound for type parameter '{nw.Name}' of {thing} '{name}' is different from the corresponding type bound of the " +
            $"corresponding type parameter of the {thing} it overrides (expected '{oldBound}', found '{newBound}')");
        }
      }
    }

    private void CheckOverride_ResolvedParameters(IOrigin tok, List<Formal> old, List<Formal> nw, string name, string thing, string parameterKind, Dictionary<TypeParameter, Type> typeMap) {
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
            reporter.Error(MessageSource.Resolver, n.Tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from non-ghost to ghost",
              parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            reporter.Error(MessageSource.Resolver, n.Tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from ghost to non-ghost",
              parameterKind, n.Name, thing, name);
          } else if (!o.IsOld && n.IsOld) {
            reporter.Error(MessageSource.Resolver, n.Tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from new to non-new",
              parameterKind, n.Name, thing, name);
          } else if (o.IsOld && !n.IsOld) {
            reporter.Error(MessageSource.Resolver, n.Tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from non-new to new",
              parameterKind, n.Name, thing, name);
          } else if (!o.IsOlder && n.IsOlder) {
            reporter.Error(MessageSource.Resolver, n.Tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from non-older to older",
              parameterKind, n.Name, thing, name);
          } else if (o.IsOlder && !n.IsOlder) {
            reporter.Error(MessageSource.Resolver, n.Tok, "{0} '{1}' of {2} {3} cannot be changed, compared to in the overridden {2}, from older to non-older",
              parameterKind, n.Name, thing, name);
          } else {
            var oo = o.Type.Subst(typeMap);
            if (!n.Type.Equals(oo, true)) {
              reporter.Error(MessageSource.Resolver, n.Tok,
                "the type of {0} '{1}' is different from the type of the corresponding {0} in trait {2} ('{3}' instead of '{4}')",
                parameterKind, n.Name, thing, n.Type, oo);
            }
          }
        }
      }
    }

    private bool AreThereAnyObviousSignsOfEmptiness(Type type, ISet<IndDatatypeDecl> beingVisited) {
      type = type.NormalizeExpandKeepConstraints(); // cut through type proxies, type synonyms, but being mindful of what's in scope
      if (type is UserDefinedType { ResolvedClass: var cl } udt) {
        Contract.Assert(cl != null);
        if (cl is SubsetTypeDecl subsetTypeDecl) {
          return AreThereAnyObviousSignsOfEmptiness(subsetTypeDecl.RhsWithArgument(udt.TypeArgs), beingVisited);
        } else if (cl is NewtypeDecl newtypeDecl) {
          return AreThereAnyObviousSignsOfEmptiness(newtypeDecl.RhsWithArgument(udt.TypeArgs), beingVisited);
        }
        if (cl is IndDatatypeDecl datatypeDecl) {
          if (beingVisited.Contains(datatypeDecl)) {
            // This datatype may be empty, but it's definitely empty if we consider only the constructors that have been visited
            // since AreThereAnyObviousSignsOfEmptiness was called from IsObviouslyEmpty.
            return true;
          }
          beingVisited.Add(datatypeDecl);
          var typeMap = TypeParameter.SubstitutionMap(datatypeDecl.TypeArgs, udt.TypeArgs);
          var isEmpty = datatypeDecl.Ctors.TrueForAll(ctor =>
            ctor.Formals.Exists(formal => AreThereAnyObviousSignsOfEmptiness(formal.Type.Subst(typeMap), beingVisited)));
          beingVisited.Remove(datatypeDecl);
          return isEmpty;
        }
      }

      return false;
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
            Contract.Assert(dt.GroundingCtor != null);  // should have been set by the successful call to ComputeGroundingCtor)
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
          return;
        }
      }
    }

    /// <summary>
    /// Check if the datatype has some constructor all whose argument types can be constructed.
    /// Returns 'true' and sets dt.GroundingCtor if that is the case.
    /// </summary>
    bool ComputeGroundingCtor(IndDatatypeDecl dt) {
      Contract.Requires(dt != null);
      Contract.Requires(dt.GroundingCtor == null);  // the intention is that this method be called only when GroundingCtor hasn't already been set
      Contract.Ensures(!Contract.Result<bool>() || dt.GroundingCtor != null);

      // Stated differently, check that there is some constructor where no argument type goes to the same stratum.
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
      } else if (cl is AbstractTypeDecl) {
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
      } else if (cl is TraitDecl traitDecl) {
        return traitDecl.IsReferenceTypeDecl; // null is a value for reference types
      } else if (cl is ClassDecl) {
        // null is a value for this possibly-null type
        return true;
      } else if (cl is ArrowTypeDecl) {
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
            if (arg.IsGhost || SurelyNeverSupportEquality(arg.Type)) {
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
            DetermineEqualitySupportType(arg.Type, ref thingsChanged);
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

    public static bool SurelyNeverSupportEqualityTypeParameters(IndDatatypeDecl.ES equalitySupport, List<TypeParameter> typeParams, List<Type> typeArgs) {
      return
        equalitySupport == IndDatatypeDecl.ES.Never ||
        (equalitySupport == IndDatatypeDecl.ES.ConsultTypeArguments &&
         typeArgs.Zip(typeParams).Any(tt =>
           tt.Item2.NecessaryForEqualitySupportOfSurroundingInductiveDatatype && SurelyNeverSupportEquality(tt.Item1)));
    }

    // If returns true, the given type never supports equality
    // If return false, then the type must support equality if type parameters support equality
    // It is unsound for a type to make this function return false when there is no type parameter
    // assignment that makes this type support equality
    public static bool SurelyNeverSupportEquality(Type type) {
      type = type.NormalizeExpand();
      return
        type.AsNewtype is { EqualitySupport: var equalitySupport, TypeArgs: var typeParams }
        && SurelyNeverSupportEqualityTypeParameters(equalitySupport, typeParams, type.TypeArgs)
        ||
        type.AsIndDatatype is { EqualitySupport: var equalitySupport2, TypeArgs: var typeParams2 }
        && SurelyNeverSupportEqualityTypeParameters(equalitySupport2, typeParams2, type.TypeArgs)
        ||
        type.IsCoDatatype || type.IsArrowType ||
        type.AsSeqType is { Arg: var argType } && SurelyNeverSupportEquality(argType) ||
        type.AsMapType is { Range: var rangeType } && SurelyNeverSupportEquality(rangeType);
    }

    public static void DetermineEqualitySupportType(Type type, ref bool thingsChanged) {
      if (type.AsTypeParameter is { } typeArg) {
        typeArg.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
        thingsChanged = true;
      } else if (type.Normalize() is UserDefinedType userDefinedType) {
        if (userDefinedType.ResolvedClass is TypeSynonymDeclBase typeSynonymDecl) {
          if (typeSynonymDecl.IsRevealedInScope(Type.GetScope())) {
            if (typeSynonymDecl.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Required) {
              return; // It's guaranteed that this type synonym requires equality
            }
            DetermineEqualitySupportType(typeSynonymDecl.RhsWithArgument(userDefinedType.TypeArgs), ref thingsChanged);
          }
        } else if (userDefinedType.ResolvedClass is NewtypeDecl newtypeDecl) {
          if (newtypeDecl.IsRevealedInScope(Type.GetScope())) {
            DetermineEqualitySupportType(newtypeDecl.RhsWithArgument(userDefinedType.TypeArgs), ref thingsChanged);
          }
        } else if (userDefinedType.ResolvedClass is IndDatatypeDecl otherDt) {
          if (otherDt.EqualitySupport == IndDatatypeDecl.ES.ConsultTypeArguments) {
            // datatype is in a different SCC
            var otherUdt = (UserDefinedType)type.NormalizeExpand();
            var i = 0;
            foreach (var otherTp in otherDt.TypeArgs) {
              if (otherTp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype) {
                var tp = otherUdt.TypeArgs[i].AsTypeParameter;
                if (tp != null) {
                  tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
                  thingsChanged = true;
                }
              }

              i++;
            }
          }
        }
      } else if (type.AsMapType is { } typeMap) {
        // A map type's Domain type is required to support equality (just like the argument type for sets and multisets), but
        // it is optional for the map type's Range type to support equality. Thus, we need to determine the equality support
        // for just the Range type.
        DetermineEqualitySupportType(typeMap.Range, ref thingsChanged);
      } else if (type.AsSeqType is { } typeSeq) {
        // Like the Range type of a map, it is optional for a sequence type's argument type to support equality. So, we make a call
        // to determine it.  
        DetermineEqualitySupportType(typeSeq.Arg, ref thingsChanged);
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
          return host is ClassLikeDecl { IsReferenceTypeDecl: true };
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

    public Scope<Thing>.PushResult ScopePushAndReport<Thing>(Scope<Thing> scope, string name, Thing thing, IOrigin tok, string kind) where Thing : class {
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
          reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.none, tok, "Duplicate {0} name: {1}", kind, name);
          break;
        case Scope<Thing>.PushResult.Shadow:
          reporter.Warning(MessageSource.Resolver, ResolutionErrors.ErrorId.none, tok, "Shadowed {0} name: {1}", kind, name);
          break;
      }

      return r;
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    public void ResolveFunctionSignature(Function f) {
      Contract.Requires(f != null);
      scope.PushMarker();
      if (f.SignatureIsOmitted) {
        reporter.Error(MessageSource.Resolver, f, "function signature can be omitted only in refining functions");
      }
      var option = f.TypeArgs.Count == 0 ? new ResolveTypeOption(f) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      foreach (Formal p in f.Ins) {
        ScopePushAndReport(scope, p, "parameter");
        ResolveType(p.Tok, p.Type, f, option, f.TypeArgs);
      }
      if (f.Result != null) {
        ScopePushAndReport(scope, f.Result, "parameter/return");
        ResolveType(f.Result.Tok, f.Result.Type, f, option, f.TypeArgs);
      } else {
        ResolveType(f.Tok, f.ResultType, f, option, f.TypeArgs);
      }
      scope.PopMarker();
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
    public void ResolveMethodSignature(Method m) {
      Contract.Requires(m != null);

      scope.PushMarker();
      if (m.SignatureIsOmitted) {
        reporter.Error(MessageSource.Resolver, m, "method signature can be omitted only in refining methods");
      }
      var option = m.TypeArgs.Count == 0 ? new ResolveTypeOption(m) : new ResolveTypeOption(ResolveTypeOptionEnum.AllowPrefix);
      // resolve in-parameters
      foreach (Formal p in m.Ins) {
        ScopePushAndReport(scope, p, "parameter");
        ResolveType(p.Tok, p.Type, m, option, m.TypeArgs);
      }
      // resolve out-parameters
      foreach (Formal p in m.Outs) {
        ScopePushAndReport(scope, p, "parameter");
        ResolveType(p.Tok, p.Type, m, option, m.TypeArgs);
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
        ResolveType(p.Tok, p.Type, iter, option, iter.TypeArgs);
      }
      foreach (var p in iter.Outs) {
        ResolveType(p.Tok, p.Type, iter, option, iter.TypeArgs);
        if (!p.Type.KnownToHaveToAValue(p.IsGhost)) {
          reporter.Error(MessageSource.Resolver, p.Tok, "type of yield-parameter must support auto-initialization (got '{0}')", p.Type);
        }
      }
      // resolve the types of the added fields (in case some of these types would cause the addition of default type arguments)
      if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
        foreach (var p in iter.OutsHistoryFields) {
          ResolveType(p.Tok, p.Type, iter, option, iter.TypeArgs);
        }
      }
      if (iter.TypeArgs.Count != iter.NonNullTypeDecl.TypeArgs.Count) {
        // Apparently, the type resolution automatically added type arguments to the iterator. We'll add these to the
        // corresponding non-null type as well.
        Contract.Assert(initiallyNoTypeArguments);
        Contract.Assert(iter.NonNullTypeDecl.TypeArgs.Count == 0);
        var nnt = iter.NonNullTypeDecl;
        nnt.TypeArgs.AddRange(TypeParameter.CloneTypeParameters(iter.TypeArgs));
        var varUdt = (UserDefinedType)nnt.Var.Type;
        Contract.Assert(varUdt.TypeArgs.Count == 0);
        varUdt.TypeArgs = nnt.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      }
      scope.PopMarker();
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
    internal Type ResolvedArrayType(IOrigin tok, int dims, Type arg, ResolutionContext resolutionContext, bool useClassNameType) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      var (at, modBuiltins) = SystemModuleManager.ArrayType(tok, dims, new List<Type> { arg }, false, useClassNameType);
      modBuiltins(SystemModuleManager);
      ResolveType(tok, at, resolutionContext, ResolveTypeOptionEnum.DontInfer, null);
      return at;
    }

    public Expression VarDotMethod(IOrigin tok, string varName, string methodName) {
      return new ApplySuffix(tok, null, new ExprDotName(tok, new IdentifierExpr(tok, varName), new Name(methodName), null), new List<ActualBinding>(), Token.NoToken);
    }

    public Expression makeTemp(String prefix, AssignOrReturnStmt s, ResolutionContext resolutionContext, Expression ex) {
      var temp = FreshTempVarName(prefix, resolutionContext.CodeContext);
      var locvar = new LocalVariable(s.Origin, temp, ex.Type, false);
      var id = new IdentifierExpr(s.Tok, temp);
      var idlist = new List<Expression>() { id };
      var lhss = new List<LocalVariable>() { locvar };
      var rhss = new List<AssignmentRhs>() { new ExprRhs(ex) };
      var up = new AssignStatement(s.Origin, idlist, rhss);
      s.ResolvedStatements.Add(new VarDeclStmt(s.Origin, lhss, up));
      return id;
    }

    public void EnsureSupportsErrorHandling(IOrigin tok, Type tp, bool expectExtract, [CanBeNull] string keyword) {
      // The "method not found" errors which will be generated here were already reported while
      // resolving the statement, so we don't want them to reappear and redirect them into a sink.
      var origReporter = reporter;
      this.reporter = new ErrorReporterSink(Options);

      var isFailure = ResolveMember(tok, tp, "IsFailure", out _);
      var propagateFailure = ResolveMember(tok, tp, "PropagateFailure", out _);
      var extract = ResolveMember(tok, tp, "Extract", out _);

      if (keyword != null) {
        if (isFailure == null || (extract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          var requiredMembers = expectExtract
            ? "functions 'IsFailure()' and 'Extract()'"
            : "function 'IsFailure()', but not 'Extract()'";
          origReporter.Error(MessageSource.Resolver, tok,
            $"The right-hand side of ':- {keyword}', which is of type '{tp}', with a keyword token must have {requiredMembers}");
        }
      } else {
        if (isFailure == null || propagateFailure == null || (extract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          var requiredMembers = expectExtract
            ? "functions 'IsFailure()', 'PropagateFailure()', and 'Extract()'"
            : "functions 'IsFailure()' and 'PropagateFailure()', but not 'Extract()'";
          origReporter.Error(MessageSource.Resolver, tok, $"The right-hand side of ':-', which is of type '{tp}', must have {requiredMembers}");
        }
      }

      void CheckIsFunction([CanBeNull] MemberDecl memberDecl, bool allowMethod) {
        if (memberDecl == null || memberDecl is Function) {
          // fine
        } else if (allowMethod && memberDecl is Method) {
          // give a deprecation warning, so we will remove this language feature around the Dafny 4 time frame
          origReporter.Deprecated(MessageSource.Resolver, ErrorId.r_failure_methods_deprecated, tok,
            $"Support for member '{memberDecl.Name}' in type '{tp}' (used indirectly via a :- statement) being a method is deprecated;" +
            " declare it to be a function instead");
        } else {
          // not allowed
          origReporter.Error(MessageSource.Resolver, tok,
            $"Member '{memberDecl.Name}' in type '{tp}' (used indirectly via a :- statement) is expected to be a function");
        }
      }

      CheckIsFunction(isFailure, false);
      if (keyword == null) {
        CheckIsFunction(propagateFailure, true);
      }
      if (expectExtract) {
        CheckIsFunction(extract, true);
      }

      this.reporter = origReporter;
    }

    /// <summary>
    /// Check that "stmt" is a valid statement for the body of an assert-by, forall,
    /// or calc-hint statement. In particular, check that the local variables assigned in
    /// the bodies of these statements are declared in the statements, not in some enclosing
    /// context. 
    /// </summary>
    public void CheckLocalityUpdates(Statement stmt, ISet<LocalVariable> localsAllowedInUpdates, string where) {
      Contract.Requires(stmt != null);
      Contract.Requires(localsAllowedInUpdates != null);
      Contract.Requires(where != null);

      if (stmt is AssertStmt or ForallStmt or CalcStmt or ModifyStmt) {
        // don't recurse, since CheckHintRestrictions will be called on that assert-by separately
        return;
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          CheckLocalityUpdatesLhs(lhs, localsAllowedInUpdates, @where);
        }
      } else if (stmt is SingleAssignStmt) {
        var s = (SingleAssignStmt)stmt;
        CheckLocalityUpdatesLhs(s.Lhs, localsAllowedInUpdates, @where);
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        foreach (var lhs in s.Lhs) {
          CheckLocalityUpdatesLhs(lhs, localsAllowedInUpdates, @where);
        }
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        s.Locals.ForEach(local => localsAllowedInUpdates.Add(local));
      } else if (stmt is ModifyStmt) {
        // no further complaints (note, ghost interests have already checked for 'modify' statements)
      } else if (stmt is BlockStmt) {
        localsAllowedInUpdates = new HashSet<LocalVariable>(localsAllowedInUpdates);
        // use this new set for the recursive calls
      } else if (stmt is BlockByProofStmt blockByProofStmt) {
        localsAllowedInUpdates = new HashSet<LocalVariable>(localsAllowedInUpdates);
        // use this new set for the recursive calls

        CheckLocalityUpdates(blockByProofStmt.Body, localsAllowedInUpdates, where);
        return;
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
        reporter.Error(MessageSource.Resolver, lhs.Tok, "{0} is not allowed to update a variable it doesn't declare", where);
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

    void FindAllMembers(ClassLikeDecl cl, string memberName, ISet<MemberDecl> foundSoFar) {
      Contract.Requires(cl != null);
      Contract.Requires(memberName != null);
      Contract.Requires(foundSoFar != null);
      if (GetClassMembers(cl).TryGetValue(memberName, out var member)) {
        foundSoFar.Add(member);
      }
      cl.ParentTraitHeads.ForEach(trait => FindAllMembers(trait, memberName, foundSoFar));
    }

    // TODO move
    public static UserDefinedType GetThisType(IOrigin tok, TopLevelDeclWithMembers cl) {
      Contract.Requires(tok != null);
      Contract.Requires(cl != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      if (cl is ClassLikeDecl { NonNullTypeDecl: { } } cls) {
        return UserDefinedType.FromTopLevelDecl(tok, cls.NonNullTypeDecl, cls.TypeArgs);
      } else {
        return UserDefinedType.FromTopLevelDecl(tok, cl, cl.TypeArgs);
      }
    }

    // TODO move
    public static UserDefinedType GetReceiverType(IOrigin tok, MemberDecl member) {
      Contract.Requires(tok != null);
      Contract.Requires(member != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      return GetThisType(tok, (TopLevelDeclWithMembers)member.EnclosingClass);
    }

    internal Expression VarDotFunction(IOrigin tok, string varName, string functionName) {
      return new ApplySuffix(tok, null, new ExprDotName(tok, new IdentifierExpr(tok, varName), new Name(functionName), null), new List<ActualBinding>(), Token.NoToken);
    }

    // TODO search for occurrences of "new LetExpr" which could benefit from this helper
    internal LetExpr LetPatIn(IOrigin tok, CasePattern<BoundVar> lhs, Expression rhs, Expression body) {
      return new LetExpr(tok, new List<CasePattern<BoundVar>>() { lhs }, new List<Expression>() { rhs }, body, true);
    }

    internal LetExpr LetVarIn(IOrigin tok, string name, Type tp, Expression rhs, Expression body) {
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
      expr.ResolvedExpression = LetVarIn(expr.Tok, temp, tempType, expr.Rhs,
        // "if temp.IsFailure()"
        new ITEExpr(expr.Tok, false, VarDotFunction(expr.Tok, temp, "IsFailure"),
          // "then temp.PropagateFailure()"
          VarDotFunction(expr.Tok, temp, "PropagateFailure"),
          // "else"
          expr.Lhs == null
            // "F"
            ? expr.Body
            // "var x: T := temp.Extract(); F"
            : LetPatIn(expr.Tok, expr.Lhs, VarDotFunction(expr.Tok, temp, "Extract"), expr.Body)));

      ResolveExpression(expr.ResolvedExpression, resolutionContext);
      expr.Type = expr.ResolvedExpression.Type;
      bool expectExtract = (expr.Lhs != null);
      EnsureSupportsErrorHandling(expr.Tok, PartiallyResolveTypeForMemberSelection(expr.Tok, tempType), expectExtract, null);
    }

    public static Type SelectAppropriateArrowTypeForFunction(Function function, Dictionary<TypeParameter, Type> subst, SystemModuleManager systemModuleManager) {
      return SelectAppropriateArrowType(function.Tok,
        function.Ins.ConvertAll(formal => formal.Type.Subst(subst)),
        function.ResultType.Subst(subst),
        function.Reads.Expressions.Count != 0, function.Req.Count != 0,
        systemModuleManager);
    }

    public static Type SelectAppropriateArrowType(IOrigin tok, List<Type> typeArgs, Type resultType, bool hasReads, bool hasReq, SystemModuleManager systemModuleManager) {
      Contract.Requires(tok != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(resultType != null);
      var arity = typeArgs.Count;
      var typeArgsAndResult = Util.Snoc(typeArgs, resultType);
      if (hasReads) {
        // any arrow
        return new ArrowType(tok, systemModuleManager.ArrowTypeDecls[arity], typeArgsAndResult);
      } else if (hasReq) {
        // partial arrow
        return new UserDefinedType(tok, ArrowType.PartialArrowTypeName(arity), systemModuleManager.PartialArrowTypeDecls[arity], typeArgsAndResult);
      } else {
        // total arrow
        return new UserDefinedType(tok, ArrowType.TotalArrowTypeName(arity), systemModuleManager.TotalArrowTypeDecls[arity], typeArgsAndResult);
      }
    }

    /// <summary>
    /// Adds appropriate type constraints that says "expr" evaluates to an integer or (if "allowBitVector" is true) a
    /// a bitvector.  The "errFormat" string can contain a "{0}", referring to the name of the type of "expr".
    /// </summary>
    public void ConstrainToIntegerType(Expression expr, bool allowBitVector, string errFormat) {
      Contract.Requires(expr != null);
      Contract.Requires(errFormat != null);
      var err = new TypeConstraint.ErrorMsgWithToken(expr.Tok, errFormat, expr.Type);
      ConstrainToIntegerType(expr.Tok, expr.Type, allowBitVector, err);
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
          udt = new UserDefinedType(pat.Tok, dtd.Name, dtd, typeArgs);
          ConstrainSubtypeRelation(udt, sourceType, pat.Tok, "type of RHS ({0}) does not match type of bound variable '{1}'", sourceType, pat.Id);
        }
      }
      if (dtd == null && ctor == null) {
        reporter.Error(MessageSource.Resolver, pat.Tok, "to use a pattern, the type of the source/RHS expression must be a datatype (instead found {0})", sourceType);
      } else if (ctor == null) {
        reporter.Error(MessageSource.Resolver, pat.Tok, "constructor {0} does not exist in datatype {1}", pat.Id, dtd.Name);
      } else {
        if (pat.Arguments == null) {
          if (ctor.Formals.Count == 0) {
            // The Id matches a constructor of the correct type and 0 arguments,
            // so make it a nullary constructor, not a variable
            pat.MakeAConstructor();
          }
        } else {
          if (ctor.Formals.Count != pat.Arguments.Count) {
            reporter.Error(MessageSource.Resolver, pat.Tok, "pattern for constructor {0} has wrong number of formals (found {1}, expected {2})", pat.Id, pat.Arguments.Count, ctor.Formals.Count);
          }
        }
        // build the type-parameter substitution map for this use of the datatype
        Contract.Assert(dtd.TypeArgs.Count == udt.TypeArgs.Count);  // follows from the type previously having been successfully resolved
        var subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, udt.TypeArgs);
        // recursively call ResolveCasePattern on each of the arguments
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
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
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount && j == ctor.Formals.Count) {
          pat.AssembleExpr(udt.TypeArgs);
        }
      }
    }

    internal readonly List<DefaultValueExpression> allDefaultValueExpressions = new();

    /// <summary>
    /// This method is called at the tail end of Pass1 of the Resolver.
    /// </summary>
    internal void FillInDefaultValueExpressions() {
      var visited = new Dictionary<DefaultValueExpression, DefaultValueExpression.WorkProgress>();
      foreach (var e in allDefaultValueExpressions) {
        e.FillIn(this, visited);
      }
      allDefaultValueExpressions.Clear();
    }

    public Dictionary<TypeParameter, Type> BuildTypeArgumentSubstitute(Dictionary<TypeParameter, Type> typeArgumentSubstitutions,
      Type/*?*/ receiverTypeBound = null) {
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
        subst = AddParentTypeParameterSubstitutions(subst, receiverTypeBound);
      }

      return subst;
    }

    public static Dictionary<TypeParameter, Type> AddParentTypeParameterSubstitutions(Dictionary<TypeParameter, Type> subst, Type receiverType = null) {
      TopLevelDeclWithMembers cl;
      var udt = receiverType?.AsNonNullRefType;
      if (udt != null) {
        cl = (TopLevelDeclWithMembers)((NonNullTypeDecl)udt.ResolvedClass).ViewAsClass;
      } else {
        udt = receiverType.NormalizeExpand() as UserDefinedType;
        cl = udt?.ResolvedClass as TopLevelDeclWithMembers;
      }
      if (cl != null) {
        cl.AddParentTypeParameterSubstitutions(subst);
      }

      return subst;
    }

    public static string GhostPrefix(bool isGhost) {
      return isGhost ? "ghost " : "";
    }

    internal static ModuleSignature GetSignatureExt(ModuleSignature sig) {
      Contract.Requires(sig != null);
      Contract.Ensures(Contract.Result<ModuleSignature>() != null);
      return sig;
    }

    public ModuleSignature GetSignature(ModuleSignature sig) {
      return GetSignatureExt(sig);
    }

    public static Expression GetImpliedTypeConstraint(IVariable bv, Type type) {
      return GetImpliedTypeConstraint(Expression.CreateIdentExpr(bv), type);
    }

    /// <summary>
    /// Collects the constraints of all subset types and newtypes in "type" and applies these to "e".
    /// For example, given
    ///     type Even = x: int | x % 2 == 0
    ///     newtype Div6 = y: Even | y % 3 == 0
    /// GetImpliedTypeConstraint(e, Div6) returns
    ///     true && ((e as Even) % 2 == 0) && e % 3 == 0
    /// </summary>
    public static Expression GetImpliedTypeConstraint(Expression e, Type type) {
      Contract.Requires(e != null);
      Contract.Requires(type != null);
      type = type.NormalizeExpandKeepConstraints();
      if (type is UserDefinedType udt) {
        Expression CombineConstraints(Type baseType, BoundVar boundVar, Expression constraint) {
          var c = GetImpliedTypeConstraint(e, baseType);
          if (boundVar != null) {
            var ee = new ConversionExpr(e.Tok, e, boundVar.Type) { Type = boundVar.Type };
            var substMap = new Dictionary<IVariable, Expression> { { boundVar, ee } };
            var typeMap = TypeParameter.SubstitutionMap(udt.ResolvedClass.TypeArgs, udt.TypeArgs);
            var substituter = new Substituter(null, substMap, typeMap);
            c = Expression.CreateAnd(c, substituter.Substitute(constraint));
          }
          return c;
        }

        if (udt.ResolvedClass is NewtypeDecl newtypeDecl) {
          return CombineConstraints(newtypeDecl.RhsWithArgument(udt.TypeArgs), newtypeDecl.Var, newtypeDecl.Constraint);
        }
        if (udt.ResolvedClass is SubsetTypeDecl subsetTypeDecl) {
          return CombineConstraints(subsetTypeDecl.RhsWithArgument(udt.TypeArgs), subsetTypeDecl.Var, subsetTypeDecl.Constraint);
        }
      }
      return Expression.CreateBoolLiteral(e.Tok, true);
    }

    /// <summary>
    /// Returns the set of free variables in "expr".
    /// Requires "expr" to be successfully resolved.
    /// Ensures that the set returned has no aliases.
    /// </summary>
    public static ISet<IVariable> FreeVariables(Expression expr) {
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
        foreach (var fe in e.Reads.Expressions) {
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

      public SeqSelectOneErrorMsg(IOrigin tok, Type exprSeqType, Type expectedSeqType)
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
      leftOperandType = leftOperandType.NormalizeToAncestorType();
      operandType = operandType.NormalizeToAncestorType();
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
      var visitor = new CollectFriendlyCallsInSpec_Visitor(reporter, friendlyCalls, co, context);
      visitor.Visit(expr, position ? CallingPosition.Positive : CallingPosition.Negative);
    }
  }

  abstract class ResolverTopDownVisitor<T> : TopDownVisitor<T> {
    protected ErrorReporter reporter;
    public ResolverTopDownVisitor(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }
  }
}
