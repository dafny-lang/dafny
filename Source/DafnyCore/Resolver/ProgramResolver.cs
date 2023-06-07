using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny; 

public class ProgramResolver {

  public DafnyOptions Options { get; }
  public BuiltIns BuiltIns { get; }
  public ErrorReporter Reporter { get; }

  public List<IRewriter> rewriters;

  internal readonly ValuetypeDecl[] valuetypeDecls;
  public ModuleSignature systemNameInfo;
  readonly Graph<ModuleDecl> dependencies = new();
  public RefinementTransformer refinementTransformer;

  public FreshIdGenerator defaultTempVarIdGenerator = new();

  public ProgramResolver(Program program) {
    BuiltIns = program.BuiltIns;
    Reporter = program.Reporter;

    // Map#Items relies on the two destructors for 2-tuples
    BuiltIns.TupleType(Token.NoToken, 2, true);
    // Several methods and fields rely on 1-argument arrow types
    BuiltIns.CreateArrowTypeDecl(1);

    valuetypeDecls = new ValuetypeDecl[] {
        new ValuetypeDecl("bool", BuiltIns.SystemModule, t => t.IsBoolType, typeArgs => Type.Bool),
        new ValuetypeDecl("int", BuiltIns.SystemModule, t => t.IsNumericBased(Type.NumericPersuasion.Int), typeArgs => Type.Int),
        new ValuetypeDecl("real", BuiltIns.SystemModule, t => t.IsNumericBased(Type.NumericPersuasion.Real), typeArgs => Type.Real),
        new ValuetypeDecl("ORDINAL", BuiltIns.SystemModule, t => t.IsBigOrdinalType, typeArgs => Type.BigOrdinal),
        new ValuetypeDecl("_bv", BuiltIns.SystemModule, t => t.IsBitVectorType, null), // "_bv" represents a family of classes, so no typeTester or type creator is supplied
        new ValuetypeDecl("map", BuiltIns.SystemModule,
          new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Strict , TypeParameter.TPVarianceSyntax.Covariant_Strict },
          t => t.IsMapType, typeArgs => new MapType(true, typeArgs[0], typeArgs[1])),
        new ValuetypeDecl("imap", BuiltIns.SystemModule,
          new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Permissive , TypeParameter.TPVarianceSyntax.Covariant_Strict },
          t => t.IsIMapType, typeArgs => new MapType(false, typeArgs[0], typeArgs[1]))
      };
    BuiltIns.SystemModule.SourceDecls.AddRange(valuetypeDecls);
    // Resolution error handling relies on being able to get to the 0-tuple declaration
    BuiltIns.TupleType(Token.NoToken, 0, true);

    // Populate the members of the basic types

    void AddMember(MemberDecl member, ValuetypeVariety valuetypeVariety) {
      var enclosingType = valuetypeDecls[(int)valuetypeVariety];
      member.EnclosingClass = enclosingType;
      member.AddVisibilityScope(program.BuiltIns.SystemModule.VisibilityScope, false);
      enclosingType.Members.Add(member);
    }

    var floor = new SpecialField(RangeToken.NoToken, "Floor", SpecialField.ID.Floor, null, false, false, false, Type.Int, null);
    AddMember(floor, ValuetypeVariety.Real);

    var isLimit = new SpecialField(RangeToken.NoToken, "IsLimit", SpecialField.ID.IsLimit, null, false, false, false, Type.Bool, null);
    AddMember(isLimit, ValuetypeVariety.BigOrdinal);

    var isSucc = new SpecialField(RangeToken.NoToken, "IsSucc", SpecialField.ID.IsSucc, null, false, false, false, Type.Bool, null);
    AddMember(isSucc, ValuetypeVariety.BigOrdinal);

    var limitOffset = new SpecialField(RangeToken.NoToken, "Offset", SpecialField.ID.Offset, null, false, false, false, Type.Int, null);
    AddMember(limitOffset, ValuetypeVariety.BigOrdinal);
    BuiltIns.ORDINAL_Offset = limitOffset;

    var isNat = new SpecialField(RangeToken.NoToken, "IsNat", SpecialField.ID.IsNat, null, false, false, false, Type.Bool, null);
    AddMember(isNat, ValuetypeVariety.BigOrdinal);

    // Add "Keys", "Values", and "Items" to map, imap
    foreach (var typeVariety in new[] { ValuetypeVariety.Map, ValuetypeVariety.IMap }) {
      var vtd = valuetypeDecls[(int)typeVariety];
      var isFinite = typeVariety == ValuetypeVariety.Map;

      var r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[0]));
      var keys = new SpecialField(RangeToken.NoToken, "Keys", SpecialField.ID.Keys, null, false, false, false, r, null);

      r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[1]));
      var values = new SpecialField(RangeToken.NoToken, "Values", SpecialField.ID.Values, null, false, false, false, r, null);

      var gt = vtd.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      var dt = BuiltIns.TupleType(Token.NoToken, 2, true);
      var tupleType = new UserDefinedType(Token.NoToken, dt.Name, dt, gt);
      r = new SetType(isFinite, tupleType);
      var items = new SpecialField(RangeToken.NoToken, "Items", SpecialField.ID.Items, null, false, false, false, r, null);

      foreach (var memb in new[] { keys, values, items }) {
        AddMember(memb, typeVariety);
      }
    }

    // The result type of the following bitvector methods is the type of the bitvector itself. However, we're representing all bitvector types as
    // a family of types rolled up in one ValuetypeDecl. Therefore, we use the special SelfType as the result type.
    AddRotateMember(valuetypeDecls[(int)ValuetypeVariety.Bitvector], "RotateLeft", new SelfType());
    AddRotateMember(valuetypeDecls[(int)ValuetypeVariety.Bitvector], "RotateRight", new SelfType());
  }

  public void AddRotateMember(ValuetypeDecl enclosingType, string name, Type resultType) {
    var formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, null, false) };
    var rotateMember = new SpecialFunction(RangeToken.NoToken, name, BuiltIns.SystemModule, false, false,
      new List<TypeParameter>(), formals, resultType,
      new List<AttributedExpression>(), new List<FrameExpression>(), new List<AttributedExpression>(),
      new Specification<Expression>(new List<Expression>(), null), null, null, null);
    rotateMember.EnclosingClass = enclosingType;
    rotateMember.AddVisibilityScope(BuiltIns.SystemModule.VisibilityScope, false);
    enclosingType.Members.Add(rotateMember);
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

  private void ResolveValuetypeDecls() {
    var moduleResolver = new ModuleResolver(this);
    moduleResolver.moduleInfo = systemNameInfo;
    foreach (var valueTypeDecl in valuetypeDecls) {
      foreach (var member in valueTypeDecl.Members) {
        if (member is Function function) {
          moduleResolver.ResolveFunctionSignature(function);
          CallGraphBuilder.VisitFunction(function, Reporter);
        } else if (member is Method method) {
          moduleResolver.ResolveMethodSignature(method);
          CallGraphBuilder.VisitMethod(method, Reporter);
        }
      }
    }
  }


  public void ResolveProgram(Program prog) {
    Contract.Requires(prog != null);
    Type.ResetScopes();

    Type.EnableScopes();
    // For the formatter, we ensure we take snapshots of the PrefixNamedModules
    // and topleveldecls
    prog.DefaultModuleDef.PreResolveSnapshotForFormatter();
    var origErrorCount = Reporter.ErrorCount; //TODO: This is used further below, but not in the >0 comparisons in the next few lines. Is that right?
    var bindings = new ModuleBindings(null);
    var b = BindModuleNames(prog.DefaultModuleDef, bindings);
    bindings.BindName(prog.DefaultModule.Name, prog.DefaultModule, b);
    if (Reporter.ErrorCount > 0) {
      return;
    } // if there were errors, then the implict ModuleBindings data structure invariant

    // is violated, so Processing dependencies will not succeed.
    ProcessDependencies(prog.DefaultModule, b, dependencies);
    // check for cycles in the import graph
    foreach (var cycle in dependencies.AllCycles()) {
      ModuleResolver.ReportCycleError(Reporter, cycle, m => m.tok,
        m => (m is AliasModuleDecl ? "import " : "module ") + m.Name,
        "module definition contains a cycle (note: parent modules implicitly depend on submodules)");
    }

    if (Reporter.ErrorCount > 0) {
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

    if (Options.AuditProgram) {
      rewriters.Add(new Auditor.Auditor(Reporter));
    }

    refinementTransformer = new RefinementTransformer(prog);
    rewriters.Add(refinementTransformer);
    if (!Options.VerifyAllModules) {
      rewriters.Add(new IncludedLemmaBodyRemover(prog, Reporter));
    }
    rewriters.Add(new AutoContractsRewriter(Reporter, BuiltIns));
    rewriters.Add(new OpaqueMemberRewriter(this.Reporter));
    rewriters.Add(new AutoReqFunctionRewriter(this.Reporter, BuiltIns));
    rewriters.Add(new TimeLimitRewriter(Reporter));
    rewriters.Add(new ForallStmtRewriter(Reporter));
    rewriters.Add(new ProvideRevealAllRewriter(this.Reporter));
    rewriters.Add(new MatchFlattener(this.Reporter, defaultTempVarIdGenerator));

    if (Options.AutoTriggers) {
      rewriters.Add(new QuantifierSplittingRewriter(Reporter));
      rewriters.Add(new TriggerGeneratingRewriter(Reporter));
    }

    if (Options.TestContracts != DafnyOptions.ContractTestingMode.None) {
      rewriters.Add(new ExpectContracts(Reporter));
    }

    if (Options.RunAllTests) {
      rewriters.Add(new RunAllTestsMainMethod(Reporter));
    }

    rewriters.Add(new InductionRewriter(Reporter));
    rewriters.Add(new PrintEffectEnforcement(Reporter));
    rewriters.Add(new BitvectorOptimization(Reporter));

    if (Options.DisallowConstructorCaseWithoutParentheses) {
      rewriters.Add(new ConstructorWarning(Reporter));
    }
    rewriters.Add(new LocalLinter(Reporter));
    rewriters.Add(new PrecedenceLinter(Reporter));

    foreach (var plugin in Options.Plugins) {
      rewriters.AddRange(plugin.GetRewriters(Reporter));
    }

    var systemModuleResolver = new ModuleResolver(this);

    systemNameInfo = systemModuleResolver.RegisterTopLevelDecls(prog.BuiltIns.SystemModule, false);
    prog.CompileModules.Add(prog.BuiltIns.SystemModule);
    systemModuleResolver.RevealAllInScope(prog.BuiltIns.SystemModule.TopLevelDecls, systemNameInfo.VisibilityScope);
    ResolveValuetypeDecls();

    // The SystemModule is constructed with all its members already being resolved. Except for
    // the non-null type corresponding to class types.  They are resolved here:
    var systemModuleClassesWithNonNullTypes =
      prog.BuiltIns.SystemModule.TopLevelDecls.Where(d => (d as ClassLikeDecl)?.NonNullTypeDecl != null).ToList();
    foreach (var cl in systemModuleClassesWithNonNullTypes) {
      var d = ((ClassLikeDecl)cl).NonNullTypeDecl;
      systemModuleResolver.allTypeParameters.PushMarker();
      systemModuleResolver.ResolveTypeParameters(d.TypeArgs, true, d);
      systemModuleResolver.ResolveType(d.tok, d.Rhs, d, ResolveTypeOptionEnum.AllowPrefix, d.TypeArgs);
      systemModuleResolver.allTypeParameters.PopMarker();
    }
    systemModuleResolver.ResolveTopLevelDecls_Core(ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(systemModuleClassesWithNonNullTypes).ToList(),
      new Graph<IndDatatypeDecl>(), new Graph<CoDatatypeDecl>(), prog.BuiltIns.SystemModule.Name);

    foreach (var rewriter in rewriters) {
      rewriter.PreResolve(prog);
    }

    foreach (var decl in sortedDecls) {
      var moduleResolver = new ModuleResolver(this);
      moduleResolver.ResolveModuleDeclaration(prog, decl, origErrorCount);
    }

    if (Reporter.ErrorCount != origErrorCount) {
      return;
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

      string compileName = m.GetCompileName(Options);
      ModuleDefinition priorModDef;
      if (compileNameMap.TryGetValue(compileName, out priorModDef)) {
        Reporter.Error(MessageSource.Resolver, m.tok,
          "modules '{0}' and '{1}' both have CompileName '{2}'",
          priorModDef.tok.val, m.tok.val, compileName);
      } else {
        compileNameMap.Add(compileName, m);
      }
    }
  }

  public static string ModuleNotFoundErrorMessage(int i, List<Name> path, string tail = "") {
    Contract.Requires(path != null);
    Contract.Requires(0 <= i && i < path.Count);
    return "module " + path[i].Value + " does not exist" +
           (1 < path.Count
             ? " (position " + i.ToString() + " in path " + Util.Comma(".", path, x => x.Value) + ")" + tail
             : "");
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
      var modDef = new ModuleDefinition(tok.ToRange(), new Name(tok.ToRange(), name), new List<IToken>(), false, false, null, moduleDecl, null, false);
      // Add the new module to the top-level declarations of its parent and then bind its names as usual
      var subdecl = new LiteralModuleDecl(modDef, moduleDecl);
      moduleDecl.ResolvedPrefixNamedModules.Add(subdecl);
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
            Reporter.Error(MessageSource.Resolver, subdecl.tok, "Duplicate name of import: {0}", subdecl.Name);
          } else if (tld is AliasModuleDecl importDecl && importDecl.Opened && importDecl.TargetQId.Path.Count == 1 &&
                     importDecl.Name == importDecl.TargetQId.rootName()) {
            importDecl.ShadowsLiteralModule = true;
          } else {
            Reporter.Error(MessageSource.Resolver, subdecl.tok,
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
          litmod.ModuleDef.ResolvedPrefixNamedModules.Add(sm);
        } else {
          litmod.ModuleDef.PrefixNamedModules.Add(tup);
        }
      }
    }

    var bindings = BindModuleNames(litmod.ModuleDef, parentBindings);
    if (!parentBindings.BindName(litmod.Name, litmod, bindings)) {
      Reporter.Error(MessageSource.Resolver, litmod.tok, "Duplicate module name: {0}", litmod.Name);
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
        Reporter.Error(MessageSource.Resolver, m.RefinementQId.rootToken(),
          $"module {m.RefinementQId.ToString()} named as refinement base does not exist");
      } else if (other is LiteralModuleDecl && ((LiteralModuleDecl)other).ModuleDef == m) {
        Reporter.Error(MessageSource.Resolver, m.RefinementQId.rootToken(), "module cannot refine itself: {0}",
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
          Reporter.Error(MessageSource.Resolver, d.tok,
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
        Reporter.Error(MessageSource.Resolver, alias.tok, ModuleNotFoundErrorMessage(0, alias.TargetQId.Path));
      } else {
        dependencies.AddEdge(moduleDecl, root);
      }
    } else if (moduleDecl is AbstractModuleDecl) {
      var abs = moduleDecl as AbstractModuleDecl;
      ModuleDecl root;
      if (!ResolveQualifiedModuleIdRootAbstract(abs, bindings, abs.QId, out root)) {
        //if (!bindings.TryLookupFilter(abs.QId.rootToken(), out root,
        //  m => abs != m && (((abs.EnclosingModuleDefinition == m.EnclosingModuleDefinition) && (abs.Exports.Count == 0)) || m is LiteralModuleDecl)))
        Reporter.Error(MessageSource.Resolver, abs.tok, ModuleNotFoundErrorMessage(0, abs.QId.Path));
      } else {
        dependencies.AddEdge(moduleDecl, root);
      }
    }
  }
}

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
