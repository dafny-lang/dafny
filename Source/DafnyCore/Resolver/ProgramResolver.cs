using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny; 

public class ProgramResolver {

  public DafnyOptions Options { get; }
  public BuiltIns BuiltIns { get; }
  public ErrorReporter Reporter { get; }

  public IList<IRewriter> rewriters;

  internal readonly ValuetypeDecl[] valuetypeDecls;
  public ModuleSignature systemNameInfo;
  protected readonly Graph<ModuleDecl> dependencies = new();

  public FreshIdGenerator defaultTempVarIdGenerator = new();
  public readonly Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> classMembers = new();

  public ProgramResolver(Program program) {
    BuiltIns = program.BuiltIns;
    Reporter = program.Reporter;
    Options = program.Options;

    // Map#Items relies on the two destructors for 2-tuples
    BuiltIns.TupleType(Token.NoToken, 2, true);
    // Several methods and fields rely on 1-argument arrow types
    BuiltIns.CreateArrowTypeDecl(1);

    valuetypeDecls = new[] {
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
    var b = prog.DefaultModuleDef.BindModuleNames(this, bindings);
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
    }

    var sortedDecls = dependencies.TopologicallySortedComponents();
    prog.ModuleSigs = new();

    SetHeights(sortedDecls);

    prog.Compilation.Rewriters = Rewriters.GetRewriters(prog, defaultTempVarIdGenerator);
    rewriters = prog.Compilation.Rewriters;

    var systemModuleResolver = new ModuleResolver(this);

    systemNameInfo = systemModuleResolver.RegisterTopLevelDecls(prog.BuiltIns.SystemModule, false);
    systemModuleResolver.moduleInfo = systemNameInfo;

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

    foreach (var moduleClassMembers in systemModuleResolver.moduleClassMembers) {
      classMembers[moduleClassMembers.Key] = moduleClassMembers.Value;
    }

    foreach (var rewriter in rewriters) {
      rewriter.PreResolve(prog);
    }

    foreach (var decl in sortedDecls) {
      var moduleResolutionResult = ResolveModuleDeclaration(prog.Compilation, decl);
      foreach (var sig in moduleResolutionResult.Signatures) {
        prog.ModuleSigs[sig.Key] = sig.Value;
      }
      foreach (var moduleClassMembers in moduleResolutionResult.ClassMembers) {
        classMembers[moduleClassMembers.Key] = moduleClassMembers.Value;
      }

      foreach (var diagnostic in moduleResolutionResult.ErrorReporter.AllMessages) {
        Reporter.Message(diagnostic.Source, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token,
          diagnostic.Message);
      }
    }

    if (Reporter.ErrorCount != origErrorCount) {
      return;
    }

    Type.DisableScopes();
    CheckDupModuleNames(prog);

    foreach (var module in prog.Modules()) { // TODO move this inside cached module resolution?
      foreach (var rewriter in rewriters) {
        rewriter.PostResolve(module);
      }
    }

    foreach (var rewriter in rewriters) {
      rewriter.PostResolve(prog);
    }
  }

  protected virtual ModuleResolutionResult ResolveModuleDeclaration(CompilationData compilation, ModuleDecl decl) {
    var moduleResolver = new ModuleResolver(this);
    return moduleResolver.ResolveModuleDeclaration(compilation, decl);
  }

  private static void SetHeights(List<ModuleDecl> sortedDecls) {
    foreach (var withIndex in sortedDecls.Zip(Enumerable.Range(0, int.MaxValue))) {
      var md = withIndex.First;
      md.Height = withIndex.Second;
      if (md is LiteralModuleDecl literalModuleDecl) {
        var mdef = literalModuleDecl.ModuleDef;
        mdef.Height = withIndex.Second;
      }
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
