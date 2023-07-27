using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public record PrefixNameModule(IReadOnlyList<IToken> Parts, LiteralModuleDecl Module);

public class ModuleDefinition : RangeNode, IDeclarationOrUsage, IAttributeBearingDeclaration, ICloneable<ModuleDefinition> {

  public IToken BodyStartTok = Token.NoToken;
  public IToken TokenWithTrailingDocString = Token.NoToken;
  public string DafnyName => NameNode.StartToken.val; // The (not-qualified) name as seen in Dafny source code
  public readonly Name NameNode; // (Last segment of the) module name

  public override IToken Tok => NameNode.StartToken;

  public string Name => NameNode.Value;
  public string FullDafnyName {
    get {
      if (EnclosingModule == null) {
        return "";
      }

      string n = EnclosingModule.FullDafnyName;
      return (n.Length == 0 ? n : (n + ".")) + DafnyName;
    }
  }
  public string FullName {
    get {
      if (EnclosingModule == null || EnclosingModule.IsDefaultModule) {
        return Name;
      } else {
        return EnclosingModule.FullName + "." + Name;
      }
    }
  }
  public readonly List<IToken> PrefixIds; // The qualified module name, except the last segment when a
                                          // nested module declaration is outside its enclosing module
  public ModuleDefinition EnclosingModule;  // readonly, except can be changed by resolver for prefix-named modules when the real parent is discovered
  public readonly Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;
  public ModuleQualifiedId RefinementQId; // full qualified ID of the refinement parent, null if no refinement base
  public bool SuccessfullyResolved;  // set to true upon successful resolution; modules that import an unsuccessfully resolved module are not themselves resolved
  public readonly bool IsAbstract;
  public readonly bool IsFacade; // True iff this module represents a module facade (that is, an abstract interface)
  private readonly bool IsBuiltinName; // true if this is something like _System that shouldn't have it's name mangled.

  public DefaultClassDecl DefaultClass { get; set; }

  public readonly List<TopLevelDecl> SourceDecls = new();
  [FilledInDuringResolution]
  public readonly List<TopLevelDecl> ResolvedPrefixNamedModules = new();
  [FilledInDuringResolution]
  public readonly List<PrefixNameModule> PrefixNamedModules = new();  // filled in by the parser; emptied by the resolver
  public virtual IEnumerable<TopLevelDecl> TopLevelDecls => DefaultClasses.
        Concat(SourceDecls).
        Concat(ResolvedPrefixNamedModules);

  public IEnumerable<IPointer<TopLevelDecl>> TopLevelDeclPointers =>
    (DefaultClass == null
      ? Enumerable.Empty<Pointer<TopLevelDecl>>()
      : new[] { new Pointer<TopLevelDecl>(() => DefaultClass, v => DefaultClass = (DefaultClassDecl)v) }).
    Concat(SourceDecls.ToPointers()).Concat(ResolvedPrefixNamedModules.ToPointers());

  protected IEnumerable<TopLevelDecl> DefaultClasses {
    get { return DefaultClass == null ? Enumerable.Empty<TopLevelDecl>() : new TopLevelDecl[] { DefaultClass }; }
  }

  [FilledInDuringResolution]
  public readonly Graph<ICallable> CallGraph = new();
  [FilledInDuringResolution]
  public int Height;  // height in the topological sorting of modules;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(TopLevelDecls));
    Contract.Invariant(CallGraph != null);
  }

  public ModuleDefinition(Cloner cloner, ModuleDefinition original, Name name) : this(cloner, original) {
    NameNode = name;
    IsBuiltinName = true;
  }

  public ModuleDefinition(Cloner cloner, ModuleDefinition original) : base(cloner, original) {
    IsBuiltinName = original.IsBuiltinName;
    NameNode = original.NameNode;
    PrefixIds = original.PrefixIds.Select(cloner.Tok).ToList();

    IsFacade = original.IsFacade;
    Attributes = original.Attributes;
    IsAbstract = original.IsAbstract;
    RefinementQId = original.RefinementQId == null ? null : new ModuleQualifiedId(cloner, original.RefinementQId);
    foreach (var d in original.SourceDecls) {
      SourceDecls.Add(cloner.CloneDeclaration(d, this));
    }

    DefaultClass = (DefaultClassDecl)cloner.CloneDeclaration(original.DefaultClass, this);
    foreach (var tup in original.PrefixNamedModules) {
      var newTup = tup with {
        Module = (LiteralModuleDecl)cloner.CloneDeclaration(tup.Module, this)
      };
      PrefixNamedModules.Add(newTup);
    }

    // For cloning modules into their compiled variants, we don't want to copy resolved fields, but we do need to copy this.
    // We're hoping to remove the copying of modules into compiled variants altogether,
    // and then this can be moved to inside the `if (cloner.CloneResolvedFields)` block
    foreach (var tup in original.ResolvedPrefixNamedModules) {
      ResolvedPrefixNamedModules.Add(cloner.CloneDeclaration(tup, this));
    }

    if (cloner.CloneResolvedFields) {
      Height = original.Height;
    }
  }

  public ModuleDefinition(RangeToken tok, Name name, List<IToken> prefixIds, bool isAbstract, bool isFacade,
    ModuleQualifiedId refinementQId, ModuleDefinition parent, Attributes attributes,
    bool isBuiltinName) : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    this.NameNode = name;
    this.PrefixIds = prefixIds;
    this.Attributes = attributes;
    this.EnclosingModule = parent;
    this.RefinementQId = refinementQId;
    this.IsAbstract = isAbstract;
    this.IsFacade = isFacade;
    this.IsBuiltinName = isBuiltinName;

    if (Name != "_System") {
      DefaultClass = new DefaultClassDecl(this, new List<MemberDecl>());
    }
  }

  private VisibilityScope visibilityScope;
  public VisibilityScope VisibilityScope =>
    visibilityScope ??= new VisibilityScope(this.SanitizedName);

  public virtual bool IsDefaultModule => false;

  private string sanitizedName = null;

  public string SanitizedName {
    get {
      if (sanitizedName == null) {
        if (IsBuiltinName) {
          sanitizedName = Name;
        } else if (EnclosingModule != null && EnclosingModule.Name != "_module") {
          // Include all names in the module tree path, to disambiguate when compiling
          // a flat list of modules.
          // Use an "underscore-escaped" character as a module name separator, since
          // underscores are already used as escape characters in SanitizeName()
          sanitizedName = EnclosingModule.SanitizedName + "_m" + NonglobalVariable.SanitizeName(Name);
        } else {
          sanitizedName = NonglobalVariable.SanitizeName(Name);
        }
      }
      return sanitizedName;
    }
  }

  string compileName;

  public string GetCompileName(DafnyOptions options) {
    if (compileName == null) {
      var externArgs = options.DisallowExterns ? null : Attributes.FindExpressions(this.Attributes, "extern");
      var nonExternSuffix = (options.Get(CommonOptionBag.AddCompileSuffix) && Name != "_module" && Name != "_System" ? "_Compile" : "");
      if (externArgs != null && 1 <= externArgs.Count && externArgs[0] is StringLiteralExpr) {
        compileName = (string)((StringLiteralExpr)externArgs[0]).Value;
      } else if (externArgs != null) {
        compileName = Name + nonExternSuffix;
      } else {
        compileName = SanitizedName + nonExternSuffix;
      }
    }

    return compileName;
  }

  /// <summary>
  /// Determines if "a" and "b" are in the same strongly connected component of the call graph, that is,
  /// if "a" and "b" are mutually recursive.
  /// Assumes that CallGraph has already been filled in for the modules containing "a" and "b".
  /// </summary>
  public static bool InSameSCC(ICallable a, ICallable b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    if (a is SpecialFunction || b is SpecialFunction) { return false; }
    var module = a.EnclosingModule;
    return module == b.EnclosingModule && module.CallGraph.GetSCCRepresentative(a) == module.CallGraph.GetSCCRepresentative(b);
  }

  /// <summary>
  /// Return the representative elements of the SCCs that contain any member declaration in a
  /// class in "declarations".
  /// Note, the representative element may in some cases be a Method, not necessarily a Function.
  /// </summary>
  public static IEnumerable<ICallable> AllFunctionSCCs(List<TopLevelDecl> declarations) {
    var set = new HashSet<ICallable>();
    foreach (var d in declarations) {
      var cl = d as TopLevelDeclWithMembers;
      if (cl != null) {
        var module = cl.EnclosingModuleDefinition;
        foreach (var member in cl.Members) {
          var fn = member as Function;
          if (fn != null) {
            var repr = module.CallGraph.GetSCCRepresentative(fn);
            set.Add(repr);
          }
        }
      }
    }
    return set;
  }

  public static IEnumerable<Function> AllFunctions(List<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      var cl = d as TopLevelDeclWithMembers;
      if (cl != null) {
        foreach (var member in cl.Members) {
          var fn = member as Function;
          if (fn != null) {
            yield return fn;
          }
        }
      }
    }
  }

  public static IEnumerable<Field> AllFields(IEnumerable<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      if (d is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members) {
          if (member is Field fn) {
            yield return fn;
          }
        }
      }
    }
  }

  public static IEnumerable<TopLevelDeclWithMembers> AllTypesWithMembers(List<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      if (d is TopLevelDeclWithMembers cl) {
        yield return cl;
      }
    }
  }

  /// <summary>
  /// Yields all functions and methods that are members of some type in the given list of
  /// declarations.
  /// Note, an iterator declaration is a type, in this sense.
  /// Note, if the given list are the top-level declarations of a module, the yield will include
  /// extreme predicates/lemmas but not their associated prefix predicates/lemmas (which are tucked
  /// into the extreme predicate/lemma's PrefixPredicate/PrefixLemma field).
  /// </summary>
  public static IEnumerable<ICallable> AllCallables(IEnumerable<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      if (d is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members.Where(member => member is ICallable and not ConstantField)) {
          yield return (ICallable)member;
          if (member is Function { ByMethodDecl: { } } f) {
            yield return f.ByMethodDecl;
          }
        }
      }
    }
  }

  /// <summary>
  /// Yields all functions and methods that are members of some type in the given list of
  /// declarations, including prefix lemmas and prefix predicates.
  /// </summary>
  public static IEnumerable<ICallable> AllCallablesIncludingPrefixDeclarations(IEnumerable<TopLevelDecl> declarations) {
    foreach (var decl in AllCallables(declarations)) {
      yield return decl;
      if (decl is ExtremeLemma extremeLemma) {
        yield return extremeLemma.PrefixLemma;
      } else if (decl is ExtremePredicate extremePredicate) {
        yield return extremePredicate.PrefixPredicate;
      }
    }
  }

  /// <summary>
  /// Yields all functions and methods that are members of some non-iterator type in the given
  /// list of declarations, as well as any IteratorDecl's in that list.
  /// </summary>
  public static IEnumerable<ICallable> AllItersAndCallables(IEnumerable<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      if (d is IteratorDecl) {
        yield return (IteratorDecl)d;
      } else if (d is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members.Where(member => member is ICallable)) {
          yield return (ICallable)member;
          if (member is Function { ByMethodDecl: { } } f) {
            yield return f.ByMethodDecl;
          }
        }
      }
    }
  }

  /// <summary>
  /// Emits the declarations in "declarations", but for each such declaration that is a class with
  /// a corresponding non-null type, also emits that non-null type *after* the class declaration.
  /// </summary>
  public static IEnumerable<TopLevelDecl> AllDeclarationsAndNonNullTypeDecls(IEnumerable<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      yield return d;
      if (d is ClassLikeDecl { NonNullTypeDecl: { } } cl) {
        yield return cl.NonNullTypeDecl;
      }
    }
  }

  public static IEnumerable<ExtremeLemma> AllExtremeLemmas(List<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      if (d is TopLevelDeclWithMembers cl) {
        foreach (var member in cl.Members) {
          if (member is ExtremeLemma extremeLemma) {
            yield return extremeLemma;
          }
        }
      }
    }
  }

  public bool IsEssentiallyEmptyModuleBody() {
    return TopLevelDecls.All(decl => decl.IsEssentiallyEmpty());
  }

  public IToken NameToken => tok;
  public override IEnumerable<Node> Children => (Attributes != null ?
      new List<Node> { Attributes } :
      Enumerable.Empty<Node>()).Concat<Node>(TopLevelDecls).
    Concat(RefinementQId == null ? Enumerable.Empty<Node>() : new Node[] { RefinementQId });

  private IEnumerable<Node> preResolveTopLevelDecls;
  private IEnumerable<Node> preResolvePrefixNamedModules;

  public override IEnumerable<Node> PreResolveChildren {
    get {
      var attributes = Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>();
      return attributes.Concat(preResolveTopLevelDecls ?? TopLevelDecls).Concat(
          (preResolvePrefixNamedModules ?? PrefixNamedModules.Select(tuple => tuple.Module)));
    }
  }

  public void PreResolveSnapshotForFormatter() {
    preResolveTopLevelDecls = TopLevelDecls.ToImmutableList();
    preResolvePrefixNamedModules = PrefixNamedModules.Select(tuple => tuple.Module).ToImmutableList();
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    return TopLevelDecls.SelectMany(m => m.Assumptions(decl));
  }

  public ModuleDefinition Clone(Cloner cloner) {
    return new ModuleDefinition(cloner, this);
  }

  /// <summary>
  /// Resolves the module definition.
  /// A return code of "false" is an indication of an error that may or may not have
  /// been reported in an error message. So, in order to figure out if m was successfully
  /// resolved, a caller has to check for both a change in error count and a "false"
  /// return value.
  /// </summary>
  public bool Resolve(ModuleSignature sig, ModuleResolver resolver, bool isAnExport = false) {
    Contract.Requires(resolver.AllTypeConstraints.Count == 0);
    Contract.Ensures(resolver.AllTypeConstraints.Count == 0);

    sig.VisibilityScope.Augment(resolver.ProgramResolver.SystemModuleManager.systemNameInfo.VisibilityScope);
    // make sure all imported modules were successfully resolved
    foreach (var d in TopLevelDecls) {
      if (d is AliasModuleDecl || d is AbstractModuleDecl) {
        ModuleSignature importSig;
        if (d is AliasModuleDecl) {
          var alias = (AliasModuleDecl)d;
          importSig = alias.TargetQId.Root != null ? alias.TargetQId.Root.Signature : alias.Signature;
        } else {
          importSig = ((AbstractModuleDecl)d).OriginalSignature;
        }

        if (importSig.ModuleDef is not { SuccessfullyResolved: true }) {
          return false;
        }
      } else if (d is LiteralModuleDecl) {
        var nested = (LiteralModuleDecl)d;
        if (!nested.ModuleDef.SuccessfullyResolved) {
          if (!IsEssentiallyEmptyModuleBody()) {
            // say something only if this will cause any testing to be omitted
            resolver.reporter.Error(MessageSource.Resolver, nested,
              "not resolving module '{0}' because there were errors in resolving its nested module '{1}'", Name,
              nested.Name);
          }

          return false;
        }
      }
    }

    var oldModuleInfo = resolver.moduleInfo;
    resolver.moduleInfo = ModuleResolver.MergeSignature(sig, resolver.ProgramResolver.SystemModuleManager.systemNameInfo);
    Type.PushScope(resolver.moduleInfo.VisibilityScope);
    ModuleResolver.ResolveOpenedImports(resolver.moduleInfo, this, resolver.Reporter, resolver); // opened imports do not persist
    var datatypeDependencies = new Graph<IndDatatypeDecl>();
    var codatatypeDependencies = new Graph<CoDatatypeDecl>();
    var allDeclarations = AllDeclarationsAndNonNullTypeDecls(TopLevelDecls).ToList();
    int prevErrorCount = resolver.reporter.Count(ErrorLevel.Error);
    resolver.ResolveTopLevelDecls_Signatures(this, sig, allDeclarations, datatypeDependencies, codatatypeDependencies);
    Contract.Assert(resolver.AllTypeConstraints.Count == 0); // signature resolution does not add any type constraints

    resolver.scope.PushMarker();
    resolver.scope.AllowInstance = false;
    resolver.ResolveAttributes(this, new ResolutionContext(new NoContext(EnclosingModule), false), true); // Must follow ResolveTopLevelDecls_Signatures, in case attributes refer to members
    resolver.scope.PopMarker();

    if (resolver.reporter.Count(ErrorLevel.Error) == prevErrorCount) {
      resolver.ResolveTopLevelDecls_Core(allDeclarations, datatypeDependencies, codatatypeDependencies, Name, isAnExport);
    }

    Type.PopScope(resolver.moduleInfo.VisibilityScope);
    resolver.moduleInfo = oldModuleInfo;
    return true;
  }

  public void ProcessPrefixNamedModules() {
    // moduleDecl.PrefixNamedModules is a list of pairs like:
    //     A.B.C  ,  module D { ... }
    // We collect these according to the first component of the prefix, like so:
    //     "A"   ->   (A.B.C  ,  module D { ... })
    var prefixModulesByFirstPart = PrefixNamedModules.
      GroupBy(prefixNameModule => prefixNameModule.Parts[0].val).
      ToDictionary(g => g.Key, g => g.ToList());

    PrefixNamedModules.Clear();

    // First, register all literal modules, and transferring their prefix-named modules downwards
    foreach (var subDecl in TopLevelDecls.OfType<LiteralModuleDecl>()) {
      // Transfer prefix-named modules downwards into the sub-module
      if (prefixModulesByFirstPart.TryGetValue(subDecl.Name, out var prefixModules)) {
        prefixModulesByFirstPart.Remove(subDecl.Name);
        prefixModules = prefixModules.ConvertAll(ShortenPrefix);
      }

      ProcessPrefixNamedModules(prefixModules, subDecl);
    }

    // Next, add new modules for any remaining entries in "prefixNames".
    foreach (var (name, prefixNamedModules) in prefixModulesByFirstPart) {
      var firstPartToken = prefixNamedModules.First().Parts[0];
      var modDef = new ModuleDefinition(firstPartToken.ToRange(), new Name(firstPartToken.ToRange(), name), new List<IToken>(), false,
        false, null, this, null, false);
      // Add the new module to the top-level declarations of its parent and then bind its names as usual

      // Use an empty cloneId because these are empty module declarations.
      var cloneId = Guid.Empty;
      var subDecl = new LiteralModuleDecl(modDef, this, cloneId);
      ResolvedPrefixNamedModules.Add(subDecl);
      ProcessPrefixNamedModules(prefixNamedModules.ConvertAll(ShortenPrefix), subDecl);
    }
  }

  private static void ProcessPrefixNamedModules(List<PrefixNameModule> prefixModules, LiteralModuleDecl subDecl) {
    // Transfer prefix-named modules downwards into the sub-module
    if (prefixModules != null) {
      foreach (var prefixModule in prefixModules) {
        if (prefixModule.Parts.Count == 0) {
          // change the parent, now that we have found the right parent module for the prefix-named module
          prefixModule.Module.ModuleDef.EnclosingModule = subDecl.ModuleDef;
          var sm = new LiteralModuleDecl(prefixModule.Module.ModuleDef, subDecl.ModuleDef,
            prefixModule.Module.CloneId);
          subDecl.ModuleDef.ResolvedPrefixNamedModules.Add(sm);
        } else {
          subDecl.ModuleDef.PrefixNamedModules.Add(prefixModule);
        }
      }
    }

    subDecl.ModuleDef.ProcessPrefixNamedModules();
  }

  public ModuleBindings BindModuleNames(ProgramResolver resolver, ModuleBindings parentBindings) {
    var bindings = new ModuleBindings(parentBindings);

    foreach (var subLiteral in TopLevelDecls.OfType<LiteralModuleDecl>()) {
      subLiteral.BindModuleNames(resolver, bindings);
    }

    // Go through import declarations (that is, AbstractModuleDecl's and AliasModuleDecl's).
    foreach (var subDecl in TopLevelDecls.OfType<ModuleDecl>()) {
      if (subDecl is not (AbstractModuleDecl or AliasModuleDecl)) {
        continue;
      }

      if (bindings.BindName(subDecl.Name, subDecl, null)) {
        // the add was successful
      } else {
        // there's already something with this name
        var yes = bindings.TryLookup(subDecl.tok, out var prevDecl);
        Contract.Assert(yes);
        if (prevDecl is AbstractModuleDecl || prevDecl is AliasModuleDecl) {
          resolver.Reporter.Error(MessageSource.Resolver, subDecl.tok, "Duplicate name of import: {0}", subDecl.Name);
        } else if (subDecl is AliasModuleDecl { Opened: true } importDecl && importDecl.TargetQId.Path.Count == 1 &&
                   importDecl.Name == importDecl.TargetQId.RootName()) {
          importDecl.ShadowsLiteralModule = true;
        } else {
          resolver.Reporter.Error(MessageSource.Resolver, subDecl.tok,
            "Import declaration uses same name as a module in the same scope: {0}", subDecl.Name);
        }
      }
    }

    return bindings;
  }

  private static PrefixNameModule ShortenPrefix(PrefixNameModule prefixNameModule) {
    Contract.Requires(prefixNameModule.Parts.Count != 0);
    var rest = prefixNameModule.Parts.Skip(1).ToList();
    return prefixNameModule with { Parts = rest };
  }

  public ModuleSignature RegisterTopLevelDecls(ModuleResolver resolver, bool useImports) {
    Contract.Requires(this != null);
    var sig = new ModuleSignature();
    sig.ModuleDef = this;
    sig.IsAbstract = IsAbstract;
    sig.VisibilityScope = new VisibilityScope();
    sig.VisibilityScope.Augment(VisibilityScope);

    // This is solely used to detect duplicates amongst the various e
    ISet<string> toplevels = new HashSet<string>();
    // Now add the things present
    var anonymousImportCount = 0;
    foreach (TopLevelDecl d in TopLevelDecls) {
      Contract.Assert(d != null);

      if (d is RevealableTypeDecl) {
        resolver.revealableTypes.Add((RevealableTypeDecl)d);
      }

      // register the class/datatype/module name
      TopLevelDecl registerThisDecl = null;
      string registerUnderThisName = null;
      if (d is ModuleExportDecl export) {
        if (sig.ExportSets.ContainsKey(d.Name)) {
          resolver.reporter.Error(MessageSource.Resolver, d, "duplicate name of export set: {0}", d.Name);
        } else {
          sig.ExportSets[d.Name] = export;
        }
      } else if (d is AliasModuleDecl importDecl && importDecl.ShadowsLiteralModule) {
        // add under an anonymous name
        registerThisDecl = d;
        registerUnderThisName = string.Format("{0}#{1}", d.Name, anonymousImportCount);
        anonymousImportCount++;
      } else if (toplevels.Contains(d.Name)) {
        resolver.reporter.Error(MessageSource.Resolver, d, "duplicate name of top-level declaration: {0}", d.Name);
      } else if (d is ClassLikeDecl { NonNullTypeDecl: { } nntd }) {
        registerThisDecl = nntd;
        registerUnderThisName = d.Name;
      } else {
        // Register each class and trait C under its own name, C. Below, we will change this for reference types (which includes all classes
        // and some of the traits), so that C? maps to the class/trait and C maps to the corresponding NonNullTypeDecl. We will need these
        // initial mappings in order to look through the parent traits of traits, below.
        registerThisDecl = d;
        registerUnderThisName = d.Name;
      }

      if (registerThisDecl != null) {
        toplevels.Add(registerUnderThisName);
        sig.TopLevels[registerUnderThisName] = registerThisDecl;
      }

      if (d is ModuleDecl) {
        // nothing to do
      } else if (d is TypeSynonymDecl) {
        // nothing more to register
      } else if (d is NewtypeDecl || d is AbstractTypeDecl) {
        var cl = (TopLevelDeclWithMembers)d;
        // register the names of the type members
        var members = new Dictionary<string, MemberDecl>();
        resolver.AddClassMembers(cl, members);
        cl.RegisterMembers(resolver, members);
      } else if (d is IteratorDecl) {
        var iter = (IteratorDecl)d;
        iter.Resolve(resolver);

      } else if (d is DefaultClassDecl defaultClassDecl) {
        var preMemberErrs = resolver.reporter.Count(ErrorLevel.Error);

        // register the names of the class members
        var members = new Dictionary<string, MemberDecl>();
        resolver.AddClassMembers(defaultClassDecl, members);
        defaultClassDecl.RegisterMembers(resolver, members);

        Contract.Assert(preMemberErrs != resolver.reporter.Count(ErrorLevel.Error) || !defaultClassDecl.Members.Except(members.Values).Any());

        foreach (MemberDecl m in members.Values) {
          Contract.Assert(!m.HasStaticKeyword || Attributes.Contains(m.Attributes, "opaque_reveal"));
          if (m is Function or Method or ConstantField) {
            sig.StaticMembers[m.Name] = m;
          }

          if (toplevels.Contains(m.Name)) {
            resolver.reporter.Error(MessageSource.Resolver, m.tok, $"duplicate declaration for name {m.Name}");
          } else {
            toplevels.Add(m.Name);
          }
        }

      } else if (d is ClassLikeDecl) {
        var cl = (ClassLikeDecl)d;
        var preMemberErrs = resolver.reporter.Count(ErrorLevel.Error);

        // register the names of the class members
        var members = new Dictionary<string, MemberDecl>();
        resolver.AddClassMembers(cl, members);
        cl.RegisterMembers(resolver, members);

        Contract.Assert(preMemberErrs != resolver.reporter.Count(ErrorLevel.Error) || !cl.Members.Except(members.Values).Any());

      } else if (d is DatatypeDecl) {
        var dt = (DatatypeDecl)d;

        // register the names of the constructors
        dt.ConstructorsByName = new();
        // ... and of the other members
        var members = new Dictionary<string, MemberDecl>();
        resolver.AddClassMembers(dt, members);

        foreach (DatatypeCtor ctor in dt.Ctors) {
          if (ctor.Name.EndsWith("?")) {
            resolver.reporter.Error(MessageSource.Resolver, ctor,
              "a datatype constructor name is not allowed to end with '?'");
          } else if (dt.ConstructorsByName.ContainsKey(ctor.Name)) {
            resolver.reporter.Error(MessageSource.Resolver, ctor, "Duplicate datatype constructor name: {0}", ctor.Name);
          } else {
            dt.ConstructorsByName.Add(ctor.Name, ctor);
            ctor.InheritVisibility(dt);

            // create and add the query "method" (field, really)
            var queryName = ctor.NameNode.Append("?");
            var query = new DatatypeDiscriminator(ctor.RangeToken, queryName, SpecialField.ID.UseIdParam, "is_" + ctor.GetCompileName(resolver.Options),
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
          var duplicates = new HashSet<Formal>();
          foreach (var formal in ctor.Formals) {
            MemberDecl previousMember = null;
            var localDuplicate = false;
            if (formal.HasName) {
              if (members.TryGetValue(formal.Name, out previousMember)) {
                localDuplicate = formalsUsedInThisCtor.Contains(formal.Name);
                if (localDuplicate) {
                  resolver.reporter.Error(MessageSource.Resolver, ctor,
                    "Duplicate use of deconstructor name in the same constructor: {0}", formal.Name);
                  duplicates.Add(formal);
                } else if (previousMember is DatatypeDestructor) {
                  // this is okay, if the destructor has the appropriate type; this will be checked later, after type checking
                } else {
                  resolver.reporter.Error(MessageSource.Resolver, ctor,
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

          foreach (var duplicate in duplicates) {
            ctor.Formals.Remove(duplicate);
          }
        }

        // finally, add any additional user-defined members
        dt.RegisterMembers(resolver, members);

      } else {
        var cl = (ValuetypeDecl)d;
        // register the names of the type members
        var members = new Dictionary<string, MemberDecl>();
        resolver.AddClassMembers(cl, members);
        cl.RegisterMembers(resolver, members);
      }
    }

    DetermineReferenceTypes(resolver, sig);

    // Now, for each reference type (class and some traits), register its possibly-null type.
    // In the big loop above, each class and trait was registered under its own name. We're now going to change that for the reference types.
    foreach (TopLevelDecl d in TopLevelDecls) {
      if (d is ClassLikeDecl { NonNullTypeDecl: { } nntd }) {
        var name = d.Name + "?";
        if (toplevels.Contains(name)) {
          resolver.reporter.Error(MessageSource.Resolver, d,
            "a module that already contains a top-level declaration '{0}' is not allowed to declare a reference type ({1}) '{2}'",
            name, d.WhatKind, d.Name);
        } else {
          toplevels.Add(name);
          toplevels.Add(d.Name);
          // change the mapping of d.Name to d.NonNullTypeDecl
          sig.TopLevels[d.Name] = nntd;
          sig.TopLevels[name] = d;
        }
      }
    }

    return sig;
  }

  private void DetermineReferenceTypes(ModuleResolver resolver, ModuleSignature sig) {
    // Figure out which TraitDecl's are reference types, and for each of these, create a corresponding NonNullTypeDecl.
    // To figure this out, we need to look at the parents of each TraitDecl, but those parents have not yet been resolved.
    // Since we just need the head of each parent, we'll do that name resolution here (and will redo it later, when each parent
    // type is resolved properly).
    //
    // Some inaccuracies can occur here, since possibly-null types have not yet been registered. However, since such types aren't allowed
    // as parents, it doesn't matter that they aren't available yet.
    //
    // If the head of a parent trait cannot be resolved, it is ignored here. An error will be reported later, when trait declarations are
    // resolved properly. Similarly, any cycle detected among the trait-parent heads is ignored. Cycles are detected (again) later and an
    // error will be reported then (in the meantime, we may have computed incorrectly whether or not a TraitDecl is a reference type, but
    // the cycle still remains, so an error will be reported later). (Btw, the later cycle detection detects not only cycles among parent
    // heads, but also among the type arguments of parent traits.)
    //
    // In the following dictionary, a TraitDecl not being present among the keys means it has not been visited in the InheritsFromObject traversal.
    // If a TraitDecl is a key and maps to "false", then it is currently being visited.
    // If a TraitDecl is a key and maps to "true", then its .IsReferenceTypeDecl has been computed and is ready to be used.
    var traitsProgress = new Dictionary<TraitDecl, bool>();
    foreach (var decl in TopLevelDecls.Where(d => d is TraitDecl)) {
      // Resolve a "path" to a top-level declaration, if possible. On error, return null.
      // The path is expected to consist of NameSegment or ExprDotName nodes.
      TopLevelDecl ResolveNamePath(Expression path) {
        // A single NameSegment is a little different, because it may refer to built-in type (of interest here: "object").
        if (path is NameSegment nameSegment) {
          if (sig.TopLevels.TryGetValue(nameSegment.Name, out var topLevelDecl)) {
            return topLevelDecl;
          } else if (resolver.moduleInfo != null && resolver.moduleInfo.TopLevels.TryGetValue(nameSegment.Name, out topLevelDecl)) {
            // For "object" and other reference-type declarations from other modules, we're picking up the NonNullTypeDecl; if so, return
            // the original declaration.
            return topLevelDecl is NonNullTypeDecl nntd ? nntd.ViewAsClass : topLevelDecl;
          } else if (resolver.ProgramResolver.SystemModuleManager.systemNameInfo.TopLevels.TryGetValue(nameSegment.Name, out topLevelDecl)) {
            // For "object" and other reference-type declarations from other modules, we're picking up the NonNullTypeDecl; if so, return
            // the original declaration.
            return topLevelDecl is NonNullTypeDecl nntd ? nntd.ViewAsClass : topLevelDecl;
          } else {
            return null;
          }
        }

        // convert the ExprDotName to a list of strings
        var names = new List<string>();
        while (path is ExprDotName exprDotName) {
          names.Add(exprDotName.SuffixName);
          path = exprDotName.Lhs;
        }
        names.Add(((NameSegment)path).Name);
        var s = sig;
        var i = names.Count;
        while (true) {
          i--;
          if (!s.TopLevels.TryGetValue(names[i], out var topLevelDecl)) {
            return null;
          } else if (i == 0) {
            // For reference-type declarations from other modules, we're picking up the NonNullTypeDecl; if so, return
            // the original declaration.
            return topLevelDecl is NonNullTypeDecl nntd ? nntd.ViewAsClass : topLevelDecl;
          } else if (topLevelDecl is ModuleDecl moduleDecl) {
            var signature = moduleDecl.AccessibleSignature(false);
            s = resolver.GetSignature(signature);
          } else {
            return null;
          }
        }
      }

      bool InheritsFromObject(TraitDecl traitDecl) {
        if (traitsProgress.TryGetValue(traitDecl, out var isDone)) {
          if (isDone) {
            return traitDecl.IsReferenceTypeDecl;
          } else {
            // there is a cycle among the parents, so we'll suppose the trait does inherit from "object"
            return true;
          }
        }
        traitsProgress[traitDecl] = false; // indicate that traitDecl is currently being visited

        var inheritsFromObject = traitDecl.IsObjectTrait;
        foreach (var parent in traitDecl.ParentTraits) {
          if (parent is UserDefinedType udt) {
            if (ResolveNamePath(udt.NamePath) is TraitDecl parentTrait) {
              if (parentTrait.EnclosingModuleDefinition == this) {
                inheritsFromObject = InheritsFromObject(parentTrait) || inheritsFromObject;
              } else {
                inheritsFromObject = parentTrait.IsReferenceTypeDecl || inheritsFromObject;
              }
            }
          }
        }

        traitDecl.SetUpAsReferenceType(resolver.Options.Get(CommonOptionBag.GeneralTraits) ? inheritsFromObject : true);
        traitsProgress[traitDecl] = true; // indicate that traitDecl.IsReferenceTypeDecl can now be called
        return inheritsFromObject;
      }

      InheritsFromObject((TraitDecl)decl);
    }
  }
}