using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public record PrefixNameModule(IReadOnlyList<IToken> Parts, LiteralModuleDecl Module);

public class ModuleDefinition : RangeNode, IDeclarationOrUsage, IAttributeBearingDeclaration, ICloneable<ModuleDefinition> {
  public Guid UniqueParseContentHash { get; set; }
  
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
  private readonly bool defaultClassFirst;

  public DefaultClassDecl DefaultClass { get; set; }

  public readonly List<TopLevelDecl> SourceDecls = new();
  [FilledInDuringResolution]
  public readonly List<TopLevelDecl> ResolvedPrefixNamedModules = new();
  [FilledInDuringResolution]
  public readonly List<PrefixNameModule> PrefixNamedModules = new();  // filled in by the parser; emptied by the resolver
  public virtual IEnumerable<TopLevelDecl> TopLevelDecls =>
    defaultClassFirst ? DefaultClasses.
        Concat(SourceDecls).
        Concat(ResolvedPrefixNamedModules)
      : SourceDecls.
        Concat(DefaultClasses).
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
    RefinementQId = original.RefinementQId;
    defaultClassFirst = original.defaultClassFirst;
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
    bool isBuiltinName, bool defaultClassFirst = false) : base(tok) {
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
    this.defaultClassFirst = defaultClassFirst;

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
      if (externArgs != null && 1 <= externArgs.Count && externArgs[0] is StringLiteralExpr) {
        compileName = (string)((StringLiteralExpr)externArgs[0]).Value;
      } else if (externArgs != null) {
        compileName = Name;
      } else {
        compileName = SanitizedName;
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
  public bool Resolve(ModuleSignature sig, Resolver resolver, bool isAnExport = false) {
    Contract.Requires(resolver.AllTypeConstraints.Count == 0);
    Contract.Ensures(resolver.AllTypeConstraints.Count == 0);

    sig.VisibilityScope.Augment(resolver.systemNameInfo.VisibilityScope);
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

        if (importSig.ModuleDef == null || !importSig.ModuleDef.SuccessfullyResolved) {
          if (!IsEssentiallyEmptyModuleBody()) {
            // say something only if this will cause any testing to be omitted
            resolver.reporter.Error(MessageSource.Resolver, d,
              "not resolving module '{0}' because there were errors in resolving its import '{1}'", Name, d.Name);
          }

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
    resolver.moduleInfo = Resolver.MergeSignature(sig, resolver.systemNameInfo);
    Type.PushScope(resolver.moduleInfo.VisibilityScope);
    Resolver.ResolveOpenedImports(resolver.moduleInfo, this, resolver); // opened imports do not persist
    var datatypeDependencies = new Graph<IndDatatypeDecl>();
    var codatatypeDependencies = new Graph<CoDatatypeDecl>();
    var allDeclarations = ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(TopLevelDecls).ToList();
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

  public ModuleBindings BindModuleNames(Resolver resolver, ModuleBindings parentBindings) {
    var bindings = new ModuleBindings(parentBindings);

    BindPrefixNamedModules(resolver, bindings);

    // Finally, go through import declarations (that is, AbstractModuleDecl's and AliasModuleDecl's).
    foreach (var tld in TopLevelDecls) {
      if (tld is AbstractModuleDecl || tld is AliasModuleDecl) {
        var subdecl = (ModuleDecl)tld;
        if (bindings.BindName(subdecl.Name, subdecl, null)) {
          // the add was successful
        } else {
          // there's already something with this name
          var yes = bindings.TryLookup(subdecl.tok, out var prevDecl);
          Contract.Assert(yes);
          if (prevDecl is AbstractModuleDecl || prevDecl is AliasModuleDecl) {
            resolver.reporter.Error(MessageSource.Resolver, subdecl.tok, "Duplicate name of import: {0}", subdecl.Name);
          } else if (tld is AliasModuleDecl importDecl && importDecl.Opened && importDecl.TargetQId.Path.Count == 1 &&
                     importDecl.Name == importDecl.TargetQId.rootName()) {
            importDecl.ShadowsLiteralModule = true;
          } else {
            resolver.reporter.Error(MessageSource.Resolver, subdecl.tok,
              "Import declaration uses same name as a module in the same scope: {0}", subdecl.Name);
          }
        }
      }
    }

    return bindings;
  }

  private void BindPrefixNamedModules(Resolver resolver, ModuleBindings bindings)
  {
    // moduleDecl.PrefixNamedModules is a list of pairs like:
    //     A.B.C  ,  module D { ... }
    // We collect these according to the first component of the prefix, like so:
    //     "A"   ->   (A.B.C  ,  module D { ... })
    var prefixModulesByFirstPart = new Dictionary<string, List<PrefixNameModule>>();
    foreach (var prefixNameModule in PrefixNamedModules)
    {
      var firstPartName = prefixNameModule.Parts[0].val;
      var prev = prefixModulesByFirstPart.GetOrCreate(firstPartName, () => new List<PrefixNameModule>());
      prev.Add(prefixNameModule);
    }

    PrefixNamedModules.Clear();

    // First, register all literal modules, and transferring their prefix-named modules downwards
    foreach (var subdecl in TopLevelDecls.OfType<LiteralModuleDecl>())
    {
      // Transfer prefix-named modules downwards into the sub-module
      if (prefixModulesByFirstPart.TryGetValue(subdecl.Name, out var prefixModules))
      {
        prefixModulesByFirstPart.Remove(subdecl.Name);
        prefixModules = prefixModules.ConvertAll(ShortenPrefix);
      }

      subdecl.BindModuleName(resolver, prefixModules, bindings);
    }

    // Next, add new modules for any remaining entries in "prefixNames".
    foreach (var entry in prefixModulesByFirstPart)
    {
      var prefixNamedModules = entry.Value;
      var tok = prefixNamedModules.First().Parts[0];
      var modDef = new ModuleDefinition(tok.ToRange(), new Name(tok.ToRange(), entry.Key), new List<IToken>(), false,
        false, null, this, null, false);
      // Add the new module to the top-level declarations of its parent and then bind its names as usual
      var subdecl = new LiteralModuleDecl(modDef, this);
      ResolvedPrefixNamedModules.Add(subdecl);
      subdecl.BindModuleName(resolver, prefixNamedModules.ConvertAll(ShortenPrefix), bindings);
    }
  }

  private PrefixNameModule ShortenPrefix(PrefixNameModule tup) {
    Contract.Requires(tup.Parts.Count != 0);
    var rest = tup.Parts.Skip(1).ToList();
    return tup with { Parts = rest };
  }
}