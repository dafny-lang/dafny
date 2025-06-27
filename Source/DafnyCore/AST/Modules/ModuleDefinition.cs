#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public record PrefixNameModule(DafnyOptions Options, IReadOnlyList<IOrigin> Parts, LiteralModuleDecl Module);

public enum ModuleKindEnum {
  Concrete,
  Abstract,
  Replaceable
}

public enum ImplementationKind {
  Refinement,
  Replacement
}

public record Implements(ImplementationKind Kind, ModuleQualifiedId Target);

public class ModuleDefinition : NodeWithOrigin, IAttributeBearingDeclaration, ICloneable<ModuleDefinition> {

  public static Option<bool> LegacyModuleNames = new("--legacy-module-names",
    @"
Generate module names in the older A_mB_mC style instead of the current A.B.C scheme".TrimStart()) {
    IsHidden = true
  };

  static ModuleDefinition() {
    DafnyOptions.RegisterLegacyUi(LegacyModuleNames, DafnyOptions.ParseBoolean, "Compilation options", legacyName: "legacyModuleNames", defaultValue: false);
    OptionRegistry.RegisterOption(LegacyModuleNames, OptionScope.Translation);
  }

  public IOrigin BodyStartTok = Token.NoToken;
  public string DafnyName => NameNode.StartToken.val; // The (not-qualified) name as seen in Dafny source code
  public Name NameNode { get; set; }

  public override bool SingleFileToken => !ResolvedPrefixNamedModules.Any();

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
      if (EnclosingModule == null || EnclosingModule.TryToAvoidName) {
        return Name;
      } else {
        return EnclosingModule.FullName + "." + Name;
      }
    }
  }
  /// <summary>
  /// The qualified module name, except the last segment when a nested module declaration is outside its enclosing module
  /// </summary>
  public List<IOrigin> PrefixIds;

  public ModuleDefinition? EnclosingModule;  // readonly, except can be changed by resolver for prefix-named modules when the real parent is discovered
  public Attributes? Attributes { get; set; }
  public string WhatKind => "module definition";
  public Implements? Implements; // null if no refinement base
  public bool SuccessfullyResolved;  // set to true upon successful resolution; modules that import an unsuccessfully resolved module are not themselves resolved
  public ModuleKindEnum ModuleKind;
  public bool IsFacade; // True iff this module represents a module facade (that is, an abstract interface)
  private bool IsBuiltinName => Name is "_System" or "_module"; // true if this is something like _System that shouldn't have it's name mangled.

  public DefaultClassDecl? DefaultClass { get; set; }

  public List<TopLevelDecl> SourceDecls = [];
  [FilledInDuringResolution]
  public List<TopLevelDecl> ResolvedPrefixNamedModules = [];
  [FilledInDuringResolution]
  public List<PrefixNameModule> PrefixNamedModules = [];  // filled in by the parser; emptied by the resolver

  [FilledInDuringResolution]
  public CallRedirector? CallRedirector { get; set; }

  public IEnumerable<TopLevelDecl> TopLevelDecls => DefaultClasses.
        Concat(SourceDecls).
        Concat(ResolvedPrefixNamedModules);

  public IEnumerable<IPointer<TopLevelDecl>> TopLevelDeclPointers =>
    (DefaultClass == null
      ? Enumerable.Empty<Pointer<TopLevelDecl>>()
      : new[] { new Pointer<TopLevelDecl>(() => DefaultClass, v => DefaultClass = (DefaultClassDecl)v) }).
    Concat(SourceDecls.ToPointers()).Concat(ResolvedPrefixNamedModules.ToPointers());

  public IEnumerable<TopLevelDecl> DefaultClasses {
    get { return DefaultClass == null ? Enumerable.Empty<TopLevelDecl>() : new TopLevelDecl[] { DefaultClass }; }
  }

  [FilledInDuringResolution]
  public Graph<ICallable> CallGraph = new();

  // This field is only populated if `defaultFunctionOpacity` is set to something other than transparent
  [FilledInDuringResolution]
  public Graph<ICallable> InterModuleCallGraph = new();

  [FilledInDuringResolution]
  public int Height;  // height in the topological sorting of modules;

  [FilledInDuringResolution]
  public Dictionary<Declaration, AccessibleMember> AccessibleMembers = new();

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Cce.NonNullElements(TopLevelDecls));
    Contract.Invariant(CallGraph != null);
  }

  public ModuleDefinition(Cloner cloner, ModuleDefinition original, Name name) : this(cloner, original) {
    NameNode = name;
  }

  public ModuleDefinition(Cloner cloner, ModuleDefinition original) : base(cloner, original) {
    NameNode = original.NameNode;
    PrefixIds = original.PrefixIds.Select(cloner.Origin).ToList();
    IsFacade = original.IsFacade;
    Attributes = original.Attributes;
    ModuleKind = original.ModuleKind;
    Implements = original.Implements == null ? null : original.Implements with { Target = new ModuleQualifiedId(cloner, original.Implements.Target) };
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

    if (cloner.CloneResolvedFields) {
      foreach (var tup in original.ResolvedPrefixNamedModules) {
        ResolvedPrefixNamedModules.Add(cloner.CloneDeclaration(tup, this));
      }

      Height = original.Height;
    }
  }

  [SyntaxConstructor]
  public ModuleDefinition(IOrigin origin, Name nameNode, List<IOrigin> prefixIds, ModuleKindEnum moduleKind,
    Implements? implements, [BackEdge] ModuleDefinition? enclosingModule, Attributes? attributes,
    List<TopLevelDecl> sourceDecls)
    : this(origin, nameNode, prefixIds, moduleKind, false, implements, enclosingModule, attributes, sourceDecls) {
  }

  public ModuleDefinition(IOrigin origin, Name nameNode, List<IOrigin> prefixIds, ModuleKindEnum moduleKind, bool isFacade,
    Implements? implements, ModuleDefinition? enclosingModule, Attributes? attributes, List<TopLevelDecl>? sourceDecls = null) : base(origin) {
    this.NameNode = nameNode;
    this.PrefixIds = prefixIds;
    this.Attributes = attributes;
    this.EnclosingModule = enclosingModule;
    this.Implements = implements;
    this.ModuleKind = moduleKind;
    this.IsFacade = isFacade;
    this.SourceDecls = sourceDecls ?? new();

    if (Name != "_System") {
      DefaultClass = new DefaultClassDecl(this, []);
    }
  }

  private VisibilityScope? visibilityScope;
  public VisibilityScope VisibilityScope =>
    visibilityScope ??= new VisibilityScope(this.SanitizedName);

  public virtual bool IsDefaultModule => false;

  public virtual bool TryToAvoidName => false;

  private string? sanitizedName = null;

  public void ClearNameCache() {
    sanitizedName = null;
    compileName = null;
  }

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

  string? compileName;

  public ModuleDefinition? GetImplementedModule() {
    return Implements is { Kind: ImplementationKind.Replacement } ? Implements.Target.Def : null;
  }

  public string GetCompileName(DafnyOptions options) {
    if (compileName != null) {
      return compileName;
    }

    var implemented = GetImplementedModule();
    if (implemented != null) {
      return implemented.GetCompileName(options);
    }

    var externArgs = options.DisallowExterns ? null : Attributes.FindExpressions(this.Attributes, "extern");
    var nonExternSuffix = (options.Get(CommonOptionBag.AddCompileSuffix) && Name != "_module" && Name != "_System" ? "_Compile" : "");
    if (externArgs != null && 1 <= externArgs.Count && externArgs[0] is StringLiteralExpr) {
      compileName = (string)((StringLiteralExpr)externArgs[0]).Value!;
    } else if (externArgs != null) {
      compileName = Name + nonExternSuffix;
    } else {

      if (IsBuiltinName) {
        compileName = Name;
      } else if (EnclosingModule is { TryToAvoidName: false }) {
        if (options.Get(LegacyModuleNames)) {
          compileName = SanitizedName;
        } else {
          // Include all names in the module tree path, to disambiguate when compiling
          // a flat list of modules.
          // Use an "underscore-escaped" character as a module name separator, since
          // underscores are already used as escape characters in SanitizeName()
          compileName = EnclosingModule.GetCompileName(options) + options.Backend.ModuleSeparator + NonglobalVariable.SanitizeName(Name);
        }
      } else {
        compileName = NonglobalVariable.SanitizeName(Name);
      }

      compileName += nonExternSuffix;
    }

    return compileName;
  }

  /// <summary>
  /// Determines if "a" and "b" are in the same strongly connected component of the call graph, that is,
  /// if "a" and "b" are mutually recursive.
  /// Assumes that CallGraph has already been filled in for the modules containing "a" and "b".
  /// </summary>
  public static bool InSameSCC(ICallable a, ICallable b) {
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

  public IOrigin NavigationToken => NameNode.Origin;
  public override IEnumerable<INode> Children =>
    Attributes.AsEnumerable().
    Concat<Node>(DefaultClasses).
    Concat(SourceDecls).
    Concat(PrefixNamedModules.Any() ? PrefixNamedModules.Select(m => m.Module) : ResolvedPrefixNamedModules).
    Concat(Implements == null ? Enumerable.Empty<Node>() : new Node[] { Implements.Target });

  private IEnumerable<Node>? preResolveTopLevelDecls;
  private IEnumerable<Node>? preResolvePrefixNamedModules;

  public override IEnumerable<INode> PreResolveChildren {
    get {
      return Attributes.AsEnumerable().
        Concat<Node>(preResolveTopLevelDecls ?? TopLevelDecls).
        Concat(preResolvePrefixNamedModules ?? PrefixNamedModules.Select(tuple => tuple.Module));
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
  public bool Resolve(ModuleSignature sig, ModuleResolver resolver, string? exportSetName = null) {
    Contract.Requires(resolver.AllTypeConstraints.Count == 0);
    Contract.Ensures(resolver.AllTypeConstraints.Count == 0);

    sig.VisibilityScope.Augment(resolver.ProgramResolver.SystemModuleManager.systemNameInfo.VisibilityScope);
    // make sure all imported modules were successfully resolved
    foreach (var d in TopLevelDecls) {
      if (d is AliasModuleDecl importDecl) {
        var importSig = importDecl.TargetQId.Root != null ? importDecl.TargetQId.Root.Signature : importDecl.Signature;
        if (importSig is not { ModuleDef: { SuccessfullyResolved: true } }) {
          return false;
        }
      } else if (d is AbstractModuleDecl abstractImportDecl) {
        var importSig = abstractImportDecl.OriginalSignature;
        if (importSig is not { ModuleDef: { SuccessfullyResolved: true } }) {
          return false;
        }
      } else if (d is LiteralModuleDecl nestedModuleDecl) {
        if (!nestedModuleDecl.ModuleDef.SuccessfullyResolved) {
          if (!IsEssentiallyEmptyModuleBody()) {
            // say something only if this will cause any testing to be omitted
            resolver.reporter.Error(MessageSource.Resolver, nestedModuleDecl.NameNode,
              "not resolving module '{0}' because there were errors in resolving its nested module '{1}'", Name,
              nestedModuleDecl.Name);
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
      resolver.ResolveTopLevelDecls_Core(allDeclarations, datatypeDependencies, codatatypeDependencies,
        exportSetName == null ? Name : $"{Name} export {exportSetName}", exportSetName != null);
    }

    Type.PopScope(resolver.moduleInfo.VisibilityScope);
    resolver.moduleInfo = oldModuleInfo;


    // Build the AccessibleMembers dictionary
    foreach (var d in TopLevelDecls) {
      if (d is AliasModuleDecl || d is AbstractModuleDecl) {
        ModuleSignature importSig;
        if (d is AliasModuleDecl alias) {
          if (alias.TargetQId.Decl is not null) {
            importSig = alias.TargetQId.Decl.Signature;
          } else if (alias.TargetQId.Root is not null) {
            importSig = alias.TargetQId.Root.Signature;
          } else {
            importSig = alias.Signature;
          }
        } else {
          importSig = ((AbstractModuleDecl)d).OriginalSignature;
        }

        var origMod = importSig.ModuleDef;

        var exports = d is AliasModuleDecl ? ((AliasModuleDecl)d).Exports : ((AbstractModuleDecl)d).Exports;
        var exportSet = exports.Any() ? exports.First().val : null;

        foreach (var (decl, accMember) in origMod.AccessibleMembers) {
          if (IsDeclExported(origMod, exportSet, decl, out var isDeclRevealed)) {
            var newAccMember = accMember.Clone();

            newAccMember.AccessPath.Insert(0, TopLevelDeclToNameSegment(d, d.Origin));
            newAccMember.IsRevealed = newAccMember.IsRevealed && isDeclRevealed;
            AddAccessibleMember(decl, newAccMember);
          }
        }

        var newAccessibleMember = new AccessibleMember();
        AddAccessibleMember(d, newAccessibleMember);

      } else if (d is LiteralModuleDecl) {
        var nested = (LiteralModuleDecl)d;

        foreach (var (decl, accMember) in nested.ModuleDef.AccessibleMembers) {
          if (IsDeclExported(nested.ModuleDef, null, decl, out var isDeclRevealed)) {
            var newAccMember = accMember.Clone();

            newAccMember.AccessPath.Insert(0, TopLevelDeclToNameSegment(d, d.Origin));
            newAccMember.IsRevealed = newAccMember.IsRevealed && isDeclRevealed;

            AddAccessibleMember(decl, newAccMember);
          }
        }

        var newAccessibleMember = new AccessibleMember();
        AddAccessibleMember(d, newAccessibleMember);

      } else if (d is TopLevelDeclWithMembers tld) {
        var memberList = tld.Members;

        foreach (var mem in memberList) {
          var accessPath = new List<NameSegment> { TopLevelDeclToNameSegment(d, d.Origin) };
          var newAccessibleMember = new AccessibleMember(accessPath);
          AddAccessibleMember(mem, newAccessibleMember);
        }
      }
    }

    return true;
  }

  private static NameSegment TopLevelDeclToNameSegment(TopLevelDecl decl, IOrigin tok) {
    var typeArgs = new List<Type>();

    foreach (var arg in decl.TypeArgs) {
      typeArgs.Add(new IntType());
    }

    return new NameSegment(tok, decl.Name, typeArgs);
  }

  private bool IsDeclExported(ModuleDefinition moduleDefinition, string? exportSetName, Declaration decl, out bool isItRevealed) {
    isItRevealed = true;

    exportSetName ??= moduleDefinition.Name;

    var moduleExports = moduleDefinition.TopLevelDecls.Where(decl => decl is ModuleExportDecl && decl.Name == exportSetName).ToList();

    if (!moduleExports.Any()) {
      return true;
    }

    var exportSignatures = ((ModuleExportDecl)moduleExports.First()).Exports.Where(export => export.Decl == decl).ToList();

    if (!exportSignatures.Any()) {
      return false;
    }

    isItRevealed = !exportSignatures.First().Opaque;
    return true;
  }

  private void AddAccessibleMember(Declaration accessibleDecl, AccessibleMember newVal) {
    if (AccessibleMembers.TryGetValue(accessibleDecl, out var oldVal)) {
      newVal = !oldVal.IsRevealed && newVal.IsRevealed ? newVal : oldVal;
    }

    AccessibleMembers[accessibleDecl] = newVal;
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
      if (prefixModulesByFirstPart.Remove(subDecl.Name, out var prefixModules)) {
        prefixModules = prefixModules.ConvertAll(ShortenPrefix);
      }

      ProcessPrefixNamedModules(prefixModules, subDecl);
    }

    // Next, add new modules for any remaining entries in "prefixNames".
    foreach (var (name, prefixNamedModules) in prefixModulesByFirstPart) {
      var prefixNameModule = prefixNamedModules.First();
      var firstPartToken = prefixNameModule.Parts[0];
      var modDef = new ModuleDefinition(SourceOrigin.NoToken, new Name(firstPartToken, name), [], ModuleKindEnum.Concrete,
        false, null, this, null);
      // Add the new module to the top-level declarations of its parent and then bind its names as usual

      // Use an empty cloneId because these are empty module declarations.
      var cloneId = Guid.Empty;
      var subDecl = new LiteralModuleDecl(prefixNameModule.Options, modDef, this, cloneId);
      ResolvedPrefixNamedModules.Add(subDecl);
      // only set the range on the last submodule of the chain, since the others can be part of multiple files
      ProcessPrefixNamedModules(prefixNamedModules.ConvertAll(ShortenPrefix), subDecl);
    }
  }

  private static void ProcessPrefixNamedModules(List<PrefixNameModule>? prefixModules, LiteralModuleDecl subDecl) {
    // Transfer prefix-named modules downwards into the sub-module
    if (prefixModules != null) {
      foreach (var prefixModule in prefixModules) {
        if (prefixModule.Parts.Count == 0) {
          // change the parent, now that we have found the right parent module for the prefix-named module
          prefixModule.Module.ModuleDef.EnclosingModule = subDecl.ModuleDef;
          var sm = new LiteralModuleDecl(prefixModule.Options, prefixModule.Module.ModuleDef, subDecl.ModuleDef,
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
        var existingModuleIsFound = bindings.TryLookup(subDecl.Name, out var prevDecl);
        Contract.Assert(existingModuleIsFound);
        if (prevDecl is AbstractModuleDecl || prevDecl is AliasModuleDecl) {
          resolver.Reporter.Error(MessageSource.Resolver, subDecl.Origin, "Duplicate name of import: {0}", subDecl.Name);
        } else if (subDecl is AliasModuleDecl { Opened: true } importDecl && importDecl.TargetQId.Path.Count == 1 &&
                   importDecl.Name == importDecl.TargetQId.RootName()) {
          importDecl.ShadowsLiteralModule = true;
        } else {
          resolver.Reporter.Error(MessageSource.Resolver, subDecl.Origin,
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

  private static List<(string, string)> incompatibleAttributePairs =
    [("rlimit", "resource_limit")];

  private void CheckIncompatibleAttributes(ModuleResolver resolver, Attributes? attrs) {
    foreach (var pair in incompatibleAttributePairs) {
      var attr1 = Attributes.Find(attrs, pair.Item1);
      var attr2 = Attributes.Find(attrs, pair.Item2);
      if (attr1 is not null && attr2 is not null) {
        resolver.reporter.Error(MessageSource.Resolver, attr1.Origin,
            $"the {pair.Item1} and {pair.Item2} attributes cannot be used together");
      }
    }
  }

  public ModuleSignature RegisterTopLevelDecls(ModuleResolver resolver, bool useImports) {
    Contract.Requires(this != null);
    var sig = new ModuleSignature();
    sig.ModuleDef = this;
    sig.IsAbstract = ModuleKind == ModuleKindEnum.Abstract;
    sig.VisibilityScope = new VisibilityScope();
    sig.VisibilityScope.Augment(VisibilityScope);

    // This is solely used to detect duplicates amongst the various e
    Dictionary<string, INode> toplevels = new();
    var duplicateNames = new HashSet<string>();
    // Now add the things present
    var anonymousImportCount = 0;
    foreach (TopLevelDecl d in TopLevelDecls) {
      Contract.Assert(d != null);

      if (d is RevealableTypeDecl) {
        resolver.revealableTypes.Add((RevealableTypeDecl)d);
      }

      // register the class/datatype/module name
      TopLevelDecl? registerThisDecl = null;
      var registerUnderThisName = d.Name;
      var duplicateName = duplicateNames.Contains(registerUnderThisName);
      INode? existingTopLevel = null;
      if (d is ModuleExportDecl export) {
        if (duplicateName || !sig.ExportSets.TryAdd(registerUnderThisName, export)) {
          duplicateName = true;
          resolver.reporter.Error(MessageSource.Resolver, d, "duplicate name of export set: {0}", registerUnderThisName);
        }
      } else if (d is AliasModuleDecl { ShadowsLiteralModule: true }) {
        // add under an anonymous name
        registerThisDecl = d;
        registerUnderThisName = $"{d.Name}#{anonymousImportCount}";
        anonymousImportCount++;
      } else if (duplicateName || toplevels.TryGetValue(d.Name, out existingTopLevel)) {
        duplicateName = true;
        var origin = existingTopLevel != null ? new NestedOrigin(d.Origin, existingTopLevel.Origin) : d.Origin;
        resolver.reporter.Error(MessageSource.Resolver, origin, "duplicate name of top-level declaration: {0}", d.Name);
      } else if (d is ClassLikeDecl { NonNullTypeDecl: { } nntd }) {
        registerThisDecl = nntd;
      } else {
        // Register each class and trait C under its own name, C. Below, we will change this for reference types (which includes all classes
        // and some of the traits), so that C? maps to the class/trait and C maps to the corresponding NonNullTypeDecl. We will need these
        // initial mappings in order to look through the parent traits of traits, below.
        registerThisDecl = d;
      }

      if (registerThisDecl != null) {
        toplevels[registerUnderThisName] = d;
        sig.TopLevels[registerUnderThisName] = registerThisDecl;
      } else if (duplicateName) {
        duplicateNames.Add(registerUnderThisName);
        toplevels.Remove(registerUnderThisName);
        sig.TopLevels.Remove(registerUnderThisName);
      }

      if (d is ModuleDecl) {
        // nothing to do
      } else if (d is TypeSynonymDecl) {
        // nothing more to register
      } else if (d is NewtypeDecl or AbstractTypeDecl) {
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

          CheckIncompatibleAttributes(resolver, m.Attributes);

          if (m is Function or MethodOrConstructor or ConstantField) {
            sig.StaticMembers[m.Name] = m;
          }

          if (!toplevels.TryAdd(m.Name, m)) {
            resolver.reporter.Error(MessageSource.Resolver, m.Origin, $"duplicate declaration for name {m.Name}");
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
            var query = new DatatypeDiscriminator(ctor.Origin, queryName, SpecialField.ID.UseIdParam, "is_" + ctor.GetCompileName(resolver.Options),
              ctor.IsGhost, Type.Bool, null);
            query.InheritVisibility(dt);
            query.EnclosingClass = dt; // resolve here
            members.Add(queryName.Value, query);
            ctor.QueryField = query;

            // also register the constructor name globally
            if (sig.Ctors.TryGetValue(ctor.Name, out var pair)) {
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
            MemberDecl? previousMember = null;
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
              dtor = new DatatypeDestructor(formal.Origin, ctor, formal, formal.NameNode, "dtor_" + formal.CompileName,
                formal.IsGhost, formal.Type, null);
              dtor.InheritVisibility(dt);
              dtor.EnclosingClass = dt; // resolve here
              if (formal.HasName && !localDuplicate && previousMember == null) {
                // the destructor has an explict name and there was no member at all with this name before
                members.Add(formal.Name, dtor);
              }
            }

            if (!localDuplicate) {
              ctor.Destructors.Add(dtor);
            }
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
      if (d is ClassLikeDecl { NonNullTypeDecl: { } nntd } && !duplicateNames.Contains(d.Name)) {
        var name = d.Name + "?";
        if (toplevels.ContainsKey(name)) {
          resolver.reporter.Error(MessageSource.Resolver, d,
            "a module that already contains a top-level declaration '{0}' is not allowed to declare a reference type ({1}) '{2}'",
            name, d.WhatKind, d.Name);
        } else {
          toplevels[name] = d;
          toplevels[d.Name] = d;
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
    var openedImports = TopLevelDecls.OfType<ModuleDecl>().Where(d => d.Opened).ToList();
    var traitsProgress = new Dictionary<TraitDecl, bool>();
    foreach (var decl in TopLevelDecls.Where(d => d is TraitDecl)) {
      // Resolve a "path" to a top-level declaration, if possible. On error, return null.
      // The path is expected to consist of NameSegment or ExprDotName nodes.
      TopLevelDecl? ResolveNamePath(Expression path) {
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
          }
          // Look through opened imports (which haven't yet been added to the module's signature). There may be ambiguities among the declarations
          // of these opened imports. Still, we'll just pick the first declaration that matches, if any. If this declaration turns out to be
          // ambiguous, then an error will be reported later; in the meantime, all that would have happened is that the resolved name path here
          // is referring to some top-level declaration that won't accurately answer the question of whether "path" is referring to a reference
          // type or not.
          foreach (var importDecl in openedImports) {
            Contract.Assert(importDecl is AliasModuleDecl or AbstractModuleDecl); // only these ModuleDecl's can be .Opened
            if (importDecl.AccessibleSignature(false).TopLevels.TryGetValue(nameSegment.Name, out topLevelDecl)) {
              // For "object" and other reference-type declarations from other modules, we're picking up the NonNullTypeDecl; if so, return
              // the original declaration.
              return topLevelDecl is NonNullTypeDecl nntd ? nntd.ViewAsClass : topLevelDecl;
            }
          }
          // We didn't find "path"
          return null;
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
        foreach (var parent in traitDecl.Traits) {
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

        traitDecl.SetUpAsReferenceType(resolver.Options.Get(CommonOptionBag.GeneralTraits) == CommonOptionBag.GeneralTraitsOptions.Legacy || inheritsFromObject);
        traitsProgress[traitDecl] = true; // indicate that traitDecl.IsReferenceTypeDecl can now be called
        return inheritsFromObject;
      }

      InheritsFromObject((TraitDecl)decl);
    }

  }

  public LiteralModuleDecl? EnclosingLiteralModuleDecl { get; set; }

  public string GetDescription(DafnyOptions options) {
    return $"module {Name}";
  }
}