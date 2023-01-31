using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public abstract class Declaration : INamedRegion, IAttributeBearingDeclaration, IDeclarationOrUsage {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
  }

  public static string IdProtect(string name) {
    return DafnyOptions.O.Backend.PublicIdProtect(name);
  }

  public IToken TokenWithTrailingDocString = Token.NoToken;
  public Name MyName;

  public override IToken Tok => MyName.StartToken;
  public IToken NameToken => MyName.StartToken;
  
  public string Name => MyName.Value;
  public bool IsRefining;

  private VisibilityScope opaqueScope = new VisibilityScope();
  private VisibilityScope revealScope = new VisibilityScope();

  private bool scopeIsInherited = false;

  public override IEnumerable<AssumptionDescription> Assumptions() {
    if (Attributes.Contains(Attributes, "axiom")) {
      yield return AssumptionDescription.HasAxiomAttribute;
    }

    if (Attributes.Find(Attributes, "verify") is Attributes va &&
        va.Args.Count == 1 && Expression.IsBoolLiteral(va.Args[0], out var verify) &&
        verify == false) {
      yield return AssumptionDescription.HasVerifyFalseAttribute;
    }
  }

  public virtual bool CanBeExported() {
    return true;
  }

  public virtual bool CanBeRevealed() {
    return false;
  }

  public bool ScopeIsInherited { get { return scopeIsInherited; } }

  public void AddVisibilityScope(VisibilityScope scope, bool IsOpaque) {
    if (IsOpaque) {
      opaqueScope.Augment(scope);
    } else {
      revealScope.Augment(scope);
    }
  }

  public void InheritVisibility(Declaration d, bool onlyRevealed = true) {
    Contract.Assert(opaqueScope.IsEmpty());
    Contract.Assert(revealScope.IsEmpty());
    scopeIsInherited = false;

    revealScope = d.revealScope;

    if (!onlyRevealed) {
      opaqueScope = d.opaqueScope;
    }
    scopeIsInherited = true;

  }

  public bool IsRevealedInScope(VisibilityScope scope) {
    return revealScope.VisibleInScope(scope);
  }

  public bool IsVisibleInScope(VisibilityScope scope) {
    return IsRevealedInScope(scope) || opaqueScope.VisibleInScope(scope);
  }

  protected string sanitizedName;
  public virtual string SanitizedName => sanitizedName ??= NonglobalVariable.SanitizeName(Name);

  protected string compileName;
  public virtual string CompileName {
    get {
      if (compileName == null) {
        IsExtern(out _, out compileName);
        compileName ??= SanitizedName;
      }
      return compileName;
    }
  }

  public bool IsExtern(out string/*?*/ qualification, out string/*?*/ name) {
    // ensures result==false ==> qualification == null && name == null
    Contract.Ensures(Contract.Result<bool>() || (Contract.ValueAtReturn(out qualification) == null && Contract.ValueAtReturn(out name) == null));
    // ensures result==true ==> qualification != null ==> name != null
    Contract.Ensures(!Contract.Result<bool>() || Contract.ValueAtReturn(out qualification) == null || Contract.ValueAtReturn(out name) != null);

    qualification = null;
    name = null;
    if (!DafnyOptions.O.DisallowExterns) {
      var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
      if (externArgs != null) {
        if (externArgs.Count == 0) {
          return true;
        } else if (externArgs.Count == 1 && externArgs[0] is StringLiteralExpr) {
          name = externArgs[0].AsStringLiteral();
          return true;
        } else if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
          qualification = externArgs[0].AsStringLiteral();
          name = externArgs[1].AsStringLiteral();
          return true;
        }
      }
    }
    return false;
  }
  public Attributes Attributes;  // readonly, except during class merging in the refinement transformations and when changed by Compiler.MarkCapitalizationConflict
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;

  protected Declaration(RangeToken rangeToken, Name name, Attributes attributes, bool isRefining) : base(rangeToken) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    this.MyName = name;
    this.Attributes = attributes;
    this.IsRefining = isRefining;
  }

  [Pure]
  public override string ToString() {
    Contract.Ensures(Contract.Result<string>() != null);
    return Name;
  }

  internal FreshIdGenerator IdGenerator = new();
  public override IEnumerable<Node> Children => (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>());
}

public class TypeParameter : TopLevelDecl {
  public interface ParentType {
    string FullName { get; }
  }

  public override string WhatKind => "type parameter";

  ParentType parent;
  public ParentType Parent {
    get {
      return parent;
    }
    set {
      Contract.Requires(Parent == null);  // set it only once
      Contract.Requires(value != null);
      parent = value;
    }
  }

  public override string SanitizedName {
    get {
      if (sanitizedName == null) {
        var name = Name;
        if (parent is MemberDecl && !name.StartsWith("_")) {
          // prepend "_" to type parameters of functions and methods, to ensure they don't clash with type parameters of the enclosing type
          name = "_" + name;
        }
        sanitizedName = NonglobalVariable.SanitizeName(name);
      }
      return sanitizedName;
    }
  }

  public override string CompileName => SanitizedName; // Ignore :extern

  /// <summary>
  /// NonVariant_Strict     (default) - non-variant, no uses left of an arrow
  /// NonVariant_Permissive    !      - non-variant
  /// Covariant_Strict         +      - co-variant, no uses left of an arrow
  /// Covariant_Permissive     *      - co-variant
  /// Contravariant            -      - contra-variant
  /// </summary>
  public enum TPVarianceSyntax { NonVariant_Strict, NonVariant_Permissive, Covariant_Strict, Covariant_Permissive, Contravariance }
  public enum TPVariance { Co, Non, Contra }
  public static TPVariance Negate(TPVariance v) {
    switch (v) {
      case TPVariance.Co:
        return TPVariance.Contra;
      case TPVariance.Contra:
        return TPVariance.Co;
      default:
        return v;
    }
  }
  public static int Direction(TPVariance v) {
    switch (v) {
      case TPVariance.Co:
        return 1;
      case TPVariance.Contra:
        return -1;
      default:
        return 0;
    }
  }
  public TPVarianceSyntax VarianceSyntax;
  public TPVariance Variance {
    get {
      switch (VarianceSyntax) {
        case TPVarianceSyntax.Covariant_Strict:
        case TPVarianceSyntax.Covariant_Permissive:
          return TPVariance.Co;
        case TPVarianceSyntax.NonVariant_Strict:
        case TPVarianceSyntax.NonVariant_Permissive:
          return TPVariance.Non;
        case TPVarianceSyntax.Contravariance:
          return TPVariance.Contra;
        default:
          Contract.Assert(false);  // unexpected VarianceSyntax
          throw new cce.UnreachableException();
      }
    }
  }
  public bool StrictVariance {
    get {
      switch (VarianceSyntax) {
        case TPVarianceSyntax.Covariant_Strict:
        case TPVarianceSyntax.NonVariant_Strict:
          return true;
        case TPVarianceSyntax.Covariant_Permissive:
        case TPVarianceSyntax.NonVariant_Permissive:
        case TPVarianceSyntax.Contravariance:
          return false;
        default:
          Contract.Assert(false);  // unexpected VarianceSyntax
          throw new cce.UnreachableException();
      }
    }
  }

  public enum EqualitySupportValue { Required, InferredRequired, Unspecified }
  public struct TypeParameterCharacteristics {
    public RangeToken RangeToken = null;
    public EqualitySupportValue EqualitySupport;  // the resolver may change this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
    public Type.AutoInitInfo AutoInit;
    public bool HasCompiledValue => AutoInit == Type.AutoInitInfo.CompilableValue;
    public bool IsNonempty => AutoInit != Type.AutoInitInfo.MaybeEmpty;
    public bool ContainsNoReferenceTypes;
    public TypeParameterCharacteristics(bool dummy) {
      EqualitySupport = EqualitySupportValue.Unspecified;
      AutoInit = Type.AutoInitInfo.MaybeEmpty;
      ContainsNoReferenceTypes = false;
    }
    public TypeParameterCharacteristics(EqualitySupportValue eqSupport, Type.AutoInitInfo autoInit, bool containsNoReferenceTypes) {
      EqualitySupport = eqSupport;
      AutoInit = autoInit;
      ContainsNoReferenceTypes = containsNoReferenceTypes;
    }
  }
  public TypeParameterCharacteristics Characteristics;
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != EqualitySupportValue.Unspecified; }
  }

  public bool NecessaryForEqualitySupportOfSurroundingInductiveDatatype = false;  // computed during resolution; relevant only when Parent denotes an IndDatatypeDecl

  public bool IsToplevelScope { // true if this type parameter is on a toplevel (ie. class C<T>), and false if it is on a member (ie. method m<T>(...))
    get { return parent is TopLevelDecl; }
  }
  public int PositionalIndex; // which type parameter this is (ie. in C<S, T, U>, S is 0, T is 1 and U is 2).

  public TypeParameter(RangeToken rangeToken, Name name, TPVarianceSyntax varianceS, TypeParameterCharacteristics characteristics)
    : base(rangeToken, name, null, new List<TypeParameter>(), null, false) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Characteristics = characteristics;
    VarianceSyntax = varianceS;
  }

  public TypeParameter(RangeToken rangeToken, Name name, TPVarianceSyntax varianceS)
    : this(rangeToken, name, varianceS, new TypeParameterCharacteristics(false)) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
  }

  public TypeParameter(RangeToken tok, Name name, int positionalIndex, ParentType parent)
     : this(tok, name, TPVarianceSyntax.NonVariant_Strict) {
    PositionalIndex = positionalIndex;
    Parent = parent;
  }

  public override string FullName {
    get {
      // when debugging, print it all:
      return /* Parent.FullName + "." + */ Name;
    }
  }

  public static TypeParameterCharacteristics GetExplicitCharacteristics(TopLevelDecl d) {
    Contract.Requires(d != null);
    TypeParameterCharacteristics characteristics = new TypeParameterCharacteristics(false);
    if (d is OpaqueTypeDecl) {
      var dd = (OpaqueTypeDecl)d;
      characteristics = dd.Characteristics;
    } else if (d is TypeSynonymDecl) {
      var dd = (TypeSynonymDecl)d;
      characteristics = dd.Characteristics;
    }
    if (characteristics.EqualitySupport == EqualitySupportValue.InferredRequired) {
      return new TypeParameterCharacteristics(EqualitySupportValue.Unspecified, characteristics.AutoInit, characteristics.ContainsNoReferenceTypes);
    } else {
      return characteristics;
    }
  }

  public static Dictionary<TypeParameter, Type> SubstitutionMap(List<TypeParameter> formals, List<Type> actuals) {
    Contract.Requires(formals != null);
    Contract.Requires(actuals != null);
    Contract.Requires(formals.Count == actuals.Count);
    var subst = new Dictionary<TypeParameter, Type>();
    for (int i = 0; i < formals.Count; i++) {
      subst.Add(formals[i], actuals[i]);
    }
    return subst;
  }

}

// Represents a submodule declaration at module level scope
public abstract class ModuleDecl : TopLevelDecl {
  public override string WhatKind { get { return "module"; } }
  [FilledInDuringResolution] public ModuleSignature Signature; // filled in topological order.
  public virtual ModuleSignature AccessibleSignature(bool ignoreExports) {
    Contract.Requires(Signature != null);
    return Signature;
  }
  public virtual ModuleSignature AccessibleSignature() {
    Contract.Requires(Signature != null);
    return Signature;
  }
  public int Height;

  public readonly bool Opened;

  public ModuleDecl(RangeToken rangeToken, Name name, ModuleDefinition parent, bool opened, bool isRefining)
    : base(rangeToken, name, parent, new List<TypeParameter>(), null, isRefining) {
    Height = -1;
    Signature = null;
    Opened = opened;
  }
  public abstract object Dereference();

  public int? ResolvedHash { get; set; }

  public override bool IsEssentiallyEmpty() {
    // A module or import is considered "essentially empty" to its parents, but the module is going to be resolved by itself.
    return true;
  }
}
// Represents module X { ... }
public class LiteralModuleDecl : ModuleDecl {
  public readonly ModuleDefinition ModuleDef;

  [FilledInDuringResolution] public ModuleSignature DefaultExport;  // the default export set of the module.

  private ModuleSignature emptySignature;
  public override ModuleSignature AccessibleSignature(bool ignoreExports) {
    if (ignoreExports) {
      return Signature;
    }
    return this.AccessibleSignature();
  }
  public override ModuleSignature AccessibleSignature() {
    if (DefaultExport == null) {
      if (emptySignature == null) {
        emptySignature = new ModuleSignature();
      }
      return emptySignature;
    }
    return DefaultExport;
  }

  public override IEnumerable<Node> Children => new[] { ModuleDef };

  public LiteralModuleDecl(ModuleDefinition module, ModuleDefinition parent)
    : base(module.RangeToken, module.MyName, parent, false, false) {
    ModuleDef = module;
    TokenWithTrailingDocString = module.TokenWithTrailingDocString;
  }

  public override object Dereference() { return ModuleDef; }
}

// Represents "module name = path;", where name is an identifier and path is a possibly qualified name.
public class AliasModuleDecl : ModuleDecl, IHasUsages {
  public readonly ModuleQualifiedId TargetQId; // generated by the parser, this is looked up
  public readonly List<IToken> Exports; // list of exports sets
  [FilledInDuringResolution] public bool ShadowsLiteralModule;  // initialized early during Resolution (and used not long after that); true for "import opened A = A" where "A" is a literal module in the same scope

  public AliasModuleDecl(RangeToken rangeToken, ModuleQualifiedId path, Name name, ModuleDefinition parent, bool opened, List<IToken> exports)
    : base(rangeToken, name, parent, opened, false) {
    Contract.Requires(path != null && path.Path.Count > 0);
    Contract.Requires(exports != null);
    Contract.Requires(exports.Count == 0 || path.Path.Count == 1);
    TargetQId = path;
    Exports = exports;
  }

  public override ModuleDefinition Dereference() { return Signature.ModuleDef; }
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { Dereference() };
  }
}

// Represents "module name as path [ = compilePath];", where name is a identifier and path is a possibly qualified name.
// Used to be called ModuleFacadeDecl -- renamed to be like LiteralModuleDecl, AliasModuleDecl
public class AbstractModuleDecl : ModuleDecl {
  public readonly ModuleQualifiedId QId;
  public readonly List<IToken> Exports; // list of exports sets
  public ModuleDecl CompileRoot;
  public ModuleSignature OriginalSignature;

  public AbstractModuleDecl(RangeToken rangeToken, ModuleQualifiedId qid, Name name, ModuleDefinition parent, bool opened, List<IToken> exports)
    : base(rangeToken, name, parent, opened, false) {
    Contract.Requires(qid != null && qid.Path.Count > 0);
    Contract.Requires(exports != null);

    QId = qid;
    Exports = exports;
  }
  public override object Dereference() { return this; }
}

// Represents the exports of a module.
public class ModuleExportDecl : ModuleDecl {
  public readonly bool IsDefault;
  public List<ExportSignature> Exports; // list of TopLevelDecl that are included in the export
  public List<IToken> Extends; // list of exports that are extended
  [FilledInDuringResolution] public readonly List<ModuleExportDecl> ExtendDecls = new List<ModuleExportDecl>();
  [FilledInDuringResolution] public readonly HashSet<Tuple<Declaration, bool>> ExportDecls = new HashSet<Tuple<Declaration, bool>>();
  public bool RevealAll; // only kept for initial rewriting, then discarded
  public bool ProvideAll;

  public readonly VisibilityScope ThisScope;
  public ModuleExportDecl(RangeToken rangeToken, ModuleDefinition parent,
    List<ExportSignature> exports, List<IToken> extends, bool provideAll, bool revealAll, bool isDefault, bool isRefining)
    : base(rangeToken, (isDefault || rangeToken.StartToken.val == "export") ? new Name(parent.Name) : new Name(rangeToken.StartToken), parent, false, isRefining) {
    Contract.Requires(exports != null);
    IsDefault = isDefault;
    Exports = exports;
    Extends = extends;
    ProvideAll = provideAll;
    RevealAll = revealAll;
    ThisScope = new VisibilityScope(this.FullSanitizedName);
  }

  public ModuleExportDecl(RangeToken rangeToken, Name name, ModuleDefinition parent,
    List<ExportSignature> exports, List<IToken> extends, bool provideAll, bool revealAll, bool isDefault, bool isRefining)
    : base(rangeToken, name, parent, false, isRefining) {
    Contract.Requires(exports != null);
    IsDefault = isDefault;
    Exports = exports;
    Extends = extends;
    ProvideAll = provideAll;
    RevealAll = revealAll;
    ThisScope = new VisibilityScope(this.FullSanitizedName);
  }

  public void SetupDefaultSignature() {
    Contract.Requires(this.Signature == null);
    var sig = new ModuleSignature();
    sig.ModuleDef = this.EnclosingModuleDefinition;
    sig.IsAbstract = this.EnclosingModuleDefinition.IsAbstract;
    sig.VisibilityScope = new VisibilityScope();
    sig.VisibilityScope.Augment(ThisScope);
    this.Signature = sig;
  }

  public override object Dereference() { return this; }
  public override bool CanBeExported() {
    return false;
  }

}

public class ExportSignature : TokenNode, IHasUsages {
  public readonly IToken ClassIdTok;
  public readonly bool Opaque;
  public readonly string ClassId;
  public readonly string Id;

  [FilledInDuringResolution] public Declaration Decl;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
    Contract.Invariant(Id != null);
    Contract.Invariant((ClassId != null) == (ClassIdTok != null));
  }

  public ExportSignature(IToken prefixTok, string prefix, IToken idTok, string id, bool opaque) {
    Contract.Requires(prefixTok != null);
    Contract.Requires(prefix != null);
    Contract.Requires(idTok != null);
    Contract.Requires(id != null);
    tok = idTok;
    ClassIdTok = prefixTok;
    ClassId = prefix;
    Id = id;
    Opaque = opaque;
    OwnedTokensCache = new List<IToken>() { Tok, prefixTok };
  }

  public ExportSignature(IToken idTok, string id, bool opaque) {
    Contract.Requires(idTok != null);
    Contract.Requires(id != null);
    tok = idTok;
    Id = id;
    Opaque = opaque;
    OwnedTokensCache = new List<IToken>() { Tok };
  }

  public override string ToString() {
    if (ClassId != null) {
      return ClassId + "." + Id;
    }
    return Id;
  }

  public IToken NameToken => Tok;
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { Decl };
  }
}

public class ModuleSignature {
  public VisibilityScope VisibilityScope = null;
  public readonly Dictionary<string, ModuleDecl> ShadowedImportedModules = new();
  public readonly Dictionary<string, TopLevelDecl> TopLevels = new Dictionary<string, TopLevelDecl>();
  public readonly Dictionary<string, ModuleExportDecl> ExportSets = new Dictionary<string, ModuleExportDecl>();
  public readonly Dictionary<string, Tuple<DatatypeCtor, bool>> Ctors = new Dictionary<string, Tuple<DatatypeCtor, bool>>();
  public readonly Dictionary<string, MemberDecl> StaticMembers = new Dictionary<string, MemberDecl>();
  public ModuleDefinition ModuleDef = null; // Note: this is null if this signature does not correspond to a specific definition (i.e.
                                            // it is abstract). Otherwise, it points to that definition.
  public ModuleSignature CompileSignature = null; // This is the version of the signature that should be used at compile time.
  public ModuleSignature Refines = null;
  public bool IsAbstract = false;
  public ModuleSignature() { }
  public int? ResolvedHash { get; set; }

  // Qualified accesses follow module imports
  public bool FindImport(string name, out ModuleDecl decl) {
    TopLevelDecl top;
    if (TopLevels.TryGetValue(name, out top) && top is ModuleDecl) {
      decl = (ModuleDecl)top;
      return true;
    } else {
      decl = null;
      return false;
    }
  }
}

public class ModuleQualifiedId {
  public readonly List<Name> Path; // Path != null && Path.Count > 0

  public ModuleQualifiedId(List<Name> path) {
    Contract.Assert(path != null && path.Count > 0);
    this.Path = path; // note that the list is aliased -- not to be modified after construction
  }

  // Creates a clone, including a copy of the list;
  // if the argument is true, resolution information is included
  public ModuleQualifiedId Clone(bool includeResInfo) {
    var newlist = new List<Name>(Path);
    ModuleQualifiedId cl = new ModuleQualifiedId(newlist);
    if (includeResInfo) {
      cl.Root = this.Root;
      cl.Decl = this.Decl;
      cl.Def = this.Def;
      cl.Sig = this.Sig;
      Contract.Assert(this.Def == this.Sig.ModuleDef);
    }
    return cl;
  }

  public string rootName() {
    return Path[0].Value;
  }

  public IToken rootToken() {
    return Path[0].StartToken;
  }

  public override string ToString() {
    string s = Path[0].Value;
    for (int i = 1; i < Path.Count; ++i) {
      s = s + "." + Path[i].Value;
    }

    return s;
  }

  public void SetRoot(ModuleDecl m) {
    this.Root = m;
  }

  public void Set(ModuleDecl m) {
    if (m == null) {
      this.Decl = null;
      this.Def = null;
      this.Sig = null;
    } else {
      this.Decl = m;
      this.Def = m.Signature.ModuleDef;
      this.Sig = m.Signature;
    }
  }

  // The following are filled in during resolution
  // Note that the root (first path segment) is resolved initially,
  // as it is needed to determine dependency relationships.
  // Then later the rest of the path is resolved, at which point all of the
  // ids in the path have been fully resolved
  // Note also that the resolution of the root depends on the syntactice location
  // of the qualified id; the resolution of subsequent ids depends on the
  // default export set of the previous id.
  [FilledInDuringResolution] public ModuleDecl Root; // the module corresponding to Path[0].val
  [FilledInDuringResolution] public ModuleDecl Decl; // the module corresponding to the full path
  [FilledInDuringResolution] public ModuleDefinition Def; // the module definition corresponding to the full path
  [FilledInDuringResolution] public ModuleSignature Sig; // the module signature corresponding to the full path
}

public class ModuleDefinition : INamedRegion, IDeclarationOrUsage, IAttributeBearingDeclaration {
  public IToken TokenWithTrailingDocString = Token.NoToken;
  public string DafnyName => MyName.StartToken.val; // The (not-qualified) name as seen in Dafny source code
  public readonly Name MyName; // (Last segment of the) module name
  public string Name => MyName.Value;
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

  public List<Include> Includes;

  [FilledInDuringResolution] public readonly List<TopLevelDecl> TopLevelDecls = new List<TopLevelDecl>();  // filled in by the parser; readonly after that, except for the addition of prefix-named modules, which happens in the resolver
  [FilledInDuringResolution] public readonly List<Tuple<List<IToken>, LiteralModuleDecl>> PrefixNamedModules = new List<Tuple<List<IToken>, LiteralModuleDecl>>();  // filled in by the parser; emptied by the resolver
  [FilledInDuringResolution] public readonly Graph<ICallable> CallGraph = new Graph<ICallable>();
  [FilledInDuringResolution] public int Height;  // height in the topological sorting of modules;
  public readonly bool IsAbstract;
  public readonly bool IsFacade; // True iff this module represents a module facade (that is, an abstract interface)
  private readonly bool IsBuiltinName; // true if this is something like _System that shouldn't have it's name mangled.
  public readonly bool IsToBeVerified;
  public readonly bool IsToBeCompiled;

  public int? ResolvedHash { get; set; }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(TopLevelDecls));
    Contract.Invariant(CallGraph != null);
  }

  public ModuleDefinition(RangeToken tok, Name name, List<IToken> prefixIds, bool isAbstract, bool isFacade,
    ModuleQualifiedId refinementQId, ModuleDefinition parent, Attributes attributes, bool isBuiltinName,
    bool isToBeVerified, bool isToBeCompiled) : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    this.MyName = name;
    this.PrefixIds = prefixIds;
    this.Attributes = attributes;
    this.EnclosingModule = parent;
    this.RefinementQId = refinementQId;
    this.IsAbstract = isAbstract;
    this.IsFacade = isFacade;
    this.Includes = new List<Include>();
    this.IsBuiltinName = isBuiltinName;
    this.IsToBeVerified = isToBeVerified;
    this.IsToBeCompiled = isToBeCompiled;
  }

  VisibilityScope visibilityScope;
  public VisibilityScope VisibilityScope =>
    visibilityScope ??= new VisibilityScope(this.SanitizedName);

  public virtual bool IsDefaultModule {
    get {
      return false;
    }
  }

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
  public string CompileName {
    get {
      if (compileName == null) {
        var externArgs = DafnyOptions.O.DisallowExterns ? null : Attributes.FindExpressions(this.Attributes, "extern");
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

  public static IEnumerable<Field> AllFields(List<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      var cl = d as TopLevelDeclWithMembers;
      if (cl != null) {
        foreach (var member in cl.Members) {
          var fn = member as Field;
          if (fn != null) {
            yield return fn;
          }
        }
      }
    }
  }

  public static IEnumerable<ClassDecl> AllClasses(List<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      if (d is ClassDecl cl) {
        yield return cl;
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
  public static IEnumerable<ICallable> AllCallables(List<TopLevelDecl> declarations) {
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
  public static IEnumerable<ICallable> AllCallablesIncludingPrefixDeclarations(List<TopLevelDecl> declarations) {
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
  public static IEnumerable<ICallable> AllItersAndCallables(List<TopLevelDecl> declarations) {
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

  public static IEnumerable<IteratorDecl> AllIteratorDecls(List<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      if (d is IteratorDecl iter) {
        yield return iter;
      }
    }
  }

  /// <summary>
  /// Emits the declarations in "declarations", but for each such declaration that is a class with
  /// a corresponding non-null type, also emits that non-null type *after* the class declaration.
  /// </summary>
  public static IEnumerable<TopLevelDecl> AllDeclarationsAndNonNullTypeDecls(List<TopLevelDecl> declarations) {
    foreach (var d in declarations) {
      yield return d;
      if (d is ClassDecl { NonNullTypeDecl: { } } cl) {
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

  public IToken GetFirstTopLevelToken() {
    return TopLevelDecls.OfType<ClassDecl>()
      .SelectMany(classDecl => classDecl.Members)
      .Where(member => member.tok.line > 0)
      .Select(member => member.tok)
      .Concat(TopLevelDecls.OfType<LiteralModuleDecl>()
        .Select(moduleDecl => moduleDecl.ModuleDef.GetFirstTopLevelToken())
        .Where(tok => tok.line > 0)
      ).FirstOrDefault(Token.NoToken);
  }

  public IToken NameToken => tok;
  public override IEnumerable<Node> Children => (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>()).Concat(TopLevelDecls);
}

public class DefaultModuleDecl : ModuleDefinition {
  public DefaultModuleDecl()
    : base(RangeToken.NoToken, new Name("_module"), new List<IToken>(), false, false, null, null, null, true, true, true) {
  }
  public override bool IsDefaultModule {
    get {
      return true;
    }
  }
}

public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
  public abstract string WhatKind { get; }
  public readonly ModuleDefinition EnclosingModuleDefinition;
  public readonly List<TypeParameter> TypeArgs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(TypeArgs));
  }

  protected TopLevelDecl(RangeToken rangeToken, Name name, ModuleDefinition enclosingModule, List<TypeParameter> typeArgs, Attributes attributes, bool isRefining)
    : base(rangeToken, name, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    EnclosingModuleDefinition = enclosingModule;
    TypeArgs = typeArgs;
  }

  public string FullDafnyName {
    get {
      if (Name == "_module") {
        return "";
      }

      if (Name == "_default") {
        return EnclosingModuleDefinition.FullDafnyName;
      }

      string n = EnclosingModuleDefinition.FullDafnyName;
      return (n.Length == 0 ? n : (n + ".")) + Name;
    }
  }
  public virtual string FullName {
    get {
      if (EnclosingModuleDefinition is null) {
        return Name;
      }
      return EnclosingModuleDefinition.FullName + "." + Name;
    }
  }
  public string FullSanitizedName {
    get {
      if (EnclosingModuleDefinition is null) {
        return SanitizedName;
      }
      return EnclosingModuleDefinition.SanitizedName + "." + SanitizedName;
    }
  }

  public string FullNameInContext(ModuleDefinition context) {
    if (EnclosingModuleDefinition == context) {
      return Name;
    } else {
      return EnclosingModuleDefinition.Name + "." + Name;
    }
  }
  public string FullCompileName {
    get {
      var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
      if (!DafnyOptions.O.DisallowExterns && externArgs != null) {
        if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
          return externArgs[0].AsStringLiteral() + "." + externArgs[1].AsStringLiteral();
        }
      }

      return DafnyOptions.O.Backend.GetCompileName(EnclosingModuleDefinition.IsDefaultModule,
        EnclosingModuleDefinition.CompileName, CompileName);
    }
  }

  public TopLevelDecl ViewAsClass {
    get {
      if (this is NonNullTypeDecl) {
        return ((NonNullTypeDecl)this).Class;
      } else {
        return this;
      }
    }
  }

  /// <summary>
  /// Return the list of parent types of "this", where the type parameters
  /// of "this" have been instantiated by "typeArgs". For example, for a subset
  /// type, the return value is the RHS type, appropriately instantiated. As
  /// two other examples, given
  ///     class C<X> extends J<X, int>
  /// C.ParentTypes(real) = J<real, int>    // non-null types C and J
  /// C?.ParentTypes(real) = J?<real, int>  // possibly-null type C? and J?
  /// </summary>
  public virtual List<Type> ParentTypes(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(this.TypeArgs.Count == typeArgs.Count);
    return new List<Type>();
  }

  public bool AllowsAllocation => true;
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();

  /// <summary>
  /// A top-level declaration is considered "essentially empty" if there is no way it could generate any resolution error
  /// other than introducing a duplicate name.
  /// </summary>
  public virtual bool IsEssentiallyEmpty() {
    return Attributes == null || TypeArgs.Count != 0;
  }
}

public abstract class TopLevelDeclWithMembers : TopLevelDecl {
  public readonly List<MemberDecl> Members;

  // The following fields keep track of parent traits
  public readonly List<MemberDecl> InheritedMembers = new List<MemberDecl>();  // these are instance members declared in parent traits
  public readonly List<Type> ParentTraits;  // these are the types that are parsed after the keyword 'extends'; note, for a successfully resolved program, these are UserDefinedType's where .ResolvedClas is NonNullTypeDecl
  public readonly Dictionary<TypeParameter, Type> ParentFormalTypeParametersToActuals = new Dictionary<TypeParameter, Type>();  // maps parent traits' type parameters to actuals

  /// <summary>
  /// TraitParentHeads contains the head of each distinct trait parent. It is initialized during resolution.
  /// </summary>
  public readonly List<TraitDecl> ParentTraitHeads = new List<TraitDecl>();

  [FilledInDuringResolution] public InheritanceInformationClass ParentTypeInformation;
  public class InheritanceInformationClass {
    private readonly Dictionary<TraitDecl, List<(Type, List<TraitDecl> /*via this parent path*/)>> info = new Dictionary<TraitDecl, List<(Type, List<TraitDecl>)>>();

    /// <summary>
    /// Returns a subset of the trait's ParentTraits, but not repeating any head type.
    /// Assumes the declaration has been successfully resolved.
    /// </summary>
    public List<Type> UniqueParentTraits() {
      return info.ToList().ConvertAll(entry => entry.Value[0].Item1);
    }

    public void Record(TraitDecl traitHead, UserDefinedType parentType) {
      Contract.Requires(traitHead != null);
      Contract.Requires(parentType != null);
      Contract.Requires(parentType.ResolvedClass is NonNullTypeDecl nntd && nntd.ViewAsClass == traitHead);

      if (!info.TryGetValue(traitHead, out var list)) {
        list = new List<(Type, List<TraitDecl>)>();
        info.Add(traitHead, list);
      }
      list.Add((parentType, new List<TraitDecl>()));
    }

    public void Extend(TraitDecl parent, InheritanceInformationClass parentInfo, Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(parent != null);
      Contract.Requires(parentInfo != null);
      Contract.Requires(typeMap != null);

      foreach (var entry in parentInfo.info) {
        var traitHead = entry.Key;
        if (!info.TryGetValue(traitHead, out var list)) {
          list = new List<(Type, List<TraitDecl>)>();
          info.Add(traitHead, list);
        }
        foreach (var pair in entry.Value) {
          var ty = pair.Item1.Subst(typeMap);
          // prepend the path with "parent"
          var parentPath = new List<TraitDecl>() { parent };
          parentPath.AddRange(pair.Item2);
          list.Add((ty, parentPath));
        }
      }
    }

    public IEnumerable<List<(Type, List<TraitDecl>)>> GetTypeInstantiationGroups() {
      foreach (var pair in info.Values) {
        yield return pair;
      }
    }
  }

  protected TopLevelDeclWithMembers(RangeToken rangeToken, Name name, ModuleDefinition module, List<TypeParameter> typeArgs, List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits = null)
    : base(rangeToken, name, module, typeArgs, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
    Members = members;
    ParentTraits = traits ?? new List<Type>();
  }

  public static List<UserDefinedType> CommonTraits(TopLevelDeclWithMembers a, TopLevelDeclWithMembers b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    var aa = a.TraitAncestors();
    var bb = b.TraitAncestors();
    aa.IntersectWith(bb);
    var types = new List<UserDefinedType>();
    foreach (var t in aa) {
      var typeArgs = t.TypeArgs.ConvertAll(tp => a.ParentFormalTypeParametersToActuals[tp]);
      var u = new UserDefinedType(t.RangeToken, t.Name + "?", t, typeArgs);
      types.Add(u);
    }
    return types;
  }

  public override IEnumerable<Node> Children {
    get {
      return Members.Concat(ParentTraits.SelectMany(parentTrait => parentTrait.Nodes));
    }
  }

  /// <summary>
  /// Returns the set of transitive parent traits (not including "this" itself).
  /// This method assumes the .ParentTraits fields have been checked for various cycle restrictions.
  /// </summary>
  public ISet<TraitDecl> TraitAncestors() {
    var s = new HashSet<TraitDecl>();
    AddTraitAncestors(s);
    return s;
  }
  /// <summary>
  /// Adds to "s" the transitive parent traits (not including "this" itself).
  /// This method assumes the .ParentTraits fields have been checked for various cycle restrictions.
  /// </summary>
  private void AddTraitAncestors(ISet<TraitDecl> s) {
    Contract.Requires(s != null);
    foreach (var parent in ParentTraits) {
      var udt = (UserDefinedType)parent;  // in a successfully resolved program, we expect all .ParentTraits to be a UserDefinedType
      var nntd = (NonNullTypeDecl)udt.ResolvedClass;  // we expect the trait type to be the non-null version of the trait type
      var tr = (TraitDecl)nntd.Class;
      s.Add(tr);
      tr.AddTraitAncestors(s);
    }
  }

  // True if non-static members can access the underlying object "this"
  // False if all members are implicitly static (e.g. in a default class declaration)
  public abstract bool AcceptThis { get; }

  public override bool IsEssentiallyEmpty() {
    if (Members.Count != 0 || ParentTraits.Count != 0) {
      return false;
    }
    return base.IsEssentiallyEmpty();
  }
}

public class TraitDecl : ClassDecl {
  public override string WhatKind { get { return "trait"; } }
  public bool IsParent { set; get; }
  public TraitDecl(RangeToken rangeToken, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining, traits) { }

  public override IEnumerable<AssumptionDescription> Assumptions() {
    foreach (var assumption in base.Assumptions()) {
      yield return assumption;
    }

    if (Attributes.Find(Attributes, "termination") is Attributes ta &&
        ta.Args.Count == 1 && Expression.IsBoolLiteral(ta.Args[0], out var termCheck) &&
        termCheck == false) {
      yield return AssumptionDescription.HasTerminationFalseAttribute;
    }
  }
}

public class ClassDecl : TopLevelDeclWithMembers, RevealableTypeDecl {
  public override string WhatKind { get { return "class"; } }
  public override bool CanBeRevealed() { return true; }
  [FilledInDuringResolution] public bool HasConstructor;  // filled in (early) during resolution; true iff there exists a member that is a Constructor
  public readonly NonNullTypeDecl NonNullTypeDecl;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Members));
    Contract.Invariant(ParentTraits != null);
  }

  public ClassDecl(RangeToken rangeToken, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining, traits) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
    Contract.Assume(!(this is ArrowTypeDecl));  // this is also a precondition, really, but "this" cannot be mentioned in Requires of a constructor; ArrowTypeDecl should use the next constructor
    if (!IsDefaultClass) {
      NonNullTypeDecl = new NonNullTypeDecl(this);
    }
    this.NewSelfSynonym();
  }
  /// <summary>
  /// The following constructor is supposed to be called by the ArrowTypeDecl subtype, in order to avoid
  /// the call to this.NewSelfSynonym() (because NewSelfSynonym() depends on the .Arity field having been
  /// set, which it hasn't during the base call of the ArrowTypeDecl constructor). Instead, the ArrowTypeDecl
  /// constructor will do that call.
  /// </summary>
  protected ClassDecl(RangeToken rangeToken, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining, null) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
    Contract.Assume(this is ArrowTypeDecl);  // this is also a precondition, really, but "this" cannot be mentioned in Requires of a constructor
  }
  public virtual bool IsDefaultClass {
    get {
      return false;
    }
  }

  public bool IsObjectTrait {
    get => Name == "object";
  }

  internal bool HeadDerivesFrom(TopLevelDecl b) {
    Contract.Requires(b != null);
    return this == b || this.ParentTraitHeads.Exists(tr => tr.HeadDerivesFrom(b));
  }

  public List<Type> NonNullTraitsWithArgument(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);

    // Instantiate with the actual type arguments
    if (typeArgs.Count == 0) {
      // this optimization seems worthwhile
      return ParentTraits;
    } else {
      var subst = TypeParameter.SubstitutionMap(TypeArgs, typeArgs);
      return ParentTraits.ConvertAll(traitType => traitType.Subst(subst));
    }
  }

  public List<Type> PossiblyNullTraitsWithArgument(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    // Instantiate with the actual type arguments
    var subst = TypeParameter.SubstitutionMap(TypeArgs, typeArgs);
    return ParentTraits.ConvertAll(traitType => (Type)UserDefinedType.CreateNullableType((UserDefinedType)traitType.Subst(subst)));
  }

  public override List<Type> ParentTypes(List<Type> typeArgs) {
    return PossiblyNullTraitsWithArgument(typeArgs);
  }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }
  public override bool AcceptThis => this is not DefaultClassDecl;
}

public class DefaultClassDecl : ClassDecl {
  public DefaultClassDecl(ModuleDefinition module, [Captured] List<MemberDecl> members)
    : base(RangeToken.NoToken, new Name("_default"), module, new List<TypeParameter>(), members, null, false, null) {
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(members));
  }
  public override bool IsDefaultClass {
    get {
      return true;
    }
  }
}

public class ArrayClassDecl : ClassDecl {
  public override string WhatKind { get { return "array type"; } }
  public readonly int Dims;
  public ArrayClassDecl(int dims, ModuleDefinition module, Attributes attrs)
    : base(RangeToken.NoToken, new Name(BuiltIns.ArrayClassName(dims)), module,
      new List<TypeParameter>(new TypeParameter[] { new TypeParameter(RangeToken.NoToken,  new Name("arg"), TypeParameter.TPVarianceSyntax.NonVariant_Strict) }),
      new List<MemberDecl>(), attrs, false, null) {
    Contract.Requires(1 <= dims);
    Contract.Requires(module != null);

    Dims = dims;
    // Resolve type parameter
    Contract.Assert(TypeArgs.Count == 1);
    var tp = TypeArgs[0];
    tp.Parent = this;
    tp.PositionalIndex = 0;
  }
}

public class ArrowTypeDecl : ClassDecl {
  public override string WhatKind { get { return "function type"; } }
  public readonly int Arity;
  public readonly Function Requires;
  public readonly Function Reads;

  public ArrowTypeDecl(List<TypeParameter> tps, Function req, Function reads, ModuleDefinition module, Attributes attributes)
    : base(RangeToken.NoToken, ArrowType.ArrowTypeName(tps.Count - 1), module, tps,
      new List<MemberDecl> { req, reads }, attributes, false) {
    Contract.Requires(tps != null && 1 <= tps.Count);
    Contract.Requires(req != null);
    Contract.Requires(reads != null);
    Contract.Requires(module != null);
    Arity = tps.Count - 1;
    Requires = req;
    Reads = reads;
    Requires.EnclosingClass = this;
    Reads.EnclosingClass = this;
    this.NewSelfSynonym();
  }
}

public abstract class DatatypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICallable {
  public override bool CanBeRevealed() { return true; }
  public readonly List<DatatypeCtor> Ctors;

  [FilledInDuringResolution] public Dictionary<string, DatatypeCtor> ConstructorsByName { get; set; }
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Ctors));
    Contract.Invariant(1 <= Ctors.Count);
  }

  public override IEnumerable<Node> Children => Ctors.Concat<Node>(base.Children);

  public DatatypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ctors));
    Contract.Requires(cce.NonNullElements(members));
    Contract.Requires((isRefining && ctors.Count == 0) || (!isRefining && 1 <= ctors.Count));
    Ctors = ctors;
    this.NewSelfSynonym();
  }
  public bool HasFinitePossibleValues {
    get {
      // Note, to determine finiteness, it doesn't matter if the constructors are ghost or non-ghost.
      return (TypeArgs.Count == 0 && Ctors.TrueForAll(ctr => ctr.Formals.Count == 0));
    }
  }

  public bool IsRecordType {
    get { return this is IndDatatypeDecl && Ctors.Count == 1 && !Ctors[0].IsGhost; }
  }

  public bool HasGhostVariant => Ctors.Any(ctor => ctor.IsGhost);

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  bool ICodeContext.IsGhost { get { return true; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
  string ICallable.NameRelativeToModule { get { return Name; } }
  Specification<Expression> ICallable.Decreases {
    get {
      // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
      // the question of what its Decreases clause is should never arise.
      throw new cce.UnreachableException();
    }
  }
  bool ICallable.InferredDecreases {
    get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
  }

  /// <summary>
  /// For information about the grounding constructor, see docs/Compilation/AutoInitialization.md.
  /// </summary>
  public abstract DatatypeCtor GetGroundingCtor();


  public override bool IsEssentiallyEmpty() {
    if (Ctors.Any(ctor => ctor.Attributes != null || ctor.Formals.Count != 0)) {
      return false;
    }
    return base.IsEssentiallyEmpty();
  }
}

public class IndDatatypeDecl : DatatypeDecl {
  public override string WhatKind { get { return "datatype"; } }
  public DatatypeCtor GroundingCtor;  // set during resolution

  public override DatatypeCtor GetGroundingCtor() {
    return GroundingCtor;
  }

  public bool[] TypeParametersUsedInConstructionByGroundingCtor;  // set during resolution; has same length as the number of type arguments

  public enum ES { NotYetComputed, Never, ConsultTypeArguments }
  public ES EqualitySupport = ES.NotYetComputed;

  public IndDatatypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, typeArgs, ctors, members, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ctors));
    Contract.Requires(cce.NonNullElements(members));
    Contract.Requires((isRefining && ctors.Count == 0) || (!isRefining && 1 <= ctors.Count));
  }

  public override bool AcceptThis => true;
}

public class CoDatatypeDecl : DatatypeDecl {
  public override string WhatKind { get { return "codatatype"; } }
  [FilledInDuringResolution] public CoDatatypeDecl SscRepr;

  public CoDatatypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, typeArgs, ctors, members, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ctors));
    Contract.Requires(cce.NonNullElements(members));
    Contract.Requires((isRefining && ctors.Count == 0) || (!isRefining && 1 <= ctors.Count));
  }

  public override DatatypeCtor GetGroundingCtor() {
    return Ctors.FirstOrDefault(ctor => ctor.IsGhost, Ctors[0]);
  }

  public override bool AcceptThis => true;
}

/// <summary>
/// The "ValuetypeDecl" class models the built-in value types (like bool, int, set, and seq.
/// Its primary function is to hold the formal type parameters and built-in members of these types.
/// </summary>
public class ValuetypeDecl : TopLevelDecl {
  public override string WhatKind { get { return Name; } }
  public readonly Dictionary<string, MemberDecl> Members = new Dictionary<string, MemberDecl>();
  readonly Func<Type, bool> typeTester;
  readonly Func<List<Type>, Type>/*?*/ typeCreator;

  public ValuetypeDecl(string name, ModuleDefinition module, int typeParameterCount, Func<Type, bool> typeTester, Func<List<Type>, Type>/*?*/ typeCreator)
    : base(RangeToken.NoToken, name, module, new List<TypeParameter>(), null, false) {
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(0 <= typeParameterCount);
    Contract.Requires(typeTester != null);
    // fill in the type parameters
    for (int i = 0; i < typeParameterCount; i++) {
      TypeArgs.Add(new TypeParameter(RangeToken.NoToken, ((char)('T' + i)).ToString(), i, this));
    }
    this.typeTester = typeTester;
    this.typeCreator = typeCreator;
  }

  public bool IsThisType(Type t) {
    Contract.Assert(t != null);
    return typeTester(t);
  }

  public Type CreateType(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    Contract.Assume(typeCreator != null);  // can only call CreateType for a ValuetypeDecl with a type creator (this is up to the caller to ensure)
    return typeCreator(typeArgs);
  }
}

public class DatatypeCtor : Declaration, TypeParameter.ParentType {
  public readonly bool IsGhost;
  public readonly List<Formal> Formals;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Formals));
    Contract.Invariant(Destructors != null);
    Contract.Invariant(
      Destructors.Count == 0 || // this is until resolution
      Destructors.Count == Formals.Count);  // after resolution
  }

  public override IEnumerable<Node> Children => base.Children.Concat(Formals);

  // TODO: One could imagine having a precondition on datatype constructors
  [FilledInDuringResolution] public DatatypeDecl EnclosingDatatype;
  [FilledInDuringResolution] public SpecialField QueryField;
  [FilledInDuringResolution] public List<DatatypeDestructor> Destructors = new List<DatatypeDestructor>();  // includes both implicit (not mentionable in source) and explicit destructors

  public DatatypeCtor(RangeToken rangeToken, Name name, bool isGhost, [Captured] List<Formal> formals, Attributes attributes)
    : base(rangeToken, name, attributes, false) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(formals));
    this.Formals = formals;
    this.IsGhost = isGhost;
  }

  public string FullName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(EnclosingDatatype != null);

      return "#" + EnclosingDatatype.FullName + "." + Name;
    }
  }
}

/// <summary>
/// An ICodeContext is an ICallable or a NoContext.
/// </summary>
public interface ICodeContext : IASTVisitorContext {
  bool IsGhost { get; }
  List<TypeParameter> TypeArgs { get; }
  List<Formal> Ins { get; }
  bool MustReverify { get; }
  string FullSanitizedName { get; }
  bool AllowsNontermination { get; }
}

/// <summary>
/// Some declarations have more than one context. For example, a subset type has a constraint
/// (which is a ghost context) and a witness (which may be a compiled context). To distinguish
/// between these two, the declaration is wrapped inside a CodeContextWrapper.
/// </summary>
public class CodeContextWrapper : ICodeContext {
  protected readonly ICodeContext inner;
  private readonly bool isGhostContext;
  public CodeContextWrapper(ICodeContext inner, bool isGhostContext) {
    this.inner = inner;
    this.isGhostContext = isGhostContext;
  }

  public bool IsGhost => isGhostContext;
  public List<TypeParameter> TypeArgs => inner.TypeArgs;
  public List<Formal> Ins => inner.Ins;
  public ModuleDefinition EnclosingModule => inner.EnclosingModule;
  public bool MustReverify => inner.MustReverify;
  public string FullSanitizedName => inner.FullSanitizedName;
  public bool AllowsNontermination => inner.AllowsNontermination;

  public static ICodeContext Unwrap(ICodeContext codeContext) {
    while (codeContext is CodeContextWrapper ccw) {
      codeContext = ccw.inner;
    }
    return codeContext;
  }
}

/// <summary>
/// An ICallable is a Function, Method, IteratorDecl, or (less fitting for the name ICallable) RedirectingTypeDecl or DatatypeDecl.
/// </summary>
public interface ICallable : ICodeContext, INode {
  IToken Tok => RangeToken.StartToken;
  
  string WhatKind { get; }
  string NameRelativeToModule { get; }
  Specification<Expression> Decreases { get; }
  /// <summary>
  /// The InferredDecreases property says whether or not a process was attempted to provide a default decreases
  /// clause.  If such a process was attempted, even if the resulting decreases clause turned out to be empty,
  /// the property will get the value "true".  This is so that a useful error message can be provided.
  /// </summary>
  bool InferredDecreases { get; set; }
  bool AllowsAllocation { get; }
}

/// <summary>
/// This class allows an ICallable to be treated as ghost/compiled according to the "isGhostContext"
/// parameter.
///
/// This class is to ICallable what CodeContextWrapper is to ICodeContext.
/// </summary>
public class CallableWrapper : CodeContextWrapper, ICallable {
  public CallableWrapper(ICallable callable, bool isGhostContext)
    : base(callable, isGhostContext) {
  }

  protected ICallable cwInner => (ICallable)inner;
  public IToken Tok => cwInner.Tok;
  public string WhatKind => cwInner.WhatKind;
  public string NameRelativeToModule => cwInner.NameRelativeToModule;
  public Specification<Expression> Decreases => cwInner.Decreases;

  public bool InferredDecreases {
    get => cwInner.InferredDecreases;
    set { cwInner.InferredDecreases = value; }
  }

  public bool AllowsAllocation => cwInner.AllowsAllocation;
  public RangeToken RangeToken => cwInner.RangeToken;
}

public class DontUseICallable : ICallable {
  public string WhatKind { get { throw new cce.UnreachableException(); } }
  public bool IsGhost { get { throw new cce.UnreachableException(); } }
  public List<TypeParameter> TypeArgs { get { throw new cce.UnreachableException(); } }
  public List<Formal> Ins { get { throw new cce.UnreachableException(); } }
  public ModuleDefinition EnclosingModule { get { throw new cce.UnreachableException(); } }
  public bool MustReverify { get { throw new cce.UnreachableException(); } }
  public string FullSanitizedName { get { throw new cce.UnreachableException(); } }
  public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
  public IToken Tok { get { throw new cce.UnreachableException(); } }
  public string NameRelativeToModule { get { throw new cce.UnreachableException(); } }
  public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
  public bool InferredDecreases {
    get { throw new cce.UnreachableException(); }
    set { throw new cce.UnreachableException(); }
  }
  public bool AllowsAllocation => throw new cce.UnreachableException();
  public RangeToken RangeToken => throw new cce.UnreachableException();
}

/// <summary>
/// An IMethodCodeContext is a Method or IteratorDecl.
/// </summary>
public interface IMethodCodeContext : ICallable {
  List<Formal> Outs { get; }
  Specification<FrameExpression> Modifies { get; }
}

/// <summary>
/// Applies when we are not inside an ICallable.  In particular, a NoContext is used to resolve the attributes of declarations with no other context.
/// </summary>
public class NoContext : ICodeContext {
  public readonly ModuleDefinition Module;
  public NoContext(ModuleDefinition module) {
    this.Module = module;
  }
  bool ICodeContext.IsGhost { get { return true; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return Module; } }
  bool ICodeContext.MustReverify { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public string FullSanitizedName { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public bool AllowsNontermination { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  public bool AllowsAllocation => true;
}

public class IteratorDecl : ClassDecl, IMethodCodeContext {
  public override string WhatKind { get { return "iterator"; } }
  public readonly List<Formal> Ins;
  public readonly List<Formal> Outs;
  public readonly Specification<FrameExpression> Reads;
  public readonly Specification<FrameExpression> Modifies;
  public readonly Specification<Expression> Decreases;
  public readonly List<AttributedExpression> Requires;
  public readonly List<AttributedExpression> Ensures;
  public readonly List<AttributedExpression> YieldRequires;
  public readonly List<AttributedExpression> YieldEnsures;
  public readonly BlockStmt Body;
  public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }
  public readonly IToken SignatureEllipsis;
  public readonly List<Field> OutsFields;
  public readonly List<Field> OutsHistoryFields;  // these are the 'xs' variables
  [FilledInDuringResolution] public readonly List<Field> DecreasesFields;
  [FilledInDuringResolution] public SpecialField Member_Modifies;
  [FilledInDuringResolution] public SpecialField Member_Reads;
  [FilledInDuringResolution] public SpecialField Member_New;
  [FilledInDuringResolution] public Constructor Member_Init;  // created during registration phase of resolution;
  [FilledInDuringResolution] public Predicate Member_Valid;  // created during registration phase of resolution;
  [FilledInDuringResolution] public Method Member_MoveNext;  // created during registration phase of resolution;
  public readonly LocalVariable YieldCountVariable;

  public IteratorDecl(RangeToken rangeToken, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
    List<Formal> ins, List<Formal> outs,
    Specification<FrameExpression> reads, Specification<FrameExpression> mod, Specification<Expression> decreases,
    List<AttributedExpression> requires,
    List<AttributedExpression> ensures,
    List<AttributedExpression> yieldRequires,
    List<AttributedExpression> yieldEnsures,
    BlockStmt body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, module, typeArgs, new List<MemberDecl>(), attributes, signatureEllipsis != null, null) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(ins != null);
    Contract.Requires(outs != null);
    Contract.Requires(reads != null);
    Contract.Requires(mod != null);
    Contract.Requires(decreases != null);
    Contract.Requires(requires != null);
    Contract.Requires(ensures != null);
    Contract.Requires(yieldRequires != null);
    Contract.Requires(yieldEnsures != null);
    Ins = ins;
    Outs = outs;
    Reads = reads;
    Modifies = mod;
    Decreases = decreases;
    Requires = requires;
    Ensures = ensures;
    YieldRequires = yieldRequires;
    YieldEnsures = yieldEnsures;
    Body = body;
    SignatureEllipsis = signatureEllipsis;

    OutsFields = new List<Field>();
    OutsHistoryFields = new List<Field>();
    DecreasesFields = new List<Field>();

    YieldCountVariable = new LocalVariable(rangeToken, "_yieldCount", new EverIncreasingType(), true);
    YieldCountVariable.type = YieldCountVariable.OptionalType;  // resolve YieldCountVariable here
  }

  /// <summary>
  /// Returns the non-null expressions of this declaration proper (that is, do not include the expressions of substatements).
  /// Does not include the generated class members.
  /// </summary>
  public virtual IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
      foreach (var e in Attributes.SubExpressions(Reads.Attributes)) {
        yield return e;
      }
      foreach (var e in Reads.Expressions) {
        yield return e.E;
      }
      foreach (var e in Attributes.SubExpressions(Modifies.Attributes)) {
        yield return e;
      }
      foreach (var e in Modifies.Expressions) {
        yield return e.E;
      }
      foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) {
        yield return e;
      }
      foreach (var e in Decreases.Expressions) {
        yield return e;
      }
      foreach (var e in Requires) {
        yield return e.E;
      }
      foreach (var e in Ensures) {
        yield return e.E;
      }
      foreach (var e in YieldRequires) {
        yield return e.E;
      }
      foreach (var e in YieldEnsures) {
        yield return e.E;
      }
    }
  }

  /// <summary>
  /// This Dafny type exists only for the purpose of giving the yield-count variable a type, so
  /// that the type can be recognized during translation of Dafny into Boogie.  It represents
  /// an integer component in a "decreases" clause whose order is (\lambda x,y :: x GREATER y),
  /// not the usual (\lambda x,y :: x LESS y AND 0 ATMOST y).
  /// </summary>
  public class EverIncreasingType : BasicType {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);

      return "_increasingInt";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is EverIncreasingType;
    }
  }

  bool ICodeContext.IsGhost { get { return false; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return this.Ins; } }
  List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
  Specification<FrameExpression> IMethodCodeContext.Modifies { get { return this.Modifies; } }
  string ICallable.NameRelativeToModule { get { return this.Name; } }
  Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
  bool _inferredDecr;
  bool ICallable.InferredDecreases {
    set { _inferredDecr = value; }
    get { return _inferredDecr; }
  }

  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return this.EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  public bool AllowsNontermination {
    get {
      return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
    }
  }
}

public class OpaqueTypeDecl : TopLevelDeclWithMembers, TypeParameter.ParentType, RevealableTypeDecl {
  public override string WhatKind { get { return "opaque type"; } }
  public override bool CanBeRevealed() { return true; }
  public readonly TypeParameter.TypeParameterCharacteristics Characteristics;
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
  }

  public OpaqueTypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(typeArgs != null);
    Characteristics = characteristics;
    this.NewSelfSynonym();
  }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }
  public override bool AcceptThis => true;
}

public interface RedirectingTypeDecl : ICallable {
  string Name { get; }

  IToken tok { get; }
  IEnumerable<IToken> OwnedTokens { get; }
  IToken StartToken { get; }
  Attributes Attributes { get; }
  ModuleDefinition Module { get; }
  BoundVar/*?*/ Var { get; }
  Expression/*?*/ Constraint { get; }
  SubsetTypeDecl.WKind WitnessKind { get; }
  Expression/*?*/ Witness { get; }  // non-null iff WitnessKind is Compiled or Ghost
  FreshIdGenerator IdGenerator { get; }
}

public class NativeType {
  public readonly string Name;
  public readonly BigInteger LowerBound;
  public readonly BigInteger UpperBound;
  public readonly int Bitwidth;  // for unassigned types, this shows the number of bits in the type; else is 0
  public enum Selection { Byte, SByte, UShort, Short, UInt, Int, Number, ULong, Long }
  public readonly Selection Sel;
  public NativeType(string Name, BigInteger LowerBound, BigInteger UpperBound, int bitwidth, Selection sel) {
    Contract.Requires(Name != null);
    Contract.Requires(0 <= bitwidth && (bitwidth == 0 || LowerBound == 0));
    this.Name = Name;
    this.LowerBound = LowerBound;
    this.UpperBound = UpperBound;
    this.Bitwidth = bitwidth;
    this.Sel = sel;
  }
}

public class TypeDeclSynonymInfo {
  public readonly InternalTypeSynonymDecl SelfSynonymDecl;

  public TypeDeclSynonymInfo(TopLevelDecl d) {
    var thisType = UserDefinedType.FromTopLevelDecl(d.RangeToken, d);
    SelfSynonymDecl = new InternalTypeSynonymDecl(d.RangeToken, d.Name, TypeParameter.GetExplicitCharacteristics(d),
      d.TypeArgs, d.EnclosingModuleDefinition, thisType, d.Attributes);
    SelfSynonymDecl.InheritVisibility(d, false);
  }

  public UserDefinedType SelfSynonym(List<Type> args, Expression /*?*/ namePath = null) {
    return new UserDefinedType(SelfSynonymDecl.RangeToken, SelfSynonymDecl.Name, SelfSynonymDecl, args, namePath);
  }
}

public static class RevealableTypeDeclHelper {
  public static InternalTypeSynonymDecl SelfSynonymDecl(this RevealableTypeDecl rtd) =>
    rtd.SynonymInfo.SelfSynonymDecl;

  public static UserDefinedType SelfSynonym(this RevealableTypeDecl rtd, List<Type> args, Expression /*?*/ namePath = null) =>
    rtd.SynonymInfo.SelfSynonym(args, namePath);

  //Internal implementations are called before extensions, so this is safe
  public static bool IsRevealedInScope(this RevealableTypeDecl rtd, VisibilityScope scope) =>
    rtd.AsTopLevelDecl.IsRevealedInScope(scope);

  public static void NewSelfSynonym(this RevealableTypeDecl rtd) {
    rtd.SynonymInfo = new TypeDeclSynonymInfo(rtd.AsTopLevelDecl);
  }
}

public interface RevealableTypeDecl {
  TopLevelDecl AsTopLevelDecl { get; }
  TypeDeclSynonymInfo SynonymInfo { get; set; }
}

public class NewtypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl {
  public override string WhatKind { get { return "newtype"; } }
  public override bool CanBeRevealed() { return true; }
  public Type BaseType { get; set; } // null when refining
  public BoundVar Var { get; set; }  // can be null (if non-null, then object.ReferenceEquals(Var.Type, BaseType))
  public Expression Constraint { get; set; }  // is null iff Var is
  public SubsetTypeDecl.WKind WitnessKind { get; set; } = SubsetTypeDecl.WKind.CompiledZero;
  public Expression/*?*/ Witness { get; set; } // non-null iff WitnessKind is Compiled or Ghost
  [FilledInDuringResolution] public NativeType NativeType; // non-null for fixed-size representations (otherwise, use BigIntegers for integers)
  public NewtypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, Type baseType, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, new List<TypeParameter>(), members, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(isRefining ^ (baseType != null));
    Contract.Requires(members != null);
    BaseType = baseType;
  }
  public NewtypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, BoundVar bv, Expression constraint, SubsetTypeDecl.WKind witnessKind, Expression witness, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, new List<TypeParameter>(), members, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(bv != null && bv.Type != null);
    Contract.Requires((witnessKind == SubsetTypeDecl.WKind.Compiled || witnessKind == SubsetTypeDecl.WKind.Ghost) == (witness != null));
    Contract.Requires(members != null);
    BaseType = bv.Type;
    Var = bv;
    Constraint = constraint;
    Witness = witness;
    WitnessKind = witnessKind;
    this.NewSelfSynonym();
  }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public TypeParameter.EqualitySupportValue EqualitySupport {
    get {
      if (this.BaseType.SupportsEquality) {
        return TypeParameter.EqualitySupportValue.Required;
      } else {
        return TypeParameter.EqualitySupportValue.Unspecified;
      }
    }
  }

  string RedirectingTypeDecl.Name { get { return Name; } }
  IToken RedirectingTypeDecl.tok { get { return tok; } }
  IEnumerable<IToken> RedirectingTypeDecl.OwnedTokens => OwnedTokens;
  IToken RedirectingTypeDecl.StartToken => StartToken;
  Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
  ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
  BoundVar RedirectingTypeDecl.Var { get { return Var; } }
  Expression RedirectingTypeDecl.Constraint { get { return Constraint; } }
  SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
  Expression RedirectingTypeDecl.Witness { get { return Witness; } }
  FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

  bool ICodeContext.IsGhost {
    get { throw new NotSupportedException(); }  // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
  }
  List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
  string ICallable.NameRelativeToModule { get { return Name; } }
  Specification<Expression> ICallable.Decreases {
    get {
      // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
      // the question of what its Decreases clause is should never arise.
      throw new cce.UnreachableException();
    }
  }
  bool ICallable.InferredDecreases {
    get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
  }

  public override bool AcceptThis => true;

  public override bool IsEssentiallyEmpty() {
    // A "newtype" is not considered "essentially empty", because it always has a parent type to be resolved.
    return false;
  }
}

public abstract class TypeSynonymDeclBase : TopLevelDecl, RedirectingTypeDecl {
  public override string WhatKind { get { return "type synonym"; } }
  public TypeParameter.TypeParameterCharacteristics Characteristics;  // the resolver may change the .EqualitySupport component of this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
  }
  public readonly Type Rhs;

  protected TypeSynonymDeclBase(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeToken, name, module, typeArgs, attributes, false) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(module != null);
    Contract.Requires(rhs != null);
    Characteristics = characteristics;
    Rhs = rhs;
  }
  /// <summary>
  /// Return .Rhs instantiated with "typeArgs", but only look at the part of .Rhs that is in scope.
  /// </summary>
  public Type RhsWithArgument(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    var scope = Type.GetScope();
    var rtd = Rhs.AsRevealableType;
    if (rtd != null) {
      Contract.Assume(rtd.AsTopLevelDecl.IsVisibleInScope(scope));
      if (!rtd.IsRevealedInScope(scope)) {
        // type is actually hidden in this scope
        return rtd.SelfSynonym(typeArgs);
      }
    }
    return RhsWithArgumentIgnoringScope(typeArgs);
  }
  /// <summary>
  /// Returns the declared .Rhs but with formal type arguments replaced by the given actuals.
  /// </summary>
  public Type RhsWithArgumentIgnoringScope(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    // Instantiate with the actual type arguments
    if (typeArgs.Count == 0) {
      // this optimization seems worthwhile
      return Rhs;
    } else {
      var subst = TypeParameter.SubstitutionMap(TypeArgs, typeArgs);
      return Rhs.Subst(subst);
    }
  }

  public override IEnumerable<Node> Children => base.Children.Concat(Rhs.Nodes);

  string RedirectingTypeDecl.Name { get { return Name; } }
  IToken RedirectingTypeDecl.tok { get { return tok; } }
  IEnumerable<IToken> RedirectingTypeDecl.OwnedTokens => OwnedTokens;
  IToken RedirectingTypeDecl.StartToken => StartToken;
  Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
  ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
  BoundVar RedirectingTypeDecl.Var { get { return null; } }
  Expression RedirectingTypeDecl.Constraint { get { return null; } }
  SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return SubsetTypeDecl.WKind.CompiledZero; } }
  Expression RedirectingTypeDecl.Witness { get { return null; } }
  FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

  bool ICodeContext.IsGhost {
    get { throw new NotSupportedException(); }  // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
  }
  List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  bool ICodeContext.AllowsNontermination { get { return false; } }
  string ICallable.NameRelativeToModule { get { return Name; } }
  Specification<Expression> ICallable.Decreases {
    get {
      // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
      // the question of what its Decreases clause is should never arise.
      throw new cce.UnreachableException();
    }
  }
  bool ICallable.InferredDecreases {
    get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
  }
  public override bool CanBeRevealed() {
    return true;
  }

  public override bool IsEssentiallyEmpty() {
    // A synonym/subset type is not considered "essentially empty", because it always has a parent type to be resolved.
    return false;
  }
}

public class TypeSynonymDecl : TypeSynonymDeclBase, RevealableTypeDecl {
  public TypeSynonymDecl(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeToken, name, characteristics, typeArgs, module, rhs, attributes) {
    this.NewSelfSynonym();
  }
  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }
}

public class InternalTypeSynonymDecl : TypeSynonymDeclBase {
  public InternalTypeSynonymDecl(RangeToken rangeToken, string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeToken, name, characteristics, typeArgs, module, rhs, attributes) {
  }
}


public class SubsetTypeDecl : TypeSynonymDecl, RedirectingTypeDecl {
  public override string WhatKind { get { return "subset type"; } }
  public readonly BoundVar Var;
  public readonly Expression Constraint;
  public enum WKind { CompiledZero, Compiled, Ghost, OptOut, Special }
  public readonly SubsetTypeDecl.WKind WitnessKind;
  public readonly Expression/*?*/ Witness;  // non-null iff WitnessKind is Compiled or Ghost
  [FilledInDuringResolution] public bool ConstraintIsCompilable;
  [FilledInDuringResolution] public bool CheckedIfConstraintIsCompilable = false; // Set to true lazily by the Resolver when the Resolver fills in "ConstraintIsCompilable".
  public SubsetTypeDecl(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module,
    BoundVar id, Expression constraint, WKind witnessKind, Expression witness,
    Attributes attributes)
    : base(rangeToken, name, characteristics, typeArgs, module, id.Type, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(module != null);
    Contract.Requires(id != null && id.Type != null);
    Contract.Requires(constraint != null);
    Contract.Requires((witnessKind == WKind.Compiled || witnessKind == WKind.Ghost) == (witness != null));
    Var = id;
    Constraint = constraint;
    Witness = witness;
    WitnessKind = witnessKind;
  }

  public override IEnumerable<Node> Children => base.Children.Concat(new[] { Constraint });

  BoundVar RedirectingTypeDecl.Var { get { return Var; } }
  Expression RedirectingTypeDecl.Constraint { get { return Constraint; } }
  WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
  Expression RedirectingTypeDecl.Witness { get { return Witness; } }

  public override List<Type> ParentTypes(List<Type> typeArgs) {
    return new List<Type> { RhsWithArgument(typeArgs) };
  }
}

public class NonNullTypeDecl : SubsetTypeDecl {
  public override string WhatKind { get { return "non-null type"; } }
  public readonly ClassDecl Class;
  /// <summary>
  /// The public constructor is NonNullTypeDecl(ClassDecl cl). The rest is pretty crazy: There are stages of "this"-constructor calls
  /// in order to build values that depend on previously computed parameters.
  /// </summary>
  public NonNullTypeDecl(ClassDecl cl)
    : this(cl, cl.TypeArgs.ConvertAll(tp => new TypeParameter(tp.RangeToken, tp.Name, tp.VarianceSyntax, tp.Characteristics))) {
    Contract.Requires(cl != null);
  }

  private NonNullTypeDecl(ClassDecl cl, List<TypeParameter> tps)
    : this(cl, tps,
      new BoundVar(cl.RangeToken, "c", new UserDefinedType(cl.RangeToken, cl.Name + "?", tps.Count == 0 ? null : tps.ConvertAll(tp => (Type)new UserDefinedType(tp))))) {
    Contract.Requires(cl != null);
    Contract.Requires(tps != null);
  }

  private NonNullTypeDecl(ClassDecl cl, List<TypeParameter> tps, BoundVar id)
    : base(cl.RangeToken, cl.Name, new TypeParameter.TypeParameterCharacteristics(), tps, cl.EnclosingModuleDefinition, id,
      new BinaryExpr(cl.RangeToken, BinaryExpr.Opcode.Neq, new IdentifierExpr(cl.RangeToken, id), new LiteralExpr(cl.RangeToken)),
      SubsetTypeDecl.WKind.Special, null, BuiltIns.AxiomAttribute()) {
    Contract.Requires(cl != null);
    Contract.Requires(tps != null);
    Contract.Requires(id != null);
    Class = cl;
  }

  public override List<Type> ParentTypes(List<Type> typeArgs) {
    List<Type> result = new List<Type>(base.ParentTypes(typeArgs));

    foreach (var rhsParentType in Class.ParentTypes(typeArgs)) {
      var rhsParentUdt = (UserDefinedType)rhsParentType; // all parent types of .Class are expected to be possibly-null class types
      Contract.Assert(rhsParentUdt.ResolvedClass is ClassDecl);
      result.Add(UserDefinedType.CreateNonNullType(rhsParentUdt));
    }

    return result;
  }
}
