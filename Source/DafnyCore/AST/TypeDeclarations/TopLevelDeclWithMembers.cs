using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public abstract class TopLevelDeclWithMembers : TopLevelDecl {
  public readonly List<MemberDecl> Members;

  protected TopLevelDeclWithMembers(Cloner cloner, TopLevelDeclWithMembers original) 
    : base(cloner.Range(original.RangeToken), original.NameNode.Clone(cloner), 
      original.EnclosingModuleDefinition, original.TypeArgs.ConvertAll(cloner.CloneTypeParam), cloner.CloneAttributes(original.Attributes), original.IsRefining) 
  {
    Members = original.Members.ConvertAll(member => {
      var newMember = cloner.CloneMember(member, false);
      newMember.EnclosingClass = this;
      return newMember;
    });
  }

  // TODO remove this and instead clone the AST after parsing.
  public ImmutableList<MemberDecl> MembersBeforeResolution;

  // The following fields keep track of parent traits
  public readonly List<MemberDecl> InheritedMembers = new();  // these are instance members declared in parent traits
  public readonly List<Type> ParentTraits;  // these are the types that are parsed after the keyword 'extends'; note, for a successfully resolved program, these are UserDefinedType's where .ResolvedClass is NonNullTypeDecl
  public readonly Dictionary<TypeParameter, Type> ParentFormalTypeParametersToActuals = new Dictionary<TypeParameter, Type>();  // maps parent traits' type parameters to actuals

  /// <summary>
  /// TraitParentHeads contains the head of each distinct trait parent. It is initialized during resolution.
  /// </summary>
  public readonly List<TraitDecl> ParentTraitHeads = new List<TraitDecl>();

  internal bool HeadDerivesFrom(TopLevelDecl b) {
    Contract.Requires(b != null);
    return this == b || this.ParentTraitHeads.Exists(tr => tr.HeadDerivesFrom(b));
  }

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

  protected TopLevelDeclWithMembers(RangeToken rangeToken, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, List<MemberDecl> members, Attributes attributes,
    bool isRefining, List<Type>/*?*/ traits = null)
    : base(rangeToken, name, module, typeArgs, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
    Members = members;
    ParentTraits = traits ?? new List<Type>();
    SetMembersBeforeResolution();
  }

  public void SetMembersBeforeResolution() {
    MembersBeforeResolution = Members.ToImmutableList();
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
      var u = new UserDefinedType(t.Tok, t.Name + "?", t, typeArgs);
      types.Add(u);
    }
    return types;
  }

  public override IEnumerable<Node> Children => ParentTraits.Concat<Node>(Members);

  public override IEnumerable<Node> PreResolveChildren => ParentTraits.Concat<Node>(MembersBeforeResolution);

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

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    return Members.SelectMany(m => m.Assumptions(this));
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