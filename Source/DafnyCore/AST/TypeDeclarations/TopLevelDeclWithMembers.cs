#nullable enable
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class TopLevelDeclWithMembers : TopLevelDecl, IHasSymbolChildren {
  public List<MemberDecl> Members;

  // TODO remove this and instead clone the AST after parsing.
  public ImmutableList<MemberDecl>? MembersBeforeResolution;

  // The following fields keep track of parent traits
  public List<MemberDecl> InheritedMembers = [];  // these are instance members declared in parent traits
  public List<Type> Traits;  // these are the types that are parsed after the keyword 'extends'; note, for a successfully resolved program, these are UserDefinedType's where .ResolvedClass is NonNullTypeDecl
  public Dictionary<TypeParameter, Type> ParentFormalTypeParametersToActuals = new Dictionary<TypeParameter, Type>();  // maps parent traits' type parameters to actuals

  /// <summary>
  /// TraitParentHeads contains the head of each distinct trait parent. It is initialized during resolution.
  /// </summary>
  public List<TraitDecl> ParentTraitHeads = [];

  internal bool HeadDerivesFrom(TopLevelDecl b) {
    return this == b || this.ParentTraitHeads.Exists(tr => tr.HeadDerivesFrom(b));
  }

  public void AddParentTypeParameterSubstitutions(Dictionary<TypeParameter, Type> typeMap) {
    foreach (var entry in ParentFormalTypeParametersToActuals) {
      var v = entry.Value.Subst(typeMap);
      typeMap.Add(entry.Key, v);
    }
  }

  [FilledInDuringResolution] public InheritanceInformationClass? ParentTypeInformation;
  public class InheritanceInformationClass {
    private Dictionary<TraitDecl, List<(Type, List<TraitDecl> /*via this parent path*/)>> info = new Dictionary<TraitDecl, List<(Type, List<TraitDecl>)>>();

    /// <summary>
    /// Returns a subset of the trait's ParentTraits, but not repeating any head type.
    /// Assumes the declaration has been successfully resolved.
    /// </summary>
    public List<Type> UniqueParentTraits() {
      return info.ToList().ConvertAll(entry => entry.Value[0].Item1);
    }

    public void Record(TraitDecl traitHead, UserDefinedType parentType) {
      Contract.Requires(parentType.ResolvedClass is NonNullTypeDecl nntd && nntd.ViewAsClass == traitHead);

      if (!info.TryGetValue(traitHead, out var list)) {
        list = [];
        info.Add(traitHead, list);
      }
      list.Add((parentType, []));
    }

    public void Extend(TraitDecl parent, InheritanceInformationClass parentInfo, Dictionary<TypeParameter, Type> typeMap) {

      foreach (var entry in parentInfo.info) {
        var traitHead = entry.Key;
        if (!info.TryGetValue(traitHead, out var list)) {
          list = [];
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

  [SyntaxConstructor]
  protected TopLevelDeclWithMembers(IOrigin origin, Name nameNode, ModuleDefinition enclosingModuleDefinition,
    List<TypeParameter> typeArgs, List<MemberDecl> members, Attributes? attributes,
    List<Type> traits)
    : base(origin, nameNode, enclosingModuleDefinition, typeArgs, attributes) {
    Members = members;
    Traits = traits;
    SetMembersBeforeResolution();
  }

  public void SetMembersBeforeResolution() {
    MembersBeforeResolution = Members.ToImmutableList();
  }

  public List<Type> RawTraitsWithArgument(List<Type> typeArgs) {
    Contract.Requires(typeArgs.Count == TypeArgs.Count);

    // Instantiate with the actual type arguments
    var subst = TypeParameter.SubstitutionMap(TypeArgs, typeArgs);
    var isReferenceType = this is ClassLikeDecl { IsReferenceTypeDecl: true };
    var results = new List<Type>();
    foreach (var traitType in Traits) {
      var ty = (UserDefinedType)traitType.Subst(subst);
      Contract.Assert(isReferenceType || !ty.IsRefType);
      results.Add(UserDefinedType.CreateNullableTypeIfReferenceType(ty));
    }
    return results;
  }

  public override List<Type> ParentTypes(List<Type> typeArgs, bool includeTypeBounds) {
    return RawTraitsWithArgument(typeArgs);
  }

  public static List<UserDefinedType> CommonTraits(TopLevelDeclWithMembers a, TopLevelDeclWithMembers b) {
    var aa = a.TraitAncestors();
    var bb = b.TraitAncestors();
    aa.IntersectWith(bb);
    var types = new List<UserDefinedType>();
    foreach (var t in aa) {
      var typeArgs = t.TypeArgs.ConvertAll(tp => a.ParentFormalTypeParametersToActuals[tp]);
      var u = new UserDefinedType(t.Origin, t.Name + "?", t, typeArgs);
      types.Add(u);
    }
    return types;
  }

  public override IEnumerable<INode> Children => Traits.Concat<Node>(Members);

  public override IEnumerable<INode> PreResolveChildren => Traits.Concat<Node>(MembersBeforeResolution);

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
    foreach (var parent in Traits) {
      var udt = (UserDefinedType)parent;  // in a successfully resolved program, we expect all .ParentTraits to be a UserDefinedType
      TraitDecl tr;
      if (udt.ResolvedClass is NonNullTypeDecl nntd) {
        tr = (TraitDecl)nntd.Class;
      } else {
        tr = (TraitDecl)udt.ResolvedClass;
      }
      s.Add(tr);
      tr.AddTraitAncestors(s);
    }
  }

  // True if non-static members can access the underlying object "this"
  // False if all members are implicitly static (e.g. in a default class declaration)
  public abstract bool AcceptThis { get; }

  public override bool IsEssentiallyEmpty() {
    if (Members.Count != 0 || Traits.Count != 0) {
      return false;
    }
    return base.IsEssentiallyEmpty();
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    foreach (var a in base.Assumptions(this)) {
      yield return a;
    }

    foreach (var a in Members.SelectMany(m => m.Assumptions(this))) {
      yield return a;
    }

    if (Attributes.Contains(Attributes, "AssumeCrossModuleTermination")) {
      yield return new Assumption(this, Origin, AssumptionDescription.HasAssumeCrossModuleTerminationAttribute);
    }
  }

  public void RegisterMembers(ModuleResolver resolver, Dictionary<string, MemberDecl> members) {
    foreach (MemberDecl m in Members) {
      if (members.TryAdd(m.Name, m)) {
        switch (m) {
          case Constructor: {
              Contract.Assert(this is ClassLikeDecl); // the parser ensures this condition
              if (this is TraitDecl) {
                resolver.reporter.Error(MessageSource.Resolver, m.Origin, "a trait is not allowed to declare a constructor");
              } else {
                ((ClassDecl)this).HasConstructor = true;
              }

              break;
            }
          case ExtremePredicate or ExtremeLemma: {
              var extraName = m.NameNode.Append("#");
              MemberDecl extraMember;
              var cloner = new Cloner();
              var formals = new List<Formal>();
              Type typeOfK;
              if ((m is ExtremePredicate && ((ExtremePredicate)m).KNat) ||
                  (m is ExtremeLemma && ((ExtremeLemma)m).KNat)) {
                typeOfK = new UserDefinedType(m.Origin, "nat", null);
              } else {
                typeOfK = new BigOrdinalType();
              }

              var k = new ImplicitFormal(m.Origin, "_k", typeOfK, true, false);
              resolver.reporter.Info(MessageSource.Resolver, m.Origin, string.Format("_k: {0}", k.Type));
              formals.Add(k);
              if (m is ExtremePredicate extremePredicate) {
                formals.AddRange(extremePredicate.Ins.ConvertAll(f => cloner.CloneFormal(f, false)));

                List<TypeParameter> tyvars = extremePredicate.TypeArgs.ConvertAll(cloner.CloneTypeParam);

                // create prefix predicate
                extremePredicate.PrefixPredicate = new PrefixPredicate(extremePredicate.Origin, extraName, extremePredicate.HasStaticKeyword,
                  tyvars, k, formals,
                  extremePredicate.Req.ConvertAll(cloner.CloneAttributedExpr),
                  cloner.CloneSpecFrameExpr(extremePredicate.Reads),
                  extremePredicate.Ens.ConvertAll(cloner.CloneAttributedExpr),
                  new Specification<Expression>([new IdentifierExpr(extremePredicate.Origin, k.Name)], null),
                  cloner.CloneExpr(extremePredicate.Body),
                  SystemModuleManager.AxiomAttribute(),
                  extremePredicate);
                extraMember = extremePredicate.PrefixPredicate;
              } else {
                var extremeLemma = (ExtremeLemma)m;
                // _k has already been added to 'formals', so append the original formals
                formals.AddRange(extremeLemma.Ins.ConvertAll(f => cloner.CloneFormal(f, false)));
                // prepend _k to the given decreases clause
                var decr = new List<Expression>();
                decr.Add(new IdentifierExpr(extremeLemma.Origin, k.Name));
                decr.AddRange(extremeLemma.Decreases.Expressions!.ConvertAll(cloner.CloneExpr));
                // Create prefix lemma.  Note that the body is not cloned, but simply shared.
                // For a greatest lemma, the postconditions are filled in after the greatest lemma's postconditions have been resolved.
                // For a least lemma, the preconditions are filled in after the least lemma's preconditions have been resolved.
                var req = extremeLemma is GreatestLemma
                  ? extremeLemma.Req.ConvertAll(cloner.CloneAttributedExpr)
                  : new List<AttributedExpression>();
                var ens = extremeLemma is GreatestLemma
                  ? new List<AttributedExpression>()
                  : extremeLemma.Ens.ConvertAll(cloner.CloneAttributedExpr);
                extremeLemma.PrefixLemma = new PrefixLemma(new CanVerifyOrigin(extremeLemma), extraName, extremeLemma.HasStaticKeyword,
                  extremeLemma.TypeArgs.ConvertAll(cloner.CloneTypeParam), k, formals, extremeLemma.Outs.ConvertAll(f => cloner.CloneFormal(f, false)),
                  req, cloner.CloneSpecFrameExpr(extremeLemma.Reads),
                  cloner.CloneSpecFrameExpr(extremeLemma.Mod), ens,
                  new Specification<Expression>(decr, null),
                  null, // Note, the body for the prefix method will be created once the call graph has been computed and the SCC for the greatest lemma is known
                  SystemModuleManager.AxiomAttribute(cloner.CloneAttributes(extremeLemma.Attributes)), extremeLemma);
                extraMember = extremeLemma.PrefixLemma;
              }

              extraMember.InheritVisibility(m, false);
              members.Add(extraName.Value, extraMember);
              break;
            }
          case Function { ByMethodBody: not null } f:
            resolver.RegisterByMethod(f, this);
            break;
        }
      } else if (m is Constructor { HasName: false } constructor) {
        resolver.reporter.Error(MessageSource.Resolver, constructor, "More than one anonymous constructor");
      } else {
        resolver.reporter.Error(MessageSource.Resolver, m, "Duplicate member name: {0}", m.Name);
      }
    }
  }
  public virtual IEnumerable<ISymbol> ChildSymbols => Members.OfType<ISymbol>();
  public override SymbolKind? Kind => SymbolKind.Class;
  public override string GetDescription(DafnyOptions options) {
    return $"{WhatKind} {Name}";
  }
}

public static class RevealableTypeDeclHelper {
  public static InternalTypeSynonymDecl SelfSynonymDecl(this RevealableTypeDecl rtd) =>
    rtd.SynonymInfo.SelfSynonymDecl;

  public static UserDefinedType SelfSynonym(this RevealableTypeDecl rtd, List<Type> args, Expression? namePath = null) =>
    rtd.SynonymInfo.SelfSynonym(args, namePath);

  //Internal implementations are called before extensions, so this is safe
  public static bool IsRevealedInScope(this RevealableTypeDecl rtd, VisibilityScope scope) =>
    rtd.AsTopLevelDecl.IsRevealedInScope(scope);

  public static void NewSelfSynonym(this RevealableTypeDecl rtd) {
    rtd.SynonymInfo = new TypeDeclSynonymInfo(rtd.AsTopLevelDecl);
  }
}