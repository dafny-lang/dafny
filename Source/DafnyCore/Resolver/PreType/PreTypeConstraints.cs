//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text;
using JetBrains.Annotations;
using Microsoft.Extensions.Primitives;

namespace Microsoft.Dafny {
  /// <summary>
  /// This class holds the state of the pre-type inference. The state consists of a set of constraints; more precisely,
  /// it consists of lists of constraints, advice, and conditions to be confirmed.
  /// The class also contains methods for solving or partially solving these constraints.
  /// </summary>
  public class PreTypeConstraints {
    public readonly PreTypeResolver PreTypeResolver;
    private readonly DafnyOptions options;

    private List<SubtypeConstraint> unnormalizedSubtypeConstraints = [];
    private Queue<EqualityConstraint> equalityConstraints = new();
    private List<Func<bool>> guardedConstraints = [];
    private readonly List<Advice> defaultAdvice = [];
    private List<(PreTypeProxy, PreType)> compatibleBounds = [];
    private List<Confirmation> confirmations = [];

    public PreTypeConstraints(PreTypeResolver preTypeResolver) {
      this.PreTypeResolver = preTypeResolver;
      this.options = preTypeResolver.resolver.Options;
    }

    /// <summary>
    /// Try to find the receiver pre-type that corresponds to "preType".
    /// If there are subtype constraints of "preType" that point out a non-proxy subtype of "preType", then one such is returned.
    /// Otherwise, if there are supertype constraints of "preType" that point out a non-proxy supertype of "preType" AND that supertype
    /// has a member named "memberName", then such a supertype is returned.
    /// Otherwise, null is returned.
    ///
    /// The "memberName" is allowed to be passed in as "null", in which case the supertype search does not consider any trait.
    /// </summary>
    [CanBeNull]
    public DPreType ApproximateReceiverType(PreType preType, [CanBeNull] string memberName) {
      PartiallySolveTypeConstraints();

      preType = preType.Normalize();
      if (preType is DPreType dPreType) {
        return dPreType;
      }
      if (preType is not PreTypeProxy proxy) {
        // preType could be a PreTypePlaceholder, resulting from an error somewhere
        return null;
      }

      var approximateReceiverType = ApproximateReceiverTypeViaBounds(proxy, memberName, out var subProxies);
      if (approximateReceiverType != null) {
        return approximateReceiverType;
      }

      // The bounds didn't give any results, but perhaps one of the proxies visited (in the sub direction) has
      // associated default advice.
      foreach (var subProxy in subProxies) {
        TryApplyDefaultAdviceFor(subProxy);
        if (proxy.Normalize() is DPreType defaultType) {
          return defaultType;
        }
      }

      // Try once more, in case the application of default advice changed the situation
      return ApproximateReceiverTypeViaBounds(proxy, memberName, out _);
    }

    [CanBeNull]
    private DPreType ApproximateReceiverTypeViaBounds(PreTypeProxy proxy, [CanBeNull] string memberName, out HashSet<PreTypeProxy> subProxies) {
      // If there is a subtype constraint "proxy :> sub<X>", then (if the program is legal at all, then) "sub" must have the member "memberName".
      subProxies = [];
      foreach (var sub in AllSubBounds(proxy, subProxies)) {
        return sub;
      }

      // If there is a subtype constraint "super<X> :> proxy" where "super" has a member "memberName", then that is the correct member.
      foreach (var super in AllSuperBounds(proxy, new HashSet<PreTypeProxy>())) {
        if (super.Decl is TopLevelDeclWithMembers md) {
          if (memberName != null && PreTypeResolver.resolver.GetClassMembers(md).ContainsKey(memberName)) {
            return super;
          } else if (memberName == null && md is not TraitDecl) {
            return super;
          }
        }
      }

      // As a final possibility, if there is a compatible-types constraint "ty ~~ proxy", then pick "ty" as the bound
      foreach (var (compatibleBoundsProxy, compatibleBoundsType) in compatibleBounds) {
        if (compatibleBoundsProxy.Normalize() == proxy && compatibleBoundsType.Normalize() is DPreType { Decl: TopLevelDeclWithMembers md } dPreType) {
          if (memberName == null || PreTypeResolver.resolver.GetClassMembers(md).ContainsKey(memberName)) {
            return dPreType;
          }
        }
      }

      return null;
    }

    /// <summary>
    /// Expecting that "preType" is a type that does not involve traits, return that type, if possible.
    /// </summary>
    [CanBeNull]
    public DPreType FindDefinedPreType(PreType preType, bool applyAdvice) {
      Contract.Requires(preType != null);

      PartiallySolveTypeConstraints();

      preType = preType.Normalize();
      if (preType is PreTypeProxy proxy) {
        // We're looking up a type with concerns for traits, so if the proxy has any sub- or super-type, then (if the
        // program is legal at all, then) that sub- or super-type must be the type we're looking for.
        foreach (var sub in AllSubBounds(proxy, new HashSet<PreTypeProxy>())) {
          return sub;
        }
        foreach (var super in AllSuperBounds(proxy, new HashSet<PreTypeProxy>())) {
          return super;
        }

        if (applyAdvice) {
          TryApplyDefaultAdviceFor(proxy);
        }
      }

      return preType.Normalize() as DPreType;
    }

    /// <summary>
    /// Solves or simplifies as many type constraints as possible.
    /// If "allowDecisions" is "false", then no decisions, only determined inferences, are made; this mode is
    /// appropriate for the partial solving that's done before a member lookup.
    /// Returns "true" if anything changed (that is, if any of the constraints in the type-inference state
    /// caused a change some pre-type proxy).
    /// </summary>
    public void PartiallySolveTypeConstraints(string printableContext = null, bool makeDecisions = false) {
      if (printableContext != null) {
        PrintTypeInferenceState("(partial) " + printableContext);
      }

      // Note, the various constraints that have been recorded may contain pre-types that refer to symbols that
      // are not in scope. Therefore, it is important that, at the onset processing any of these constraints,
      // each pre-type is normalized with respect to scope.
      bool anythingChanged;
      do {
        anythingChanged = makeDecisions && TryMakeDecisions();
        anythingChanged |= ApplySubtypeConstraints();
        anythingChanged |= ApplyEqualityConstraints();
        anythingChanged |= ApplyGuardedConstraints();
      } while (anythingChanged);
    }

    private bool TryMakeDecisions() {
      if (TryResolveTypeProxiesUsingKnownBounds(true, false)) {
        return true;
      } else if (TryResolveTypeProxiesUsingKnownBounds(false, false)) {
        return true;
      } else if (TryResolveTypeProxiesUsingKnownBounds(true, true)) {
        return true;
      } else if (TryResolveTypeProxiesUsingKnownBounds(false, true)) {
        return true;
      } else if (TryApplyDefaultAdvice()) {
        return true;
      } else if (TryUseCompatibleTypesAsBounds()) {
        return true;
      } else if (TryEquateBounds()) {
        return true;
      }
      return false;
    }

    public void SolveAllTypeConstraints(string printableContext) {
      PrintTypeInferenceState(printableContext);
      PartiallySolveTypeConstraints(null);

      PartiallySolveTypeConstraints(null, true);

      PrintLegend();
      ConfirmTypeConstraints();
      ClearState();
    }

    void ClearState() {
      unnormalizedSubtypeConstraints.Clear();
      equalityConstraints.Clear();
      guardedConstraints.Clear();
      defaultAdvice.Clear();
      compatibleBounds.Clear();
      confirmations.Clear();
      PreTypeResolver.allPreTypeProxies.Clear();
    }

    public void AssertThatStateIsClear() {
      Contract.Assert(unnormalizedSubtypeConstraints.Count == 0);
      Contract.Assert(equalityConstraints.Count == 0);
      Contract.Assert(guardedConstraints.Count == 0);
      Contract.Assert(defaultAdvice.Count == 0);
      Contract.Assert(confirmations.Count == 0);
      // Note, PreTypeResolver.allPreTypeProxies may still be nonempty, since it's not part of the PreTypeConstraint state proper
    }

    public void PrintTypeInferenceState(string/*?*/ header = null) {
      if (!options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }

      var stringWriter = new StringWriter();
      stringWriter.WriteLine($"*** Type inference state ***{(header == null ? "" : $" {header} ")}");
      PrintList(stringWriter, "Subtype constraints", unnormalizedSubtypeConstraints,
        stc => $"{stc.Super} :> {stc.Sub}");
      PrintList(stringWriter, "Equality constraints", equalityConstraints, eqc => $"{eqc.A} == {eqc.B}");
      stringWriter.WriteLine($"    Guarded constraints: {guardedConstraints.Count}");
      PrintList(stringWriter, "Default-type advice", defaultAdvice, advice => $"{advice.PreType} ~-~-> {advice.WhatString}");
      PrintList(stringWriter, "Post-inference confirmations", confirmations, confirmationInfo => confirmationInfo.DebugInformation());
      options.OutputWriter.Debug(stringWriter.ToString());
    }

    void PrintLegend() {
      if (!options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      var sw = new StringWriter();
      PrintList(sw, "Legend", PreTypeResolver.allPreTypeProxies, pair => {
        var s = Pad($"?{pair.Item1.UniqueId}", 4) + pair.Item1;
        return pair.Item2 == null ? s : $"{Pad(s, 20)}  {pair.Item2}";
      });
      options.OutputWriter.Debug(sw.ToString());
    }

    void PrintList<T>(TextWriter writer, string rubric, IEnumerable<T> list, Func<T, string> formatter) {
      if (!options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      writer.WriteLine($"    {rubric}:");
      foreach (var t in list) {
        var info = $"        {formatter(t)}";
        if (t is PreTypeConstraint preTypeConstraint) {
          info = $"{Pad(info, 30)}  {TokToShortLocation(preTypeConstraint.tok)}: {preTypeConstraint.ErrorMessage()}";
        }
        writer.WriteLine(info);
      }
    }

    public void AddEqualityConstraint(PreType a, PreType b, IOrigin tok, string msgFormat, PreTypeConstraint baseError = null, bool reportErrors = true) {
      equalityConstraints.Enqueue(new EqualityConstraint(a, b, tok, msgFormat, baseError, reportErrors));
    }

    private bool ApplyEqualityConstraints() {
      if (equalityConstraints.Count == 0) {
        return false;
      }
      // process equality constraints until there are no more
      while (equalityConstraints.Count != 0) {
        var constraint = equalityConstraints.Dequeue();
        foreach (var newConstraint in constraint.Apply(this)) {
          equalityConstraints.Enqueue(newConstraint);
        }
      }
      return true;
    }

    public void AddSubtypeConstraint(PreType super, PreType sub, IOrigin tok, string errorFormatString, PreTypeConstraint baseError = null, bool reportErrors = true) {
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatString, baseError, reportErrors));
    }

    public void AddSubtypeConstraint(PreType super, PreType sub, IOrigin tok, Func<string> errorFormatStringProducer) {
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatStringProducer));
    }

    bool ApplySubtypeConstraints() {
      if (unnormalizedSubtypeConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = unnormalizedSubtypeConstraints;
      unnormalizedSubtypeConstraints = [];
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        if (constraint.Apply(this)) {
          anythingChanged = true;
        } else {
          unnormalizedSubtypeConstraints.Add(constraint.Normalize());
        }
      }
      return anythingChanged;
    }

    /// <summary>
    /// Try to resolve each proxy using its sub-bound constraints (if "fromSubBounds" is "true") or
    /// its super-bound constraints (if "fromSubBounds" is "false"). Add an equality constraint for
    /// any proxy whose head can be determined.
    ///
    /// If "ignoreUnknowns" is true, then ignore any constraint where the bound is a proxy or for which the running join/meet computation
    /// is ill-defined.
    /// If "ignoreUnknowns" is false, then don't resolve a proxy if it has unknowns.
    ///
    /// Return "true" if any such equality constraint was added.
    /// </summary>
    bool TryResolveTypeProxiesUsingKnownBounds(bool fromSubBounds, bool ignoreUnknowns) {
      // First, compute the join/meet of the sub/super-bound heads of each proxy
      Dictionary<PreTypeProxy, TopLevelDecl> candidateHeads = new(); // if !ignoreUnknowns, map to null to indicate the proxy has unknowns
      Dictionary<PreTypeProxy, SubtypeConstraint> constraintOrigins = new();
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        var proxy = (fromSubBounds ? constraint.Super : constraint.Sub).Normalize() as PreTypeProxy;
        var bound = (fromSubBounds ? constraint.Sub : constraint.Super).Normalize() as DPreType;
        if (proxy != null) {
          if (!candidateHeads.TryGetValue(proxy, out var previousBest)) {
            // we haven't seen this proxy before
            if (bound != null) {
              candidateHeads.Add(proxy, bound.Decl);
              constraintOrigins.Add(proxy, constraint);
            } else if (!ignoreUnknowns) {
              candidateHeads.Add(proxy, null);
              constraintOrigins.Add(proxy, constraint);
            }
          } else if (previousBest == null) {
            Contract.Assert(!ignoreUnknowns);
            // proxy is already known to have unknowns
          } else {
            var combined = bound == null
              ? null
              : fromSubBounds
                ? JoinHeads(previousBest, bound.Decl, PreTypeResolver.resolver.SystemModuleManager)
                : MeetHeads(previousBest, bound.Decl, PreTypeResolver.resolver.SystemModuleManager);
            if (combined != null || !ignoreUnknowns) {
              candidateHeads[proxy] = combined;
            }
          }
        }
      }

      // Record equality constraints for each proxy that was determined
      var anythingChanged = false;
      foreach (var (proxy, best) in candidateHeads) {
        if (best == null) {
          Contract.Assert(!ignoreUnknowns);
          continue;
        }
        var pt = new DPreType(best, best.TypeArgs.ConvertAll(_ => PreTypeResolver.CreatePreTypeProxy()));
        var constraint = constraintOrigins[proxy];
        DebugPrint($"    head decision {proxy} := {pt}");
        AddEqualityConstraint(proxy, pt, constraint.tok, constraint.ErrorFormatString, null, constraint.ReportErrors); // TODO: the message could be made more specific now (perhaps)
        anythingChanged = true;
      }
      return anythingChanged;
    }

    /// <summary>
    /// For any bound ?x :> ?y, equate ?x and ?y.
    /// </summary>
    bool TryEquateBounds() {
      var anythingChanged = false;
      var constraints = unnormalizedSubtypeConstraints;
      unnormalizedSubtypeConstraints = new();
      foreach (var constraint in constraints) {
        if (constraint.Super.Normalize() is PreTypeProxy super && constraint.Sub.Normalize() is PreTypeProxy sub) {
          if (super != sub) {
            super.Set(sub);
            anythingChanged = true;
          }
        } else {
          unnormalizedSubtypeConstraints.Add(constraint);
        }
      }

      return anythingChanged;
    }

    public static TopLevelDecl/*?*/ JoinHeads(TopLevelDecl a, TopLevelDecl b, SystemModuleManager systemModuleManager) {
      var aAncestors = new HashSet<TopLevelDecl>();
      var bAncestors = new HashSet<TopLevelDecl>();
      PreTypeResolver.ComputeAncestors(a, aAncestors, systemModuleManager);
      PreTypeResolver.ComputeAncestors(b, bAncestors, systemModuleManager);
      var ancestors = aAncestors.Intersect(bAncestors).ToList();
      // Unless ancestors.Count == 1, there is no unique answer, and not necessary any way to determine the best
      // answer. As a heuristic, pick the element with the highest unique Height number. If there is no such
      // element, return null.
      while (ancestors.Count != 0) {
        var maxAmongAncestors = ancestors.Max(Height);
        var highestAncestors = ancestors.Where(ancestor => Height(ancestor) == maxAmongAncestors).ToList();
        if (highestAncestors.Count == 1) {
          return highestAncestors.ElementAt(0);
        }
        ancestors.RemoveAll(ancestor => Height(ancestor) == maxAmongAncestors);
      }
      return null;
    }

    TopLevelDecl/*?*/ MeetHeads(TopLevelDecl a, TopLevelDecl b, SystemModuleManager systemModuleManager) {
      var aAncestors = new HashSet<TopLevelDecl>();
      PreTypeResolver.ComputeAncestors(a, aAncestors, systemModuleManager);
      if (aAncestors.Contains(b)) {
        // that's good enough; let's pick a
        return a;
      }
      var bAncestors = new HashSet<TopLevelDecl>();
      PreTypeResolver.ComputeAncestors(b, bAncestors, systemModuleManager);
      if (bAncestors.Contains(a)) {
        // that's good enough; let's pick b
        return b;
      }
      // give up
      return null;
    }

    /// <summary>
    /// Return the trait height of "decl". The height is the smallest natural number that satisfies:
    ///   - The built-in trait "object" is strictly lower than anything else
    ///   - A declaration is strictly taller than any of its (explicit or implicit) parents
    ///
    /// The purpose of the "height" is to sort parent traits during type inference. For this purpose,
    /// it seems less surprising to have (the possibly implicit) "object" have a lower height than
    /// anything else. Here's an example:
    ///     trait Trait { } // note, this trait is not a reference type
    ///     class A extends Trait { }
    ///     class B extends Trait { }
    ///     method M(a: A, b: B) {
    ///       var z;
    ///       z := a;
    ///       z := b;
    ///     }
    /// What type do you expect z to have? Looking at the program text suggests z's type to be Trait,
    /// since Trait is a common parent of both A and B. But "object" is also a common parent of A and
    /// B, since A and B are classes. It seems more surprising to report "z has no best type" than
    /// to make "object" a "last resort" during type inference.
    /// </summary>
    public static int Height(TopLevelDecl decl) {
      if (decl is TraitDecl { IsObjectTrait: true }) {
        // object is at height 0
        return 0;
      }

      if (decl is TopLevelDeclWithMembers { ParentTraitHeads: { Count: > 0 } } topLevelDeclWithMembers) {
        // Note, if "decl" is a reference type, then its parents include "object", whether or not "object" is explicitly
        // included in "ParentTraitHeads". Since the "Max" in the following line will return a number 0 or
        // higher, the "Max" would be the same whether or not "object" is in the "ParentTraitHeads" list.
        return topLevelDeclWithMembers.ParentTraitHeads.Max(Height) + 1;
      } else if (decl is TypeParameter { TypeBounds: { Count: > 0 } } typeParameter) {
        return typeParameter.TypeBoundHeads.Max(Height) + 1;
      } else {
        // Other other declarations have height 1.
        // Note, an ostensibly parent-less reference type still has the implicit "object" as a parent trait, but
        // that still makes its height 1.
        return 1;
      }
    }

    private IEnumerable<DPreType> AllSubBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (visited.Contains(proxy)) {
        yield break;
      }
      visited.Add(proxy);
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        if (constraint.Super.Normalize() == proxy) {
          var sub = constraint.Sub.Normalize();
          if (sub is PreTypeProxy subProxy) {
            foreach (var pt in AllSubBounds(subProxy, visited)) {
              yield return pt;
            }
          } else {
            yield return (DPreType)sub;
          }
        }
      }
    }

    private IEnumerable<DPreType> AllSuperBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (visited.Contains(proxy)) {
        yield break;
      }
      visited.Add(proxy);
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        if (constraint.Sub.Normalize() == proxy) {
          var super = constraint.Super.Normalize();
          if (super is PreTypeProxy superProxy) {
            foreach (var pt in AllSuperBounds(superProxy, visited)) {
              yield return pt;
            }
          } else {
            yield return (DPreType)super;
          }
        }
      }
    }

    public IEnumerable<PreType> DirectionalBounds(PreTypeProxy tproxy, int direction) {
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        if (0 <= direction && constraint.Super.Normalize() == tproxy) {
          yield return constraint.Sub;
        }
        if (direction <= 0 && constraint.Sub.Normalize() == tproxy) {
          yield return constraint.Super;
        }
      }
    }

    public void AddGuardedConstraint(Func<bool> predicate) {
      guardedConstraints.Add(predicate);
    }

    bool ApplyGuardedConstraints() {
      if (guardedConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = guardedConstraints;
      guardedConstraints = [];
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        if (constraint()) {
          anythingChanged = true;
        } else {
          guardedConstraints.Add(constraint);
        }
      }
      return anythingChanged;
    }

    public void AddDefaultAdvice(PreType preType, CommonAdvice.Target advice) {
      defaultAdvice.Add(new CommonAdvice(preType, advice));
    }

    public void AddDefaultAdvice(PreType preType, PreType adviceType) {
      defaultAdvice.Add(new TypeAdvice(preType, adviceType));
    }

    bool TryApplyDefaultAdvice() {
      bool anythingChanged = false;
      foreach (var advice in defaultAdvice) {
        anythingChanged |= advice.Apply(PreTypeResolver);
      }
      return anythingChanged;
    }

    bool TryApplyDefaultAdviceFor(PreTypeProxy proxy) {
      foreach (var advice in defaultAdvice) {
        if (advice.ApplyFor(proxy, PreTypeResolver)) {
          return true;
        }
      }
      return false;
    }

    bool TryUseCompatibleTypesAsBounds() {
      if (compatibleBounds.Count == 0) {
        // common special case
        return false;
      }
      var bounds = compatibleBounds;
      compatibleBounds = new();

      // if there is a compatible-types constraint "ty ~~ proxy", then decide on the bound "ty :> proxy"
      bool anythingChanged = false;
      foreach (var item in bounds) {
        var (compatibleBoundsProxy, compatibleBoundsType) = item;
        if (compatibleBoundsProxy.Normalize() is PreTypeProxy proxy) {
          if (!compatibleBoundsType.Contains(proxy, 1, new HashSet<PreTypeProxy>(), this, 0)) {
            proxy.Set(compatibleBoundsType);
            anythingChanged = true;
          }
        } else {
          compatibleBounds.Add(item);
        }
      }
      return anythingChanged;
    }

    public void AddConfirmation(CommonConfirmationBag check, PreType preType, IOrigin tok, string errorFormatString, Action onProxyAction) {
      confirmations.Add(new Confirmation(
        () => ConfirmConstraint(check, preType, null),
        () => string.Format(errorFormatString, preType),
        (ResolverPass reporter) => {
          if (preType.Normalize() is PreTypeProxy && onProxyAction != null) {
            onProxyAction();
          } else {
            reporter.ReportError(tok, errorFormatString, preType);
          }
        }));
    }

    public void AddConfirmation(IOrigin tok, Func<bool> check, Func<string> errorMessage) {
      confirmations.Add(new Confirmation(check, errorMessage,
        (ResolverPass reporter) => { reporter.ReportError(tok, errorMessage()); }));
    }

    /// <summary>
    /// Make a note that a possible super bound for "proxy" is "possibleSuperBound". It can later be consulted and
    /// acted on if "proxy" is not constrained in any other way.
    /// </summary>
    public void AddCompatibleBounds(PreTypeProxy proxy, PreType possibleSuperBound) {
      compatibleBounds.Add((proxy, possibleSuperBound));
    }

    void ConfirmTypeConstraints() {
      foreach (var confirmation in confirmations) {
        confirmation.Confirm(PreTypeResolver);
      }
    }

    record Confirmation(Func<bool> Check, Func<string> ErrorMessage, Action<ResolverPass> OnError) {
      public void Confirm(ResolverPass reporter) {
        if (!Check()) {
          OnError(reporter);
        }
      }

      public string DebugInformation() {
        return ErrorMessage();
      }
    }

    public enum CommonConfirmationBag {
      InIntFamily,
      InRealFamily,
      InBoolFamily,
      InCharFamily,
      InSetFamily,
      InIsetFamily,
      InMultisetFamily,
      InSeqFamily,
      InMapFamily,
      InImapFamily,
      IsNullableRefType,
      IsBitvector,
      IntLikeOrBitvector,
      NumericOrBitvector,
      NumericOrBitvectorOrCharOrORDINALOrSuchTrait,
      BooleanBits,
      IntOrORDINAL,
      IntOrBitvectorOrORDINAL,
      Plussable,
      Minusable,
      Mullable,
      Disjointable,
      OrderableLess,
      OrderableGreater,
      RankOrderable,
      RankOrderableOrTypeParameter,
      Sizeable,
      Freshable,
      IsCoDatatype,
      IsNewtypeBaseTypeLegacy,
      IsNewtypeBaseTypeGeneral,
    };

    private bool ConfirmConstraint(CommonConfirmationBag check, PreType preType, DPreType auxPreType) {
      preType = preType.Normalize();
      if (preType is PreTypeProxy) {
        return false;
      }

      var pt = (DPreType)preType;
      var ancestorPt = PreTypeResolver.NewTypeAncestor(pt);
      var ancestorDecl = ancestorPt.Decl;
      var familyDeclName = ancestorDecl.Name;
      switch (check) {
        case CommonConfirmationBag.InIntFamily:
          return familyDeclName == PreType.TypeNameInt;
        case CommonConfirmationBag.InRealFamily:
          return familyDeclName == PreType.TypeNameReal;
        case CommonConfirmationBag.InBoolFamily:
          return familyDeclName == PreType.TypeNameBool;
        case CommonConfirmationBag.InCharFamily:
          return familyDeclName == PreType.TypeNameChar;
        case CommonConfirmationBag.InSetFamily:
          return familyDeclName == PreType.TypeNameSet;
        case CommonConfirmationBag.InIsetFamily:
          return familyDeclName == PreType.TypeNameIset;
        case CommonConfirmationBag.InMultisetFamily:
          return familyDeclName == PreType.TypeNameMultiset;
        case CommonConfirmationBag.InSeqFamily:
          return familyDeclName == PreType.TypeNameSeq;
        case CommonConfirmationBag.InMapFamily:
          return familyDeclName == PreType.TypeNameMap;
        case CommonConfirmationBag.InImapFamily:
          return familyDeclName == PreType.TypeNameImap;
        case CommonConfirmationBag.IsNullableRefType:
          return DPreType.IsReferenceTypeDecl(pt.Decl);
        case CommonConfirmationBag.IsBitvector:
          return PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.IntLikeOrBitvector:
          return familyDeclName == PreType.TypeNameInt || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.NumericOrBitvector:
          return familyDeclName is PreType.TypeNameInt or PreType.TypeNameReal || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.NumericOrBitvectorOrCharOrORDINALOrSuchTrait:
          if (familyDeclName is PreType.TypeNameInt or PreType.TypeNameReal or PreType.TypeNameChar or PreType.TypeNameORDINAL ||
              PreTypeResolver.IsBitvectorName(familyDeclName)) {
            return true;
          }
          return PreTypeResolver.IsSuperPreTypeOf(pt, auxPreType);
        case CommonConfirmationBag.BooleanBits:
          return familyDeclName == PreType.TypeNameBool || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.IntOrORDINAL:
          return familyDeclName is PreType.TypeNameInt or PreType.TypeNameORDINAL;
        case CommonConfirmationBag.IntOrBitvectorOrORDINAL:
          return familyDeclName == PreType.TypeNameInt || PreTypeResolver.IsBitvectorName(familyDeclName) || familyDeclName == PreType.TypeNameORDINAL;
        case CommonConfirmationBag.Plussable:
          switch (familyDeclName) {
            case PreType.TypeNameInt:
            case PreType.TypeNameReal:
            case PreType.TypeNameORDINAL:
            case PreType.TypeNameChar:
            case PreType.TypeNameSeq:
            case PreType.TypeNameSet:
            case PreType.TypeNameIset:
            case PreType.TypeNameMultiset:
            case PreType.TypeNameMap:
            case PreType.TypeNameImap:
              return true;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.Minusable:
          switch (familyDeclName) {
            case PreType.TypeNameInt:
            case PreType.TypeNameReal:
            case PreType.TypeNameORDINAL:
            case PreType.TypeNameChar:
            case PreType.TypeNameSet:
            case PreType.TypeNameIset:
            case PreType.TypeNameMultiset:
            case PreType.TypeNameMap:
            case PreType.TypeNameImap:
              return true;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.Mullable:
          switch (familyDeclName) {
            case PreType.TypeNameInt:
            case PreType.TypeNameReal:
            case PreType.TypeNameSet:
            case PreType.TypeNameIset:
            case PreType.TypeNameMultiset:
              return true;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.Disjointable:
          return familyDeclName is PreType.TypeNameSet or PreType.TypeNameIset or PreType.TypeNameMultiset;
        case CommonConfirmationBag.OrderableLess:
        case CommonConfirmationBag.OrderableGreater:
          switch (familyDeclName) {
            case PreType.TypeNameInt:
            case PreType.TypeNameReal:
            case PreType.TypeNameORDINAL:
            case PreType.TypeNameChar:
            case PreType.TypeNameSet:
            case PreType.TypeNameIset:
            case PreType.TypeNameMultiset:
              return true;
            case PreType.TypeNameSeq:
              return check == CommonConfirmationBag.OrderableLess;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.RankOrderable:
          return ancestorDecl is IndDatatypeDecl;
        case CommonConfirmationBag.RankOrderableOrTypeParameter:
          return ancestorDecl is IndDatatypeDecl || ancestorDecl is TypeParameter;
        case CommonConfirmationBag.Sizeable:
          switch (familyDeclName) {
            case PreType.TypeNameSet: // but not "iset"
            case PreType.TypeNameMultiset:
            case PreType.TypeNameSeq:
            case PreType.TypeNameMap: // but not "imap"
              return true;
            default:
              return false;
          }
        case CommonConfirmationBag.Freshable: {
            var t = familyDeclName is PreType.TypeNameSet or PreType.TypeNameIset or PreType.TypeNameSeq
              ? ancestorPt.Arguments[0].Normalize() as DPreType
              : ancestorPt;
            return t != null && DPreType.IsReferenceTypeDecl(t.Decl);
          }
        case CommonConfirmationBag.IsCoDatatype:
          return ancestorDecl is CoDatatypeDecl;
        case CommonConfirmationBag.IsNewtypeBaseTypeLegacy:
          return pt.Decl is NewtypeDecl || pt.Decl.Name is PreType.TypeNameInt or PreType.TypeNameReal;
        case CommonConfirmationBag.IsNewtypeBaseTypeGeneral:
          if (pt.Decl is DatatypeDecl) {
            // These base types are not yet supported, but they will be soon.
            return false;
          }
          if (pt.Decl is NewtypeDecl) {
            return true;
          }
          if (DPreType.IsReferenceTypeDecl(pt.Decl) || pt.Decl is TraitDecl) {
            return false;
          }
          if (ArrowType.IsArrowTypeName(familyDeclName) || pt.Decl.Name == PreType.TypeNameORDINAL) {
            return false;
          }
          return true;
        default:
          Contract.Assert(false); // unexpected case
          throw new Cce.UnreachableException();
      }
    }

    /// <summary>
    /// If "super" is an ancestor of "sub.Decl", then return a list "L" of arguments for "super" such that
    /// "super<L>" is a supertype of "sub".
    /// Otherwise, return "null".
    /// If "allowBaseTypeCast" is "true", then allow "sub" to be replaced by an ancestor type of "sub" if "sub" is a newtype.
    /// </summary>
    [CanBeNull]
    public List<PreType> GetTypeArgumentsForSuperType(TopLevelDecl super, DPreType sub, bool allowBaseTypeCast) {
      if (super == sub.Decl) {
        return sub.Arguments;
      }

      foreach (var parentPreType in ParentPreTypes(sub)) {
        var arguments = GetTypeArgumentsForSuperType(super, parentPreType, false);
        if (arguments != null) {
          return arguments;
        }
      }

      if (sub.Decl is TypeParameter typeParameter) {
        foreach (var preTypeBound in PreTypeResolver.TypeParameterBounds2PreTypes(typeParameter)) {
          var arguments = GetTypeArgumentsForSuperType(super, preTypeBound, allowBaseTypeCast);
          if (arguments != null) {
            return arguments;
          }
        }
      }

      if (allowBaseTypeCast && sub.Decl is NewtypeDecl newtypeDecl) {
        var subst = PreType.PreTypeSubstMap(newtypeDecl.TypeArgs, sub.Arguments);
        if (newtypeDecl.BasePreType.Substitute(subst) is DPreType basePreType) {
          var arguments = GetTypeArgumentsForSuperType(super, basePreType, true);
          if (arguments != null) {
            return arguments;
          }
        }
      }

      return null;
    }

    public IEnumerable<DPreType> ParentPreTypes(DPreType dPreType) {
      if (dPreType.Decl is TopLevelDeclWithMembers md) {
        var subst = PreType.PreTypeSubstMap(md.TypeArgs, dPreType.Arguments);
        foreach (var parentType in AllParentTraits(md)) {
          yield return (DPreType)PreTypeResolver.Type2PreType(parentType).Substitute(subst);
        }
      }
    }

    /// <summary>
    /// AllParentTraits(decl) is like decl.ParentTraits, but also returns "object" if "decl" is a reference type.
    /// </summary>
    public IEnumerable<Type> AllParentTraits(TopLevelDeclWithMembers decl) {
      foreach (var parentType in decl.Traits) {
        yield return parentType;
      }
      if (DPreType.IsReferenceTypeDecl(decl)) {
        if (decl is TraitDecl { IsObjectTrait: true }) {
          // don't return object itself
        } else {
          yield return PreTypeResolver.resolver.SystemModuleManager.ObjectQ();
        }
      }
    }

    public static string TokToShortLocation(IOrigin tok) {
      return $"{System.IO.Path.GetFileName(tok.filename)}({tok.line},{tok.col - 1})";
    }

    public static string Pad(string s, int minWidth) {
      return s + new string(' ', Math.Max(minWidth - s.Length, 0));
    }

    public void DebugPrint(string message) {
      if (options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        options.OutputWriter.Debug(message);
      }
    }
  }
}
