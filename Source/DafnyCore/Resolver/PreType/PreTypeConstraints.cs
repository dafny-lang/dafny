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
using JetBrains.Annotations;

namespace Microsoft.Dafny {
  /// <summary>
  /// This class holds the state of the pre-type inference. The state consists of a set of constraints; more precisely,
  /// it consists of lists of constraints, advice, and conditions to be confirmed.
  /// The class also contains methods for solving or partially solving these constraints.
  /// </summary>
  public class PreTypeConstraints {
    public readonly PreTypeResolver PreTypeResolver;
    private readonly DafnyOptions options;

    private List<SubtypeConstraint> unnormalizedSubtypeConstraints = new();
    private Queue<EqualityConstraint> equalityConstraints = new();
    private List<Func<bool>> guardedConstraints = new();
    private readonly List<Advice> defaultAdvice = new();
    private List<System.Action> confirmations = new();

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
    public DPreType ApproximateReceiverType(IToken tok, PreType preType, [CanBeNull] string memberName) {
      PartiallySolveTypeConstraints();

      preType = preType.Normalize();
      if (preType is DPreType dPreType) {
        return dPreType;
      }
      var proxy = (PreTypeProxy)preType;

      // If there is a subtype constraint "proxy :> sub<X>", then (if the program is legal at all, then) "sub" must have the member "memberName".
      foreach (var sub in AllSubBounds(proxy, new HashSet<PreTypeProxy>())) {
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

      return null; // could not be determined
    }

    /// <summary>
    /// Expecting that "preType" is a type that does not involve traits, return that type, if possible.
    /// </summary>
    [CanBeNull]
    public DPreType FindDefinedPreType(PreType preType) {
      Contract.Requires(preType != null);

      PartiallySolveTypeConstraints();

      preType = preType.Normalize();
      if (preType is PreTypeProxy proxy) {
        // We're looking a type with concerns for traits, so if the proxy has any sub- or super-type, then (if the
        // program is legal at all, then) that sub- or super-type must be the type we're looking for.
        foreach (var sub in AllSubBounds(proxy, new HashSet<PreTypeProxy>())) {
          return sub;
        }
        foreach (var super in AllSuperBounds(proxy, new HashSet<PreTypeProxy>())) {
          return super;
        }
        return null;
      }

      return preType as DPreType;
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
      confirmations.Clear();
      PreTypeResolver.allPreTypeProxies.Clear();
    }

    public void PrintTypeInferenceState(string/*?*/ header = null) {
      if (!options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      options.OutputWriter.WriteLine("*** Type inference state ***{0}", header == null ? "" : $" {header} ");
      PrintList("Subtype constraints", unnormalizedSubtypeConstraints, stc => {
        return $"{stc.Super} :> {stc.Sub}";
      });
      PrintList("Equality constraints", equalityConstraints, eqc => {
        return $"{eqc.A} == {eqc.B}";
      });
      options.OutputWriter.WriteLine($"    Guarded constraints: {guardedConstraints.Count}");
      PrintList("Default-type advice", defaultAdvice, advice => {
        return $"{advice.PreType} ~-~-> {advice.WhatString}";
      });
      options.OutputWriter.WriteLine($"    Post-inference confirmations: {confirmations.Count}");
    }

    void PrintLegend() {
      PrintList("Legend", PreTypeResolver.allPreTypeProxies, pair => {
        var s = Pad($"?{pair.Item1.UniqueId}", 4) + pair.Item1;
        return pair.Item2 == null ? s : $"{Pad(s, 20)}  {pair.Item2}";
      });
    }

    void PrintList<T>(string rubric, IEnumerable<T> list, Func<T, string> formatter) {
      if (!options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      options.OutputWriter.WriteLine($"    {rubric}:");
      foreach (var t in list) {
        var info = $"        {formatter(t)}";
        if (t is PreTypeConstraint preTypeConstraint) {
          info = $"{Pad(info, 30)}  {TokToShortLocation(preTypeConstraint.tok)}: {preTypeConstraint.ErrorMessage()}";
        }
        options.OutputWriter.WriteLine(info);
      }
    }

    public void AddEqualityConstraint(PreType a, PreType b, IToken tok, string msgFormat, PreTypeConstraint baseError = null) {
      equalityConstraints.Enqueue(new EqualityConstraint(a, b, tok, msgFormat, baseError));
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

    public void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString, PreTypeConstraint baseError = null) {
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatString, baseError));
    }

    public void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, Func<string> errorFormatStringProducer) {
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatStringProducer));
    }

    bool ApplySubtypeConstraints() {
      if (unnormalizedSubtypeConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = unnormalizedSubtypeConstraints;
      unnormalizedSubtypeConstraints = new();
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
                : MeetHeads(previousBest, bound.Decl);
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
        DebugPrint($"    DEBUG: head decision {proxy} := {pt}");
        AddEqualityConstraint(proxy, pt, constraint.tok, constraint.ErrorFormatString); // TODO: the message could be made more specific now (perhaps)
        anythingChanged = true;
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

    TopLevelDecl/*?*/ MeetHeads(TopLevelDecl a, TopLevelDecl b) {
      var aAncestors = new HashSet<TopLevelDecl>();
      if (aAncestors.Contains(b)) {
        // that's good enough; let's pick a
        return a;
      }
      var bAncestors = new HashSet<TopLevelDecl>();
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
      guardedConstraints = new();
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

    public void AddDefaultAdvice(PreType preType, Advice.Target advice) {
      defaultAdvice.Add(new Advice(preType, advice));
    }

    bool TryApplyDefaultAdvice() {
      bool anythingChanged = false;
      foreach (var advice in defaultAdvice) {
        anythingChanged |= advice.Apply(PreTypeResolver);
      }
      return anythingChanged;
    }

    public void AddConfirmation(CommonConfirmationBag check, PreType preType, IToken tok, string errorFormatString) {
      confirmations.Add(() => {
        if (!ConfirmConstraint(check, preType, null)) {
          PreTypeResolver.ReportError(tok, errorFormatString, preType);
        }
      });
    }

    public void AddConfirmation(CommonConfirmationBag check, PreType preType, Type toType, IToken tok, string errorFormatString) {
      Contract.Requires(toType is NonProxyType);
      var toPreType = (DPreType)PreTypeResolver.Type2PreType(toType);
      confirmations.Add(() => {
        if (!ConfirmConstraint(check, preType, toPreType)) {
          PreTypeResolver.ReportError(tok, errorFormatString, preType);
        }
      });
    }

    public void AddConfirmation(System.Action confirm) {
      confirmations.Add(confirm);
    }

    void ConfirmTypeConstraints() {
      foreach (var confirmation in confirmations) {
        confirmation();
      }
    }

    public enum CommonConfirmationBag {
      InIntFamily,
      InRealFamily,
      InBoolFamily,
      InCharFamily,
      InSeqFamily,
      IsNullableRefType,
      IsBitvector,
      IntLikeOrBitvector,
      NumericOrBitvector,
      NumericOrBitvectorOrCharOrORDINALOrSuchTrait,
      BooleanBits,
      IntOrORDINAL,
      IntOrBitvectorOrORDINAL,
      Plussable,
      Mullable,
      Disjointable,
      OrderableLess,
      OrderableGreater,
      RankOrderable,
      RankOrderableOrTypeParameter,
      Sizeable,
      Freshable,
      IsCoDatatype,
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
          return familyDeclName == "int";
        case CommonConfirmationBag.InRealFamily:
          return familyDeclName == "real";
        case CommonConfirmationBag.InBoolFamily:
          return familyDeclName == "bool";
        case CommonConfirmationBag.InCharFamily:
          return familyDeclName == "char";
        case CommonConfirmationBag.InSeqFamily:
          return familyDeclName == "seq";
        case CommonConfirmationBag.IsNullableRefType:
          return DPreType.IsReferenceTypeDecl(pt.Decl);
        case CommonConfirmationBag.IsBitvector:
          return PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.IntLikeOrBitvector:
          return familyDeclName == "int" || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.NumericOrBitvector:
          return familyDeclName is "int" or "real" || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.NumericOrBitvectorOrCharOrORDINALOrSuchTrait:
          if (familyDeclName is "int" or "real" or "char" or "ORDINAL" || PreTypeResolver.IsBitvectorName(familyDeclName)) {
            return true;
          }
          return PreTypeResolver.IsSuperPreTypeOf(pt, auxPreType);
        case CommonConfirmationBag.BooleanBits:
          return familyDeclName == "bool" || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.IntOrORDINAL:
          return familyDeclName == "int" || familyDeclName == "ORDINAL";
        case CommonConfirmationBag.IntOrBitvectorOrORDINAL:
          return familyDeclName == "int" || PreTypeResolver.IsBitvectorName(familyDeclName) || familyDeclName == "ORDINAL";
        case CommonConfirmationBag.Plussable:
          switch (familyDeclName) {
            case "int":
            case "real":
            case "ORDINAL":
            case "char":
            case "seq":
            case "set":
            case "iset":
            case "multiset":
            case "map":
            case "imap":
              return true;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.Mullable:
          switch (familyDeclName) {
            case "int":
            case "real":
            case "set":
            case "iset":
            case "multiset":
              return true;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.Disjointable:
          return familyDeclName == "set" || familyDeclName == "iset" || familyDeclName == "multiset";
        case CommonConfirmationBag.OrderableLess:
        case CommonConfirmationBag.OrderableGreater:
          switch (familyDeclName) {
            case "int":
            case "real":
            case "ORDINAL":
            case "char":
            case "set":
            case "iset":
            case "multiset":
              return true;
            case "seq":
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
            case "set": // but not "iset"
            case "multiset":
            case "seq":
            case "map": // but not "imap"
              return true;
            default:
              return false;
          }
        case CommonConfirmationBag.Freshable: {
            var t = familyDeclName == "set" || familyDeclName == "iset" || familyDeclName == "seq"
              ? ancestorPt.Arguments[0].Normalize() as DPreType
              : ancestorPt;
            return t != null && DPreType.IsReferenceTypeDecl(t.Decl);
          }
        case CommonConfirmationBag.IsCoDatatype:
          return ancestorDecl is CoDatatypeDecl;

        default:
          Contract.Assert(false); // unexpected case
          throw new cce.UnreachableException();
      }
    }

    /// <summary>
    /// If "super" is an ancestor of "sub", then return a list "L" of arguments for "super" such that
    /// "super<L>" is a supertype of "sub<subArguments>".
    /// Otherwise, return "null".
    /// </summary>
    public List<PreType> /*?*/ GetTypeArgumentsForSuperType(TopLevelDecl super, TopLevelDecl sub, List<PreType> subArguments) {
      Contract.Requires(sub.TypeArgs.Count == subArguments.Count);

      if (super == sub) {
        return subArguments;
      } else if (sub is TopLevelDeclWithMembers md) {
        var subst = PreType.PreTypeSubstMap(md.TypeArgs, subArguments);
        foreach (var parentType in AllParentTraits(md)) {
          var parentPreType = (DPreType)PreTypeResolver.Type2PreType(parentType).Substitute(subst);
          var arguments = GetTypeArgumentsForSuperType(super, parentPreType.Decl, parentPreType.Arguments);
          if (arguments != null) {
            return arguments;
          }
        }
      }
      return null;
    }

    /// <summary>
    /// AllParentTraits(decl) is like decl.ParentTraits, but also returns "object" if "decl" is a reference type.
    /// </summary>
    public IEnumerable<Type> AllParentTraits(TopLevelDeclWithMembers decl) {
      foreach (var parentType in decl.ParentTraits) {
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

    public static string TokToShortLocation(IToken tok) {
      return $"{System.IO.Path.GetFileName(tok.filename)}({tok.line},{tok.col - 1})";
    }

    public static string Pad(string s, int minWidth) {
      return s + new string(' ', Math.Max(minWidth - s.Length, 0));
    }

    public void DebugPrint(string format, params object[] args) {
      if (options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        options.OutputWriter.WriteLine(format, args);
      }
    }

  }
}