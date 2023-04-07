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
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {
    // ---------------------------------------- Pre-type inference state ----------------------------------------

    /// <summary>
    /// Solves or simplifies as many type constraints as possible.
    /// If "allowDecisions" is "false", then no decisions, only determined inferences, are made; this mode is
    /// appropriate for the partial solving that's done before a member lookup.
    /// Returns "true" if anything changed (that is, if any of the constraints in the type-inference state
    /// caused a change some pre-type proxy).
    /// </summary>
    void PartiallySolveTypeConstraints(string printableContext = null, bool makeDecisions = false) {
      if (printableContext != null) {
        PrintTypeInferenceState("(partial) " + printableContext);
      }
      bool anythingChanged;
      do {
        anythingChanged = false;
        anythingChanged |= ApplySubtypeConstraints();
        anythingChanged |= ApplyEqualityConstraints();
        anythingChanged |= ApplyGuardedConstraints();
        if (makeDecisions) {
          if (DecideHeadsFromBounds(true)) {
            anythingChanged = true;
          } else if (DecideHeadsFromBounds(false)) {
            anythingChanged = true;
          }
        }
      } while (anythingChanged);
    }

    void SolveAllTypeConstraints(string printableContext) {
      PrintTypeInferenceState(printableContext);
      PartiallySolveTypeConstraints(null);

      PartiallySolveTypeConstraints(null, true);

      if (ApplyDefaultAdvice()) {
        PartiallySolveTypeConstraints(null, true);
      }

      PrintLegend();
      ConfirmTypeConstraints();
      ClearState();
    }

    void ClearState() {
      unnormalizedSubtypeConstraints.Clear();
      guardedConstraints.Clear();
      defaultAdvice.Clear();
      confirmations.Clear();
      allPreTypeProxies.Clear();
    }

    public void PrintTypeInferenceState(string/*?*/ header = null) {
      if (!resolver.Options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      Console.WriteLine("*** Type inference state ***{0}", header == null ? "" : $" {header} ");
      PrintList("Subtype constraints", unnormalizedSubtypeConstraints, stc => {
        return $"{stc.Super} :> {stc.Sub}";
      });
      PrintList("Equality constraints", equalityConstraints, eqc => {
        return $"{eqc.A} == {eqc.B}";
      });
#if IS_THERE_A_GOOD_WAY_TO_PRINT_GUARDED_CONSTRAINTS
      PrintList("Guarded constraints", guardedConstraints, gc => {
        return gc.Kind + Util.Comma("", gc.Arguments, arg => $" {arg}");
      });
#endif
      PrintList("Default-type advice", defaultAdvice, advice => {
        return $"{advice.PreType} ~-~-> {advice.WhatString}";
      });
#if IS_THERE_A_GOOD_WAY_TO_PRINT_CONFIRMATIONS
      PrintList("Post-inference confirmations", confirmations, c => {
        return $"{TokToShortLocation(c.tok)}: {c.Check} {c.PreType}: {c.ErrorMessage()}";
      });
#endif
    }

    void PrintLegend() {
      PrintList("Legend", allPreTypeProxies, pair => {
        var s = Pad($"?{pair.Item1.UniqueId}", 4) + pair.Item1;
        return pair.Item2 == null ? s : $"{Pad(s, 20)}  {pair.Item2}";
      });
    }

    public static string TokToShortLocation(IToken tok) {
      return $"{System.IO.Path.GetFileName(tok.filename)}({tok.line},{tok.col - 1})";
    }

    void PrintList<T>(string rubric, List<T> list, Func<T, string> formatter) {
      if (!resolver.Options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      Console.WriteLine($"    {rubric}:");
      foreach (var t in list) {
        var info = $"        {formatter(t)}";
        if (t is PreTypeStateWithErrorMessage preTypeStateWithErrorMessage) {
          info = $"{Pad(info, 30)}  {TokToShortLocation(preTypeStateWithErrorMessage.tok)}: {preTypeStateWithErrorMessage.ErrorMessage()}";
        }
        Console.WriteLine(info);
      }
    }

    string Pad(string s, int minWidth) {
      Contract.Requires(s != null);
      return s + new string(' ', Math.Max(minWidth - s.Length, 0));
    }

    void DebugPrint(string format, params object[] args) {
      if (resolver.Options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        Console.WriteLine(format, args);
      }
    }

    // ---------------------------------------- Equality constraints ----------------------------------------

    private class EqualityConstraint : PreTypeStateWithErrorMessage {
      public PreType A;
      public PreType B;

      public EqualityConstraint(PreType a, PreType b, IToken tok, string msgFormat)
        : base(tok, msgFormat) {
        A = a;
        B = b;
      }

      public override string ErrorMessage() {
        return string.Format(ErrorFormatString, A, B);
      }
    }

    private List<EqualityConstraint> equalityConstraints = new();

    void AddEqualityConstraint(PreType a, PreType b, IToken tok, string msgFormat) {
      equalityConstraints.Add(new EqualityConstraint(a, b, tok, msgFormat));
    }

    private bool ApplyEqualityConstraints() {
      if (equalityConstraints.Count == 0) {
        return false;
      }
      var constraints = equalityConstraints;
      equalityConstraints = new();
      foreach (var constraint in constraints) {
        ApplyEqualityConstraint(constraint.A, constraint.B, constraint.tok, constraint.ErrorFormatString);
      }
      return true;
    }

    /// <summary>
    /// Constrain "a" to be the same type as "b".
    /// This method can only be called when "unnormalizedSubtypeConstraints" is in a stable state. That means,
    /// in particular, that this method cannot be called in middle of ApplySubtypeConstraints.
    /// </summary>
    private void ApplyEqualityConstraint(PreType a, PreType b, IToken tok, string msgFormat) {
      a = a.Normalize();
      b = b.Normalize();
      if (a == b) {
        // we're already there
      } else if (a is PreTypeProxy pa && !Occurs(pa, b)) {
        pa.Set(b);
      } else if (b is PreTypeProxy pb && !Occurs(pb, a)) {
        pb.Set(a);
      } else if (a is DPreType da && b is DPreType db && da.Decl == db.Decl) {
        Contract.Assert(da.Arguments.Count == db.Arguments.Count);
        for (var i = 0; i < da.Arguments.Count; i++) {
          // TODO: should the error message in the following line be more specific?
          AddEqualityConstraint(da.Arguments[i], db.Arguments[i], tok, msgFormat);
        }
      } else {
        ReportError(tok, msgFormat, a, b);
      }
    }

    /// <summary>
    /// Returns "true" if "proxy" is among the free variables of "t".
    /// "proxy" is expected to be normalized.
    /// </summary>
    private bool Occurs(PreTypeProxy proxy, PreType t) {
      Contract.Requires(t != null);
      Contract.Requires(proxy != null);
      return Reaches(t, proxy, 1, new HashSet<PreTypeProxy>());
    }

    int _reaches_recursion;
    private bool Reaches(PreType t, PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited) {
      if (_reaches_recursion == 20) {
        Contract.Assume(false);  // possible infinite recursion
      }
      _reaches_recursion++;
      var b = Reaches_aux(t, proxy, direction, visited);
      _reaches_recursion--;
      return b;
    }
    private bool Reaches_aux(PreType t, PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited) {
      Contract.Requires(t != null);
      Contract.Requires(proxy != null);
      Contract.Requires(visited != null);
      t = t.Normalize();
      var tproxy = t as PreTypeProxy;
      if (tproxy == null) {
        var dp = (DPreType)t;
        var polarities = dp.Decl.TypeArgs.ConvertAll(tp => TypeParameter.Direction(tp.Variance));
        Contract.Assert(polarities != null);
        Contract.Assert(polarities.Count <= dp.Arguments.Count);
        for (int i = 0; i < polarities.Count; i++) {
          if (Reaches(dp.Arguments[i], proxy, direction * polarities[i], visited)) {
            return true;
          }
        }
        return false;
      } else if (tproxy == proxy) {
        return true;
      } else if (visited.Contains(tproxy)) {
        return false;
      } else {
        visited.Add(tproxy);
        return DirectionalBounds(tproxy, direction).Any(su => Reaches(su, proxy, direction, visited));
      }
    }

    // ---------------------------------------- Comparable constraints ----------------------------------------

    void AddComparableConstraint(PreType a, PreType b, IToken tok, string errorFormatString) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      AddGuardedConstraint(() => ApplyComparableConstraints(a, b, tok, errorFormatString));
    }

    bool ApplyComparableConstraints(PreType a, PreType b, IToken tok, string errorFormatString) {
      // The meaning of a comparable constraint
      //     A ~~ B
      // is the disjunction
      //     A :> B    or    B :> A
      // To decide between these two possibilities, enough information must be available about A and/or B.
      var ptA = a.Normalize() as DPreType;
      var ptB = b.Normalize() as DPreType;
      if (ptA != null && ptB != null &&
          AdaptTypeArgumentsForParent(ptB.Decl, ptA.Decl, ptA.Arguments) == null &&
          AdaptTypeArgumentsForParent(ptA.Decl, ptB.Decl, ptB.Arguments) == null) {
        // neither A :> B nor B :> A is possible
        ReportError(tok, errorFormatString, a, b);
        return true;
      } else if ((ptA != null && ptA.IsLeafType()) || (ptB != null && ptB.IsRootType())) {
        // use B :> A
        DebugPrint($"    DEBUG: turning ~~ into {b} :> {a}");
        AddSubtypeConstraint(b, a, tok, errorFormatString);
        return true;
      } else if ((ptA != null && ptA.IsRootType()) || (ptB != null && ptB.IsLeafType())) {
        // use A :> B
        DebugPrint($"    DEBUG: turning ~~ into {a} :> {b}");
        AddSubtypeConstraint(a, b, tok, errorFormatString);
        return true;
      } else {
        // not enough information to determine
        return false;
      }
    }

    // ---------------------------------------- State with error message ----------------------------------------

    abstract class PreTypeStateWithErrorMessage {
      public readonly IToken tok;
      // exactly one of "errorFormatString" and "errorFormatStringProducer" is non-null
      private readonly string errorFormatString;
      private readonly Func<string> errorFormatStringProducer;

      public string ErrorFormatString => errorFormatString ?? errorFormatStringProducer();

      public abstract string ErrorMessage();

      public PreTypeStateWithErrorMessage(IToken tok, string errorFormatString) {
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatString != null);
        this.tok = tok;
        this.errorFormatString = errorFormatString;
      }

      public PreTypeStateWithErrorMessage(IToken tok, Func<string> errorFormatStringProducer) {
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatStringProducer != null);
        this.tok = tok;
        this.errorFormatStringProducer = errorFormatStringProducer;
      }
    }

    // ---------------------------------------- Subtype constraints ----------------------------------------

    class SubtypeConstraint : PreTypeStateWithErrorMessage {
      public readonly PreType Super;
      public readonly PreType Sub;

      public override string ErrorMessage() {
        return string.Format(ErrorFormatString, Super, Sub);
      }

      public SubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString)
        : base(tok, errorFormatString) {
        Contract.Requires(super != null);
        Contract.Requires(sub != null);
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatString != null);
#if DEBUG
        Contract.Assert(super != null);
        Contract.Assert(sub != null);
#endif
        Super = super.Normalize();
        Sub = sub.Normalize();
      }

      public SubtypeConstraint(PreType super, PreType sub, IToken tok, Func<string> errorFormatStringProducer)
        : base(tok, errorFormatStringProducer) {
        Contract.Requires(super != null);
        Contract.Requires(sub != null);
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatStringProducer != null);
#if DEBUG
        Contract.Assert(super != null);
        Contract.Assert(sub != null);
#endif
        Super = super.Normalize();
        Sub = sub.Normalize();
      }

      public SubtypeConstraint Normalize() {
        var super = Super.Normalize();
        var sub = Sub.Normalize();
        if (object.ReferenceEquals(super, Super) && object.ReferenceEquals(sub, Sub)) {
          return this;
        } else {
          return new SubtypeConstraint(super, sub, Token.NoToken, ErrorFormatString);
        }
      }
    }

    private List<SubtypeConstraint> unnormalizedSubtypeConstraints = new();

    void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatString));
    }

    void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, Func<string> errorFormatStringProducer) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatStringProducer != null);
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
        var used = false;
        var super = constraint.Super.Normalize();
        var sub = constraint.Sub.Normalize();
        var ptSuper = super as DPreType;
        var ptSub = sub as DPreType;
        // In the following explanations, D is assumed to be a type with three
        // type parameters, being co-variant, contra-variant, and non-variant, respectively.
        if (ptSuper != null && ptSub != null) {
          // We're looking at D<a,b,c> :> E<x,y>
          // If E<x,y> can be rewritten as D<f(x,y), g(x,y), h(x,y)>, then
          //     Constrain a :> f(x,y)
          //     Constrain g(x,y) :> b
          //     Constrain c == h(x,y)
          // else report an error
          var arguments = AdaptTypeArgumentsForParent(ptSuper.Decl, ptSub.Decl, ptSub.Arguments);
          if (arguments != null) {
            Contract.Assert(arguments.Count == ptSuper.Decl.TypeArgs.Count);
            ConstrainTypeArguments(ptSuper.Decl.TypeArgs, ptSuper.Arguments, arguments, constraint.tok);
            used = true;
          } else {
            ReportError(constraint.tok, constraint.ErrorMessage());
            used = true;
          }
        } else if (ptSuper != null) {
          // We're looking at D<a,b,c> :> sub
          // If the head of D has no proper subtypes (i.e., it is not a trait), then
          //     Introduce alpha, beta
          //     Constrain sub == D<alpha, beta, c>
          //     Constrain a :> alpha
          //     Constrain beta :> b
          // else do nothing for now
          if (!(ptSuper.Decl is TraitDecl)) {
            var arguments = CreateProxiesForTypesAccordingToVariance(constraint.tok, ptSuper.Decl.TypeArgs, ptSuper.Arguments, false);
            var pt = new DPreType(ptSuper.Decl, arguments);
            AddEqualityConstraint(sub, pt, constraint.tok, constraint.ErrorFormatString);
            used = true;
          }
        } else if (ptSub != null) {
          // We're looking at super :> D<a,b,c>
          // If the head of D has no proper supertypes (i.e., D has no parent traits), then
          //     Introduce alpha, beta
          //     Constrain super == D<alpha, beta, c>
          //     Constrain alpha :> a
          //     Constrain b :> beta
          // else do nothing for now
          if (HasTraitSupertypes(ptSub)) {
            // there are parent traits
          } else {
            var arguments = CreateProxiesForTypesAccordingToVariance(constraint.tok, ptSub.Decl.TypeArgs, ptSub.Arguments, true);
            var pt = new DPreType(ptSub.Decl, arguments);
            AddEqualityConstraint(super, pt, constraint.tok, constraint.ErrorFormatString);
            used = true;
          }
        } else {
          // do nothing for now
        }
        if (used) {
          anythingChanged = true;
        } else {
          unnormalizedSubtypeConstraints.Add(constraint.Normalize());
        }
      }
      return anythingChanged;
    }

    /// <summary>
    /// If "super" is an ancestor of "sub", then return a list "L" of arguments for "super" such that
    /// "super<L>" is a supertype of "sub<subArguments>".
    /// Otherwise, return "null".
    /// </summary>
    List<PreType> /*?*/ AdaptTypeArgumentsForParent(TopLevelDecl super, TopLevelDecl sub, List<PreType> subArguments) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      Contract.Requires(subArguments != null);
      Contract.Requires(sub.TypeArgs.Count == subArguments.Count);

      if (super == sub) {
        return subArguments;
      } else if (sub is TopLevelDeclWithMembers md) {
        var subst = PreType.PreTypeSubstMap(md.TypeArgs, subArguments);
        foreach (var parentType in AllParentTraits(md)) {
          var parentPreType = (DPreType)Type2PreType(parentType).Substitute(subst);
          var arguments = AdaptTypeArgumentsForParent(super, parentPreType.Decl, parentPreType.Arguments);
          if (arguments != null) {
            return arguments;
          }
        }
      }
      return null;
    }

    /// <summary>
    /// For the given arguments: [a0, a1, a2, ...]
    /// use the variance given by parameters: [p0, p1, p2, ...]
    /// to return a list: [t0, t1, t2, ...]
    /// where for each i,
    ///   - if pi is Non, then ai
    ///   - else if (pi is Co) == proxiesAreSupertypes, then a new proxy constrained by:  proxy :> ai
    ///   - else a new proxy constrained by:  ai :> proxy
    /// </summary>
    List<PreType> CreateProxiesForTypesAccordingToVariance(IToken tok, List<TypeParameter> parameters, List<PreType> arguments, bool proxiesAreSupertypes) {
      Contract.Requires(tok != null);
      Contract.Requires(parameters != null);
      Contract.Requires(arguments != null);
      Contract.Requires(parameters.Count == arguments.Count);

      if (parameters.All(tp => tp.Variance == TypeParameter.TPVariance.Non)) {
        // special case this common situation
        return arguments;
      }
      var newArgs = new List<PreType>();
      for (var i = 0; i < parameters.Count; i++) {
        var tp = parameters[i];
        if (tp.Variance == TypeParameter.TPVariance.Non) {
          newArgs.Add(arguments[i]);
        } else {
          var co = tp.Variance == TypeParameter.TPVariance.Co ? "co" : "contra";
          var proxy = CreatePreTypeProxy($"type used in {co}variance constraint");
          newArgs.Add(proxy);
          if ((tp.Variance == TypeParameter.TPVariance.Co) == proxiesAreSupertypes) {
            AddSubtypeConstraint(proxy, arguments[i], tok, "bad"); // TODO: improve error message
          } else {
            AddSubtypeConstraint(arguments[i], proxy, tok, "bad"); // TODO: improve error message
          }
        }
      }
      return newArgs;
    }

    /// <summary>
    /// For every non-variant parameters[i], constrain superArguments[i] == subArguments[i].
    /// For every co-variant parameters[i], constrain superArguments[i] :> subArguments[i].
    /// For every contra-variant parameters[i], constrain subArguments[i] :> superArguments[i].
    /// </summary>
    void ConstrainTypeArguments(List<TypeParameter> parameters, List<PreType> superArguments, List<PreType> subArguments, IToken tok) {
      Contract.Requires(parameters != null);
      Contract.Requires(superArguments != null);
      Contract.Requires(subArguments != null);
      Contract.Requires(parameters.Count == superArguments.Count && superArguments.Count == subArguments.Count);
      Contract.Requires(tok != null);

      for (var i = 0; i < parameters.Count; i++) {
        var tp = parameters[i];
        var arg0 = superArguments[i];
        var arg1 = subArguments[i];
        if (tp.Variance == TypeParameter.TPVariance.Non) {
          AddEqualityConstraint(arg0, arg1, tok, "non-variance would require {0} == {1}");
        } else if (tp.Variance == TypeParameter.TPVariance.Co) {
          AddSubtypeConstraint(arg0, arg1, tok, "covariance would require {0} :> {1}");
        } else {
          AddSubtypeConstraint(arg1, arg0, tok, "contravariance would require {0} :> {1}");
        }
      }
    }

    bool DecideHeadsFromBounds(bool fromSubBounds) {
      // For each proxy, compute the join/meet of its sub/super-bound heads
      Dictionary<PreTypeProxy, TopLevelDecl> candidateHeads = new();
      Dictionary<PreTypeProxy, SubtypeConstraint> constraintOrigins = new();
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        var proxy = (fromSubBounds ? constraint.Super : constraint.Sub).Normalize() as PreTypeProxy;
        var bound = (fromSubBounds ? constraint.Sub : constraint.Super).Normalize() as DPreType;
        if (proxy != null && bound != null) {
          if (!candidateHeads.TryGetValue(proxy, out var previousBest)) {
            candidateHeads.Add(proxy, bound.Decl);
            constraintOrigins.Add(proxy, constraint);
          } else {
            var combined = fromSubBounds ? JoinHeads(previousBest, bound.Decl) : MeetHeads(previousBest, bound.Decl);
            if (combined == null) {
              // the two joins/meets were in conflict with each other; ignore the new one
            } else {
              candidateHeads[proxy] = combined;
            }
          }
        }
      }
      var anythingChanged = false;
      foreach (var (proxy, best) in candidateHeads) {
        var pt = new DPreType(best, best.TypeArgs.ConvertAll(_ => CreatePreTypeProxy()));
        var constraint = constraintOrigins[proxy];
        DebugPrint($"    DEBUG: head decision {proxy} := {pt}");
        AddEqualityConstraint(proxy, pt, constraint.tok, constraint.ErrorFormatString); // TODO: the message could be made more specific now (perhaps)
        anythingChanged = true;
      }
      return anythingChanged;
    }

    TopLevelDecl/*?*/ JoinHeads(TopLevelDecl a, TopLevelDecl b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      var aAncestors = new HashSet<TopLevelDecl>();
      var bAncestors = new HashSet<TopLevelDecl>();
      ComputeAncestors(a, aAncestors);
      ComputeAncestors(b, bAncestors);
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
      Contract.Requires(a != null);
      Contract.Requires(b != null);
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

    IEnumerable<DPreType> AllSubBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (!visited.Contains(proxy)) {
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
    }

    IEnumerable<DPreType> AllSuperBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (!visited.Contains(proxy)) {
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
    }


    IEnumerable<PreType> DirectionalBounds(PreTypeProxy tproxy, int direction) {
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        if (0 <= direction && constraint.Super.Normalize() == tproxy) {
          yield return constraint.Sub;
        }
        if (direction <= 0 && constraint.Sub.Normalize() == tproxy) {
          yield return constraint.Super;
        }
      }
    }

    // ---------------------------------------- Guarded constraints ----------------------------------------

    private List<Func<bool>> guardedConstraints = new();

    void AddGuardedConstraint(Func<bool> predicate) {
      Contract.Requires(predicate != null);
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

    // ---------------------------------------- Advice ----------------------------------------

    class Advice {
      public readonly PreType PreType;
      public readonly AdviceTarget What;

      public string WhatString => What == AdviceTarget.Object ? "object?" : What.ToString().ToLower();

      public Advice(PreType preType, AdviceTarget advice) {
        PreType = preType;
        What = advice;
      }
    }

    enum AdviceTarget {
      Bool, Char, Int, Real, String, Object
    }

    private List<Advice> defaultAdvice = new();

    void AddDefaultAdvice(PreType preType, AdviceTarget advice) {
      Contract.Requires(preType != null);
      defaultAdvice.Add(new Advice(preType, advice));
    }

    bool ApplyDefaultAdvice() {
      bool anythingChanged = false;
      foreach (var advice in defaultAdvice) {
        var preType = advice.PreType.Normalize();
        if (preType is PreTypeProxy proxy) {
          DebugPrint($"    DEBUG: acting on advice, setting {proxy} := {advice.WhatString}");

          Type StringDecl() {
            var s = resolver.moduleInfo.TopLevels["string"];
            return new UserDefinedType(s.tok, s.Name, s, new List<Type>());
          }

          var target = advice.What switch {
            AdviceTarget.Bool => Type2PreType(Type.Bool),
            AdviceTarget.Char => Type2PreType(Type.Char),
            AdviceTarget.Int => Type2PreType(Type.Int),
            AdviceTarget.Real => Type2PreType(Type.Real),
            AdviceTarget.String => Type2PreType(StringDecl()),
            AdviceTarget.Object => Type2PreType(resolver.builtIns.ObjectQ())
          };
          proxy.Set(target);
          anythingChanged = true;
        }
      }
      return anythingChanged;
    }

    // ---------------------------------------- Post-inference confirmations ----------------------------------------

    private List<System.Action> confirmations = new();

    void AddConfirmation(string check, PreType preType, IToken tok, string errorFormatString) {
      Contract.Requires(check != null);
      Contract.Requires(preType != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      confirmations.Add(() => {
        if (!ConfirmConstraint(check, preType)) {
          ReportError(tok, errorFormatString, preType);
        }
      });
    }

    void AddConfirmation(System.Action confirm) {
      confirmations.Add(confirm);
    }

    void ConfirmTypeConstraints() {
      foreach (var c in confirmations) {
        c();
      }
    }

    private bool ConfirmConstraint(string check, PreType preType) {
      preType = preType.Normalize();
      if (preType is PreTypeProxy) {
        return false;
      }

      var pt = (DPreType)preType;
      var ancestorPt = NewTypeAncestor(pt);
      var ancestorDecl = ancestorPt.Decl;
      var familyDeclName = ancestorDecl.Name;
      switch (check) {
        case "InIntFamily":
          return familyDeclName == "int";
        case "InRealFamily":
          return familyDeclName == "real";
        case "InBoolFamily":
          return familyDeclName == "bool";
        case "InCharFamily":
          return familyDeclName == "char";
        case "InSeqFamily":
          return familyDeclName == "seq";
        case "IsNullableRefType":
          return DPreType.IsReferenceTypeDecl(pt.Decl);
        case "IsBitvector":
          return IsBitvectorName(familyDeclName);
        case "IntLikeOrBitvector":
          return familyDeclName == "int" || IsBitvectorName(familyDeclName);
        case "NumericOrBitvector":
          return familyDeclName == "int" || familyDeclName == "real" || IsBitvectorName(familyDeclName);
        case "NumericOrBitvectorOrCharOrORDINAL":
          return familyDeclName == "int" || familyDeclName == "real" || IsBitvectorName(familyDeclName) || familyDeclName == "char" ||
                 familyDeclName == "ORDINAL";
        case "BooleanBits":
          return familyDeclName == "bool" || IsBitvectorName(familyDeclName);
        case "IntOrORDINAL":
          return familyDeclName == "int" || familyDeclName == "ORDINAL";
        case "IntOrBitvectorOrORDINAL":
          return familyDeclName == "int" || IsBitvectorName(familyDeclName) || familyDeclName == "ORDINAL";
        case "Plussable":
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
              return IsBitvectorName(familyDeclName);
          }
        case "Mullable":
          switch (familyDeclName) {
            case "int":
            case "real":
            case "set":
            case "iset":
            case "multiset":
              return true;
            default:
              return IsBitvectorName(familyDeclName);
          }
        case "Disjointable":
          return familyDeclName == "set" || familyDeclName == "iset" || familyDeclName == "multiset";
        case "Orderable_Lt":
        case "Orderable_Gt":
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
              return check == "Orderable_Lt";
            default:
              return IsBitvectorName(familyDeclName);
          }
        case "RankOrderable":
          return ancestorDecl is IndDatatypeDecl;
        case "RankOrderableOrTypeParameter":
          return ancestorDecl is IndDatatypeDecl || ancestorDecl is TypeParameter;
        case "Sizeable":
          switch (familyDeclName) {
            case "set": // but not "iset"
            case "multiset":
            case "seq":
            case "map": // but not "imap"
              return true;
            default:
              return false;
          }
        case "Freshable":
        {
          var t = familyDeclName == "set" || familyDeclName == "iset" || familyDeclName == "seq"
            ? ancestorPt.Arguments[0].Normalize() as DPreType
            : ancestorPt;
          return t != null && DPreType.IsReferenceTypeDecl(t.Decl);
        }

        default:
          Contract.Assert(false); // unexpected case
          throw new cce.UnreachableException();
      }
    }
  }
}