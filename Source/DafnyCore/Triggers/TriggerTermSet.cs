using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.Triggers;

/// <summary>
/// To generate triggers, we collect sets of terms. Each set may become a trigger candidate.
/// </summary>
internal class TriggerTermSet {
  public bool IsRedundant { get; private set; }
  private List<TriggerTerm> Terms { get; set; }

  private ISet<BoundVar> variables;
  private Dictionary<BoundVar, TriggerTerm> termOwningAUniqueVar;
  private Dictionary<TriggerTerm, ISet<BoundVar>> uniqueVarsOwnedByATerm;

  private int Count => Terms.Count;

  private TriggerTermSet() { }

  internal TriggerCandidate ToTriggerCandidate() {
    return new TriggerCandidate(Terms);
  }

  private static IEnumerable<TriggerTermSet> ComputeTriggerCandidatesTerms(SinglyLinkedList<TriggerTerm> source,
    ISet<BoundVar> relevantVariables) {
    return source switch {
      Cons<TriggerTerm> triggerTerms => ComputeTriggerCandidatesTerms(triggerTerms.Tail, relevantVariables).SelectMany(
        child => {
          var newSet = child.CopyWithAdd(triggerTerms.Head, relevantVariables);
          return !newSet.IsRedundant ? [newSet, child] : new[] { child };
        }),
      Nil<TriggerTerm> => new[] { Empty() },
      _ => throw new ArgumentOutOfRangeException(nameof(source))
    };
  }

  internal static IEnumerable<TriggerTermSet> ComputeNonEmptyTriggerCandidatesTerms(SinglyLinkedList<TriggerTerm> source, IEnumerable<BoundVar> relevantVariables) {
    return ComputeTriggerCandidatesTerms(source, new HashSet<BoundVar>(relevantVariables)).Where(subset => subset.Count > 0);
  }

  private static TriggerTermSet Empty() {
    var newSet = new TriggerTermSet {
      IsRedundant = false,
      Terms = [],
      variables = new HashSet<BoundVar>(),
      termOwningAUniqueVar = new Dictionary<BoundVar, TriggerTerm>(),
      uniqueVarsOwnedByATerm = new Dictionary<TriggerTerm, ISet<BoundVar>>()
    };
    return newSet;
  }

  /// <summary>
  /// Simple formulas like [P0(i) && P1(i) && P2(i) && P3(i) && P4(i)] yield very
  /// large numbers of multi-triggers, most of which are useless. As it copies its
  /// argument, this method updates various datastructures that allow it to
  /// efficiently track ownership relations between formulae and bound variables,
  /// and sets the IsRedundant flag of the returned set, allowing the caller to
  /// discard that set of terms, and the ones that would have been built on top of
  /// it, thus ensuring that the only sets of terms produced in the end are sets
  /// of terms in which each element contributes (owns) at least one variable.
  ///
  /// Note that this is trickier than just checking every term for new variables;
  /// indeed, a new term that does bring new variables in can make an existing
  /// term redundant (see redundancy-detection-does-its-job-properly.dfy).
  /// </summary>
  private TriggerTermSet CopyWithAdd(TriggerTerm term, IEnumerable<BoundVar> relevantVariables) {
    var copy = new TriggerTermSet();
    copy.Terms = [.. Terms];
    copy.variables = new HashSet<BoundVar>(variables);
    copy.termOwningAUniqueVar = new Dictionary<BoundVar, TriggerTerm>(termOwningAUniqueVar);
    copy.uniqueVarsOwnedByATerm = new Dictionary<TriggerTerm, ISet<BoundVar>>(uniqueVarsOwnedByATerm);

    copy.Terms.Add(term);

    var varsInNewTerm = new HashSet<BoundVar>(term.BoundVars);
    varsInNewTerm.IntersectWith(relevantVariables);

    var ownedByNewTerm = new HashSet<BoundVar>();

    // Check #0: does this term bring anything new?
    copy.IsRedundant = IsRedundant || varsInNewTerm.All(bv => copy.variables.Contains(bv));
    copy.variables.UnionWith(varsInNewTerm);

    // Check #1: does this term claiming ownership of all its variables cause another term to become useless?
    foreach (var v in varsInNewTerm) {
      if (copy.termOwningAUniqueVar.TryGetValue(v, out var originalOwner)) {
        var alsoOwnedByOriginalOwner = copy.uniqueVarsOwnedByATerm[originalOwner];
        alsoOwnedByOriginalOwner.Remove(v);
        if (!alsoOwnedByOriginalOwner.Any()) {
          copy.IsRedundant = true;
        }
      } else {
        ownedByNewTerm.Add(v);
        copy.termOwningAUniqueVar[v] = term;
      }
    }

    // Actually claim ownership
    copy.uniqueVarsOwnedByATerm[term] = ownedByNewTerm;

    return copy;
  }
}