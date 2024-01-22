using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.Triggers;

internal class SetOfTerms {
  internal bool IsRedundant { get; private set; }
  internal List<TriggerTerm> Terms { get; set; }

  private ISet<BoundVar> variables;
  private Dictionary<BoundVar, TriggerTerm> termOwningAUniqueVar;
  private Dictionary<TriggerTerm, ISet<BoundVar>> uniqueVarsOwnedByATerm;

  public int Count { get { return Terms.Count; } }

  private SetOfTerms() { }

  internal TriggerCandidate ToTriggerCandidate() {
    return new TriggerCandidate(Terms);
  }

  internal static SetOfTerms Empty() {
    var newSet = new SetOfTerms();
    newSet.IsRedundant = false;
    newSet.Terms = new List<TriggerTerm>();
    newSet.variables = new HashSet<BoundVar>();
    newSet.termOwningAUniqueVar = new Dictionary<BoundVar, TriggerTerm>();
    newSet.uniqueVarsOwnedByATerm = new Dictionary<TriggerTerm, ISet<BoundVar>>();
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
  internal SetOfTerms CopyWithAdd(TriggerTerm term, ISet<BoundVar> relevantVariables) {
    var copy = new SetOfTerms();
    copy.Terms = new List<TriggerTerm>(Terms);
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