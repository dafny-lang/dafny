using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// A tree where each node except the root corresponds to a phase.
///
/// Each node stores the state for that phase, which right now only is diagnostics
/// </summary>
public class PhaseTree {
  public IReadOnlyList<FileDiagnostic> Diagnostics;

  public IEnumerable<FileDiagnostic> AllDiagnostics {
    get {
      return Diagnostics.Concat(Children.Values.SelectMany(c => c.AllDiagnostics));
    }
  }

  public PhaseTree Merge(PhaseTree source, Func<FileDiagnostic, FileDiagnostic> updateDiagnostic) {
    var newChildren = source.Children.Aggregate(Children,
      (newChildren, kv) => {
        if (kv.Key == IdeState.InternalExceptions.Instance) {
          return newChildren;
        }

        if (newChildren.TryGetValue(kv.Key, out var existingChild)) {
          return newChildren.SetItem(kv.Key, existingChild.Merge(kv.Value, updateDiagnostic));
        } else {
          return newChildren.SetItem(kv.Key, kv.Value);
        }
      });
    return new PhaseTree(Diagnostics.Concat(source.Diagnostics.Select(updateDiagnostic)).ToList(), newChildren);
  }

  public PhaseTree Add(IPhase phase, IReadOnlyList<FileDiagnostic> newDiagnostics) {
    var ancestors = phase.AncestorsAndSelf;

    return Recursive(this, ancestors);
    PhaseTree Recursive(PhaseTree tree, SinglyLinkedList<IPhase> phases) {
      if (phases is Cons<IPhase> cons) {
        if (!tree.Children.TryGetValue(cons.Head, out var child)) {
          child = new PhaseTree(ImmutableList<FileDiagnostic>.Empty);
        }

        var newChild = Recursive(child, cons.Tail);
        return new PhaseTree(tree.Diagnostics, tree.Children.SetItem(cons.Head, newChild));
      }

      return new PhaseTree(tree.Diagnostics.Concat(newDiagnostics), tree.Children);
    }
  }

  public PhaseTree Remove(IPhase phase) {
    var ancestors = phase.AncestorsAndSelf;

    return Recursive(this, ancestors)!;
    PhaseTree? Recursive(PhaseTree tree, SinglyLinkedList<IPhase> phases) {
      if (phases is Cons<IPhase> cons) {
        if (tree.Children.TryGetValue(cons.Head, out var child)) {
          var recursiveResult = Recursive(child, cons.Tail);
          return recursiveResult == null
            ? new PhaseTree(tree.Diagnostics, tree.Children.Remove(cons.Head))
            : new PhaseTree(tree.Diagnostics, tree.Children.SetItem(cons.Head, recursiveResult));
        }

        return tree;
      }

      return null;
    }
  }

  public static PhaseTree Empty() {
    return new PhaseTree(ImmutableArray<FileDiagnostic>.Empty);
  }

  public PhaseTree(IReadOnlyList<FileDiagnostic> diagnostics) {
    Diagnostics = diagnostics;
    Children = ImmutableDictionary<IPhase, PhaseTree>.Empty;
  }

  public PhaseTree(IReadOnlyList<FileDiagnostic> diagnostics, ImmutableDictionary<IPhase, PhaseTree> children) {
    Diagnostics = diagnostics;
    Children = children;
  }

  public ImmutableDictionary<IPhase, PhaseTree> Children;
}