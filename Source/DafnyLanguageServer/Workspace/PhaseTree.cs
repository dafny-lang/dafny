using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// A tree where each node except the root corresponds to a phase in the verification and compilation process.
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

  public PhaseTree UpdateState(Func<FileDiagnostic, FileDiagnostic?> updateDiagnostic) {
    return new PhaseTree(Diagnostics.Select(updateDiagnostic).OfType<FileDiagnostic>().ToList(),
      Children.ToImmutableDictionary(kv => kv.Key, kv => kv.Value.UpdateState(updateDiagnostic)));
  }


  public PhaseTree Merge(PhaseTree source, Func<FileDiagnostic, FileDiagnostic?> updateDiagnostic) {
    var newChildren = source.Children.Aggregate(Children,
      (newChildren, kv) => {
        if (kv.Key == IdeState.InternalExceptions.Instance) {
          return newChildren;
        }

        if (newChildren.TryGetValue(kv.Key, out var existingChild)) {
          return newChildren.SetItem(kv.Key, existingChild.Merge(kv.Value, updateDiagnostic));
        }

        return newChildren.SetItem(kv.Key, kv.Value.UpdateState(updateDiagnostic));
      });
    return new PhaseTree(Diagnostics.Concat(source.Diagnostics.Select(updateDiagnostic).OfType<FileDiagnostic>()).ToList(), newChildren);
  }

  public PhaseTree Add(IPhase phase, IReadOnlyList<FileDiagnostic> newDiagnostics) {
    var ancestors = phase.AncestorsAndSelf();

    return Recursive(this, ancestors);
    PhaseTree Recursive(PhaseTree tree, SinglyLinkedList<IPhase> phases) {
      if (phases is Cons<IPhase> cons) {
        if (!tree.Children.TryGetValue(cons.Head, out var child)) {
          // An ancestor was not added yet.
          child = new PhaseTree(ImmutableList<FileDiagnostic>.Empty);
        }

        var newChild = Recursive(child, cons.Tail);
        return new PhaseTree(tree.Diagnostics, tree.Children.SetItem(cons.Head, newChild));
      }

      return new PhaseTree(tree.Diagnostics.Concat(newDiagnostics), tree.Children);
    }
  }

  public PhaseTree ClearDiagnosticsAndPruneChildren(IPhase phase, IReadOnlyList<IPhase> newChildren) {
    var ancestors = phase.AncestorsAndSelf();

    return Recursive(this, ancestors)!;
    PhaseTree Recursive(PhaseTree tree, SinglyLinkedList<IPhase> phases) {
      if (phases is Cons<IPhase> cons) {
        if (tree.Children.TryGetValue(cons.Head, out var child)) {
          var recursiveResult = Recursive(child, cons.Tail);
          if (recursiveResult == child) {
            // Nothing changed
            return tree;
          }
          return new PhaseTree(tree.Diagnostics, tree.Children.SetItem(cons.Head, recursiveResult));
        }

        // Could not find phase to change. Returning the same tree.
        return tree;
      }

      // Found phase to set children for.
      var remainingChildren = tree.Children;
      var childrenToRemove = tree.Children.Keys.Except(newChildren);
      foreach (var childToRemove in childrenToRemove) {
        remainingChildren = remainingChildren.Remove(childToRemove);
      }

      if (remainingChildren == tree.Children) {
        return tree;
      }

      return new PhaseTree(Array.Empty<FileDiagnostic>(), remainingChildren);
    }
  }

  public PhaseTree Remove(IPhase phase) {
    var ancestors = phase.AncestorsAndSelf();

    return Recursive(this, ancestors)!;
    static PhaseTree? Recursive(PhaseTree tree, SinglyLinkedList<IPhase> phases) {
      if (phases is Cons<IPhase> cons) {
        if (tree.Children.TryGetValue(cons.Head, out var child)) {
          var recursiveResult = Recursive(child, cons.Tail);
          if (recursiveResult == child) {
            // Nothing changed
            return tree;
          }
          return recursiveResult == null
            ? new PhaseTree(tree.Diagnostics, tree.Children.Remove(cons.Head))
            : new PhaseTree(tree.Diagnostics, tree.Children.SetItem(cons.Head, recursiveResult));
        }

        // Could not find phase to remove. Returning the same tree.
        return tree;
      }

      // Found phase to remove.
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