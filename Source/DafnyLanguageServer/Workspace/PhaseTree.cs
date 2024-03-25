using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class PhaseTree {
  public IPhase Phase { get; }
  public IReadOnlyList<FileDiagnostic> Diagnostics;

  public IEnumerable<FileDiagnostic> AllDiagnostics {
    get {
      return Diagnostics.Concat(Children.SelectMany(c => c.AllDiagnostics));
    }
  }

  public PhaseTree Add(IPhase phase, IReadOnlyList<FileDiagnostic> diagnostics) {
    var ancestors = phase.AncestorsAndSelf;

    return Recursive(this, ancestors)!;
    PhaseTree Recursive(PhaseTree tree, Cons<IPhase> phases) {
      if (phases.Head == tree.Phase) {
        return new PhaseTree(tree.Phase, tree.Diagnostics.Concat(diagnostics));
      }
      if (phases.Tail is Cons<IPhase> cons) {

        return new PhaseTree(tree.Phase, tree.Diagnostics,
          tree.Children.Select(c => Recursive(c, cons)).ToImmutableList());
      }

      return new PhaseTree(phases.Head, diagnostics);
    }
  }

  public PhaseTree Remove(IPhase phase) {
    var ancestors = phase.AncestorsAndSelf;

    return Recursive(this, ancestors)!;
    PhaseTree? Recursive(PhaseTree tree, SinglyLinkedList<IPhase> phases) {
      if (phases is Cons<IPhase> cons) {
        if (cons.Head == tree.Phase) {
          return null;
        }

        return new PhaseTree(tree.Phase, tree.Diagnostics,
          tree.Children.Select(c => Recursive(c, cons.Tail)).Where(t => t != null).ToImmutableList()!);
      }

      return tree;
    }
  }

  record EmptyPhase : IPhase {
    public IPhase? MaybeParent => null;
  }
  public static PhaseTree Empty() {
    return new PhaseTree(new EmptyPhase(), ImmutableArray<FileDiagnostic>.Empty);
  }

  public PhaseTree(IPhase phase, IReadOnlyList<FileDiagnostic> diagnostics) {
    Diagnostics = diagnostics;
    Phase = phase;
    Children = ImmutableList<PhaseTree>.Empty;
  }

  public PhaseTree(IPhase phase, IReadOnlyList<FileDiagnostic> diagnostics, ImmutableList<PhaseTree> children) {
    Phase = phase;
    Diagnostics = diagnostics;
    Children = children;
  }

  public ImmutableList<PhaseTree> Children;
}