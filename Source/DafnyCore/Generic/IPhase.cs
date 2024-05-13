#nullable enable
namespace Microsoft.Dafny;


public static class PhaseExtensions {
  public static SinglyLinkedList<IPhase> AncestorsAndSelf(this IPhase? phase) {
    if (phase == null) {
      return new Nil<IPhase>();
    }

    Cons<IPhase> result = new Cons<IPhase>(phase, new Nil<IPhase>());
    while (result.Head.MaybeParent != null) {
      result = new Cons<IPhase>(result.Head.MaybeParent, result);
    }

    return result;
  }

}
/// <summary>
/// A phase of compilation
///
/// The IDE will migrate state from phases of a previous compilation
/// It wants to know when new state for a particular phase is available, so it can swap out the migrated state with the new
/// The IDE also wants to know when a phase from a previous compilation no longer occurs in the new one, so it can remove that state.
///   There is already client side cleanup of diagnostics whose ranges were removed.
/// One could argue that with caching, migration of state is not needed. State migration means we display possibly incorrect results.
///
/// Migration of verification diagnostics has always seemed needed, because of how slow verification is.
/// However, if we do verification caching at the statement level, maybe we do not even need to migrate that.
/// 
/// Phases can have a parent, and so phases form a tree.
///
/// The children of a phase, are the phases that are discovered and completed as part of that parent.
/// </summary>
public interface IPhase {

  IPhase? MaybeParent { get; }
  MessageSource Source {
    get {
      var sourcePhase = this;
      while (sourcePhase != null && sourcePhase is not MessageSourceBasedPhase) {
        sourcePhase = sourcePhase.MaybeParent;
      }

      return (sourcePhase as MessageSourceBasedPhase)?.MessageSource ?? MessageSource.Unknown;
    }
  }
}

public record RootPhase : IPhase {
  public static readonly IPhase Instance = new RootPhase();
  public IPhase? MaybeParent => null;
}

public record MessageSourceBasedPhase(MessageSource MessageSource) : IPhase {
  public IPhase? MaybeParent => RootPhase.Instance;
}

public record PhaseFromObject(object Owner, IPhase? MaybeParent) : IPhase;

public record VerificationOfScope(VerificationOfSymbol Parent, string ScopeId) : IPhase {
  public IPhase? MaybeParent => Parent;
}

public class VerificationOfTask : IPhase {
  private VerificationOfScope Scope;

  public VerificationOfTask(VerificationOfScope scope) {
    Scope = scope;
  }

  public IPhase? MaybeParent => Scope;
}

public record VerificationOfSymbol(ICanVerify CanVerify) : IPhase {
  public IPhase? MaybeParent => new MessageSourceBasedPhase(MessageSource.Verifier);

  public virtual bool Equals(VerificationOfSymbol? other) {
    if (ReferenceEquals(null, other)) {
      return false;
    }

    if (ReferenceEquals(this, other)) {
      return true;
    }

    return CanVerify.FullDafnyName.Equals(other.CanVerify.FullDafnyName);
  }

  public override int GetHashCode() {
    return CanVerify.FullDafnyName.GetHashCode();
  }
}