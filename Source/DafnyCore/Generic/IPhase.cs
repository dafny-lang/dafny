#nullable enable
namespace Microsoft.Dafny;

/// <summary>
/// A phase of compilation
/// 
/// A phases can have a parent, and so phases form a tree.
///
/// The children of a phase, are the phases that are discovered and completed as part of that parent.
/// </summary>
public interface IPhase {
  public Cons<IPhase> AncestorsAndSelf {
    get {
      Cons<IPhase> result = new Cons<IPhase>(this, new Nil<IPhase>());
      while (result.Head.MaybeParent != null) {
        result = new Cons<IPhase>(result.Head.MaybeParent, result);
      }

      return result;
    }
  }

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

public record MessageSourceBasedPhase(MessageSource MessageSource) : IPhase {
  public IPhase? MaybeParent => null;
}

public record PhaseFromObject(object Owner, IPhase? MaybeParent) : IPhase;

public record VerificationOfSymbol(ICanVerify CanVerify) : IPhase {
  public IPhase? MaybeParent => new MessageSourceBasedPhase(MessageSource.Verifier);
}