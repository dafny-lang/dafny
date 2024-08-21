namespace CompilerBuilder;

public interface ParseResult;

public interface ParseResult<T> : ParseResult {
  internal ParseResult<TU> Continue<TU>(Func<ConcreteSuccess<T>, ParseResult<TU>> f);

  internal ConcreteResult<T>? Concrete => Success as ConcreteResult<T> ?? Failure;

  public ConcreteSuccess<T>? Success { get; }
  public ConcreteSuccess<T> ForceSuccess {
    get {
      if (Success != null) {
        return Success;
      }

      throw new InvalidOperationException(Failure!.Message + $", at ({Failure.Location.Line},{Failure.Location.Column})");
    }
  }
  
  public FailureResult<T>? Failure { get; }
  
  internal IFoundRecursion<T>? FoundRecursion { get; }

  R? Combine<R>(R? left, R? right, Func<R, R, R> combine) {
    if (left == null) {
      return right;
    }

    if (right == null) {
      return left;
    }

    return combine(left, right);
  }
  internal ParseResult<T> Combine(ParseResult<T> other) {
    if (this is IFoundRecursion<T> fr && other is IFoundRecursion<T> or) {
      return new FoundRecursion<T, T>(s => fr.Apply(s.Value, s.Remainder).Combine(
        or.Apply(s.Value, s.Remainder)));
    }

    var recursion = Combine(FoundRecursion, other.FoundRecursion, (l, r) => {
      return new FoundRecursion<T, T>(s => l.Apply(s.Value, s.Remainder).Combine(
        r.Apply(s.Value, s.Remainder)));
    });

    var concreteSuccess = Combine(Success, other.Success, (l,r) => 
      l.Remainder.Offset >= r.Remainder.Offset ? l : r);

    var failure = Combine(Failure, other.Failure, (l,r) => 
      l.Location.Offset >= r.Location.Offset ? l : r);

    if (concreteSuccess != null && failure != null && failure.Location.Offset <= concreteSuccess.Remainder.Offset) {
      // TODO consider keeping the failure if it's at the same offset, because it might have been how you wanted to continue
      failure = null;
    }

    return new Aggregate<T>(concreteSuccess, failure, recursion);
  }
}

public interface ConcreteResult<T> : ParseResult<T>;

internal record Aggregate<T>(ConcreteSuccess<T>? Success, FailureResult<T>? Failure, IFoundRecursion<T>? FoundRecursion) : ParseResult<T> {
  public ParseResult<U> Continue<U>(Func<ConcreteSuccess<T>, ParseResult<U>> f) {;
    var newFailure = Failure == null ? null : new FailureResult<U>(Failure.Message, Failure.Location);
    var newRecursion = (IFoundRecursion<U>?)FoundRecursion?.Continue(f);
    var noConcrete = new Aggregate<U>(null, newFailure, newRecursion);
    if (Success != null) {
      var concreteResult = Success.Continue(f);
      return concreteResult.Combine(noConcrete);
    }

    return noConcrete;
  }
}

public record ConcreteSuccess<T>(T Value, ITextPointer Remainder) : ConcreteResult<T> {
  public ParseResult<TB> Continue<TB>(Func<ConcreteSuccess<T>, ParseResult<TB>> f) {
    var result = f(this);
    return result;
  }

  public ConcreteSuccess<T>? Success => this;
  public FailureResult<T>? Failure => null;
  IFoundRecursion<T>? ParseResult<T>.FoundRecursion => null;
}

interface IFoundRecursion<T> : ParseResult<T> {
  ParseResult<T> Apply(object value, ITextPointer remainder);
}

/// <summary>
/// Parsers that do not have recursive children have the same result regardless of whether they're a recursion on the stack.
/// A parser that has a recursive child, will have a different result if that child is already on its stack.
///
/// TODO do a little analysis to see how often a particular parser is in a cache with different seens
/// 
/// </summary>
record FoundRecursion<TA, TB>(Func<ConcreteSuccess<TA>, ParseResult<TB>> Recursion) : IFoundRecursion<TB> {
  public ParseResult<TC> Continue<TC>(Func<ConcreteSuccess<TB>, ParseResult<TC>> f) {
    return new FoundRecursion<TA, TC>(concrete => {
      var inner = Recursion(concrete);
      var continued = inner.Continue(f);
      return continued;
    });
  }

  public ConcreteSuccess<TB>? Success => null;
  public FailureResult<TB>? Failure => null;
  IFoundRecursion<TB>? ParseResult<TB>.FoundRecursion => this;
  public IEnumerable<IFoundRecursion<TB>> Recursions => new IFoundRecursion<TB>[]{ this };

  public ParseResult<TB> Apply(object value, ITextPointer remainder) {
    return Recursion(new ConcreteSuccess<TA>((TA)value, remainder));
  }
}

public record FailureResult<T> : ConcreteResult<T> {
  public FailureResult(string Message, ITextPointer Location) {
    this.Message = Message;
    this.Location = Location;
  }

  public FailureResult<U> Cast<U>() {
    return new FailureResult<U>(Message, Location);
  }

  public ParseResult<TU> Continue<TU>(Func<ConcreteSuccess<T>, ParseResult<TU>> f) {
    return new FailureResult<TU>(Message, Location);
  }

  public ConcreteSuccess<T>? Success => null;
  public FailureResult<T> Failure => this;
  IFoundRecursion<T>? ParseResult<T>.FoundRecursion => null;
  public string Message { get; init; }
  public ITextPointer Location { get; init; }

  public void Deconstruct(out string Message, out ITextPointer Location) {
    Message = this.Message;
    Location = this.Location;
  }
}