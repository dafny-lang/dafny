namespace CompilerBuilder;

interface ParseResult;

interface ParseResult<T> : ParseResult {
  ParseResult<TU> Continue<TU>(Func<ConcreteSuccess<T>, ParseResult<TU>> f);

  ConcreteSuccess<T>? Success { get; }
  FailureR<T>? Failure { get; }
  IEnumerable<IFoundRecursion<T>> Recursions { get; }
  
  ParseResult<T> Combine(ParseResult<T> other) {
    ConcreteSuccess<T>? concreteSuccess = null;
    if (Success != null && other.Success != null) {
      concreteSuccess = Success.Remainder.Offset > other.Success.Remainder.Offset ? Success : other.Success;
    }

    concreteSuccess ??= Success ?? other.Success;
    var recursions = Recursions.Concat(other.Recursions);

    ConcreteResult<T>? concreteResult = concreteSuccess;
    if (concreteResult != null) {
      if (Failure != null && other.Failure != null) {
        concreteResult = Failure.Location.Offset > other.Failure.Location.Offset ? Failure : other.Failure;
      }

      concreteResult ??= Failure ?? other.Failure;
    }

    return new Aggregate<T>(concreteResult, recursions);
  }
  
  internal ParseResult<U> CastFailure<U>() {
    if (this is FailureR<T> failure) {
      return new FailureR<U>(failure.Message, failure.Location);
    }

    throw new InvalidOperationException();
  }
}

// interface SuccessResult<T>(ConcreteSuccess<T>? Concrete, FoundRecursion<T, T>? Recursion) {
//   OneSuccessResult<U> Bind<U>(Func<ConcreteSuccess<T>, OneSuccessResult<U>> f) {
//     
//   }
//
// }

interface ConcreteResult<T> : ParseResult<T> {
  
}
interface SuccessResult<T> : ParseResult<T> {
}

internal record Aggregate<T>(ConcreteResult<T>? Concrete, IEnumerable<IFoundRecursion<T>> Recursions) : SuccessResult<T> {
  public ParseResult<U> Continue<U>(Func<ConcreteSuccess<T>, ParseResult<U>> f) {
    var newRecursions = Recursions.Select(r => (IFoundRecursion<U>)r.Continue(f));
    var noConcrete = new Aggregate<U>(null, newRecursions);
    if (Concrete != null) {
      var concreteResult = Concrete.Continue(f);
      return concreteResult.Combine(noConcrete);
    }

    return noConcrete;
  }

  public ConcreteSuccess<T>? Success => Concrete as ConcreteSuccess<T>;
  public FailureR<T>? Failure => Concrete as FailureR<T>;
}

record ConcreteSuccess<T>(T Value, ITextPointer Remainder) : ConcreteResult<T> {
  public ParseResult<TB> Continue<TB>(Func<ConcreteSuccess<T>, ParseResult<TB>> f) {
    return f(this);
  }

  public ConcreteSuccess<T>? Success => this;
  public FailureR<T>? Failure => null;
  public IEnumerable<IFoundRecursion<T>> Recursions => Enumerable.Empty<IFoundRecursion<T>>();
}

interface IFoundRecursion<T> : ParseResult<T> {
  ParseResult<T> Apply(object value, ITextPointer remainder);
}

record FoundRecursion<TA, TB>(Func<ConcreteSuccess<TA>, ParseResult<TB>> Recursion) : IFoundRecursion<TB> {
  public ParseResult<TC> Continue<TC>(Func<ConcreteSuccess<TB>, ParseResult<TC>> f) {
    return new FoundRecursion<TA, TC>(concrete => {
      var inner = Recursion(concrete);
      if (inner is SuccessResult<TB> innerSuccess) {
        return innerSuccess.Continue(f);
      }

      return inner.CastFailure<TC>();
    });
  }

  public ConcreteSuccess<TB>? Success => null;
  public FailureR<TB>? Failure => null;
  public IEnumerable<IFoundRecursion<TB>> Recursions => new IFoundRecursion<TB>[]{ this };

  public ParseResult<TB> Apply(object value, ITextPointer remainder) {
    return Recursion(new ConcreteSuccess<TA>((TA)value, remainder));
  }
}

record FailureR<T>(string Message, ITextPointer Location) : ConcreteResult<T> {
  public ParseResult<TU> Continue<TU>(Func<ConcreteSuccess<T>, ParseResult<TU>> f) {
    return new FailureR<TU>(Message, Location);
  }

  public ConcreteSuccess<T>? Success => null;
  public FailureR<T> Failure => this;
  
  public IEnumerable<IFoundRecursion<T>> Recursions => [];
}