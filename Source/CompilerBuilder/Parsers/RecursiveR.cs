using Microsoft.Dafny;

namespace CompilerBuilder;

class RecursiveR<T>(Func<Parser<T>> get) : Parser<T> {
  private Parser<T>? inner;

  public Parser<T> Inner => inner ??= get();
  
  public ParseResult<T> Parse(ITextPointer text) {

    if (text.SeenHere(this)) {
      return new FoundRecursion<T, T>(Util.Identity);
    }
    
    var seedResult = Inner.Parse(text.Add(this));
    if (seedResult.Success == null) {
      return seedResult;
    }

    ParseResult<T> combinedResult = seedResult;
    foreach (var recursion in seedResult.Recursions) {
      var current = seedResult;
      while (current.Success != null) {
        current = recursion.Apply(current.Success.Value!, current.Success.Remainder);
        combinedResult = combinedResult.Combine(current);
      }
    }

    if (combinedResult is Aggregate<T> aggregate) {
      combinedResult = aggregate with { Recursions = aggregate.Recursions.Where(r => r is not FoundRecursion<T,T>) };
    }

    var r = combinedResult.Continue(r => r with { Remainder = r.Remainder.Remove(this) });
    return r;
  }
}