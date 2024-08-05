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
      if (recursion is not FoundRecursion<T, T>) {
        // TODO figure out why this is necessary
        continue;
      }

      // after a few iterations a binaryExpr 3 / x, is built
      // now the binaryExpr itself is available as a seed,
      // And the FoundRecursion that built it still holds a pionter to the BinaryExpr that was used to construct the initial one.
      // Constructors should be on the right of self expressions
      var current = seedResult;
      while (current.Success != null) {
        current = recursion.Apply(current.Success.Value!, current.Success.Remainder);
        combinedResult = combinedResult.Combine(current);
      }
    }

    if (combinedResult is Aggregate<T> aggregate) {
      combinedResult = aggregate with { Recursions = aggregate.Recursions.Where(r => r is not FoundRecursion<T,T>) };
    }

    return combinedResult.Continue(r1 => r1 with { Remainder = r1.Remainder.Remove(this) });
  }
}