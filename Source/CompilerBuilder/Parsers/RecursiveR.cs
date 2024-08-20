using Microsoft.Dafny;

namespace CompilerBuilder;

class RecursiveR<T>(Func<Parser<T>> get, string debugName) : Parser<T> {
  private readonly string debugName = debugName;
  private Parser<T>? inner;

  public Parser<T> Inner => inner ??= get();
  
  public override ParseResult<T> Parse(ITextPointer text) {

    if (text.SeenHere(this)) {
      return new FoundRecursion<T, T>(this, Util.Identity);
    }
    
    // TODO caching here seems pointless
    var seedResult = text.Add(this).ParseWithCache2(Inner);
    if (seedResult.Success == null) {
      return seedResult;
    }

    ParseResult<T> combinedResult = seedResult;
    ConcreteSuccess<T>? bestSuccess = seedResult.Success;
    var change = true;
    var myRecursions = new List<IFoundRecursion<T>>();
    var otherRecursions = new List<IFoundRecursion<T>>();
    foreach (var recursion in seedResult.Recursions) {
      if (recursion.Parser == this) {
        myRecursions.Add(recursion);
      } else {
        otherRecursions.Add(recursion);
      }
    }

    while (change) {
      change = false;
      foreach (var recursion in myRecursions) {
        // after a few iterations a binaryExpr 3 / x, is built
        // now the binaryExpr itself is available as a seed,
        // And the FoundRecursion that built it still holds a pionter to the BinaryExpr that was used to construct the initial one.
        // Constructors should be on the right of self expressions
        var newResult = recursion.Apply(bestSuccess.Value!, bestSuccess.Remainder);
        
        combinedResult = combinedResult.Combine(newResult);
        if (newResult.Success != null) {
          bestSuccess = newResult.Success;
          change = true;
          break;
        }
      }
    }

    // TODO figure out why we have to Remove(this) here. Wouldn't a .Drop call already remove that?
    var finalSuccess = combinedResult.Success == null
      ? null
      : combinedResult.Success with {
        Remainder = combinedResult.Success.Remainder.Remove(this)
      };
    combinedResult = new Aggregate<T>(finalSuccess, combinedResult.Failure, otherRecursions);

    return combinedResult;
  }
}