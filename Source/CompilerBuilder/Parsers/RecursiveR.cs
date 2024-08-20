using Microsoft.Dafny;

namespace CompilerBuilder;

class EmptyResult<T> : ParseResult<T> {
  public ParseResult<TU> Continue<TU>(Func<ConcreteSuccess<T>, ParseResult<TU>> f) {
    return new EmptyResult<TU>();
  }

  public ConcreteSuccess<T>? Success => null;
  public FailureResult<T>? Failure => null;
  public IEnumerable<IFoundRecursion<T>> Recursions => Enumerable.Empty<IFoundRecursion<T>>();
}
class RecursiveR<T>(Func<Parser<T>> get, string debugName) : Parser<T> {
  private readonly string debugName = debugName;
  private Parser<T>? inner;
  
  /*
   * TODO
   * The FoundRecursion results are always the same, regardless of the text pointer, right???
   * Maybe find them statically, once
   * And later do not return results for FoundRecursion
   * Maybe cache that part and don't return them the second time.
   */

  public Parser<T> Inner => inner ??= get();
  
  enum RecursionState { FindingRecursions, Entered, Fresh }
  private readonly ThreadLocal<RecursionState> state = new(() => RecursionState.Fresh);
  private readonly ThreadLocal<SinglyLinkedList<int>> enteredStack = new(() => new Nil<int>());
  
  private List<IFoundRecursion<T>>? leftRecursions;
  private static readonly ITextPointer deadPointer = new PointerFromString("");
  
  public override ParseResult<T> Parse(ITextPointer text) {
    
    var recursionState = state.Value;
    if (recursionState == RecursionState.FindingRecursions) {
      return new FoundRecursion<T, T>(this, Util.Identity);
    }
    
    if (leftRecursions == null) {
      state.Value = RecursionState.FindingRecursions;
      var result = Inner.Parse(deadPointer);
      leftRecursions = result.Recursions.ToList();
      state.Value = RecursionState.Fresh;
    }

    var startingStack = enteredStack.Value!;
    if (startingStack is Cons<int> cons && cons.Head == text.Offset) {
      // Hit left recursion
      return new EmptyResult<T>();
    }

    if (!leftRecursions.Any()) {
      return text.ParseWithCache2(Inner);
    }

    // TODO breaks when we find ourself but at a different location, which can happen for non-left recursion
    enteredStack.Value = new Cons<int>(text.Offset, startingStack!);
    // TODO caching here seems pointless
    var seedResult = text.ParseWithCache2(Inner);
    enteredStack.Value = startingStack;
    if (seedResult.Success == null) {
      return seedResult;
    }

    ParseResult<T> combinedResult = seedResult;
    ConcreteSuccess<T>? bestSuccess = seedResult.Success;
    var change = true;

    var b = 3;

    while (change) {
      change = false;
      foreach (var recursion in leftRecursions) {
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

    return combinedResult;
  }
}