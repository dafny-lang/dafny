using Microsoft.Dafny;

namespace CompilerBuilder;

class EmptyResult<T> : ParseResult<T> {
  public ParseResult<TU> Continue<TU>(Func<ConcreteSuccess<T>, ParseResult<TU>> f) {
    return new EmptyResult<TU>();
  }

  public ConcreteSuccess<T>? Success => null;
  public FailureResult<T>? Failure => null;
  public IFoundRecursion<T>? FoundRecursion => null;
  public IEnumerable<IFoundRecursion<T>> Recursions => [];
}

/// <summary>
/// It grows the seed result by building a "ParseResult<T> -> ParseResult<T>"
///
/// Alternatively, we could try to transform the grammar to get a separate base and grow grammar,
/// which would avoid hitting 'recursive calls' while determining the base
///
/// However, transforming the grammar is difficult, partly due to empty parts
/// The only way to do it is the gather all the paths in the grammar
/// And then separate the left recursive ones from the others
/// expr = (empty | 'a') (expr | 'b') 'c'
/// path1 = expr 'c'
/// path2 = 'bc'
/// path3 = 'a' expr 'c'
/// path4 = 'abc'
/// base = 'bc' | 'a' expr 'c' | 'abc'
/// grow = grow 'c'
/// </summary>
class RecursiveR<T>(Func<Parser<T>> get, string debugName) : Parser<T> {
  private readonly string debugName = debugName;
  private Parser<T>? inner;

  public Parser<T> Inner => inner ??= get();
  
  enum RecursionState { FindingLeftRecursions, Parsing }
  private readonly ThreadLocal<RecursionState> findingRecursionState = new(() => RecursionState.Parsing);
  private readonly ThreadLocal<SinglyLinkedList<int>> enteredStack = new(() => new Nil<int>());

  private bool checkedLeftRecursion;
  private IFoundRecursion<T>? leftRecursion;
  private static readonly ITextPointer deadPointer = new PointerFromString("");
  
  public override ParseResult<T> Parse(ITextPointer text) {
    
    var recursionState = findingRecursionState.Value;
    if (recursionState == RecursionState.FindingLeftRecursions) {
      return new FoundRecursion<T, T>(Util.Identity);
    }
    
    if (!checkedLeftRecursion) {
      findingRecursionState.Value = RecursionState.FindingLeftRecursions;
      leftRecursion = Inner.Parse(deadPointer) as IFoundRecursion<T>;
      findingRecursionState.Value = RecursionState.Parsing;
      checkedLeftRecursion = true;
    }

    var startingStack = enteredStack.Value!;
    if (startingStack is Cons<int> cons && cons.Head == text.Offset) {
      // Hit left recursion
      return new EmptyResult<T>();
    }

    if (leftRecursion == null) {
      return text.ParseWithCache2(Inner);
    }

    enteredStack.Value = new Cons<int>(text.Offset, startingStack!);
    // TODO caching here seems pointless
    var seedResult = text.ParseWithCache2(Inner);
    enteredStack.Value = startingStack;
    if (seedResult.Success == null) {
      return seedResult;
    }

    ParseResult<T> combinedResult = seedResult;
    ConcreteSuccess<T>? bestSuccess = seedResult.Success;

    while (bestSuccess != null) {
      // after a few iterations a binaryExpr 3 / x, is built
      // now the binaryExpr itself is available as a seed,
      // And the FoundRecursion that built it still holds a pionter to the BinaryExpr that was used to construct the initial one.
      // Constructors should be on the right of self expressions
      var newResult = leftRecursion.Apply(bestSuccess.Value!, bestSuccess.Remainder);
      
      combinedResult = combinedResult.Combine(newResult);
      bestSuccess = newResult.Success;
    }

    return combinedResult;
  }
}