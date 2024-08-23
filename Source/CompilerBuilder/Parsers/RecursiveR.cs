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

class DeadPointer : ITextPointer {
  public int Offset => 0;
  public int Line => 0;
  public int Column => 0;
  public ITextPointer Drop(int amount) {
    return this;
  }

  public char First => throw new InvalidOperationException();
  public int Length => 0;
  public char At(int offset) {
    throw new InvalidOperationException();
  }

  public ReadOnlySpan<char> Remainder => ReadOnlySpan<char>.Empty;
  public ReadOnlySpan<char> SubSequence(int length) {
    return ReadOnlySpan<char>.Empty;
  }

  public ParseResult<Unit> ParseWithCache(VoidParser parser, string reason) {
    return parser.Parse(this);
  }

  public ParseResult<T> ParseWithCache<T>(Parser<T> parser, string reason) {
    return parser.Parse(this);
  }

  public void Ref() {
  }

  public void UnRef() {
  }
}

class RecursiveR<T>(Func<Parser<T>> get, string debugName) : Parser<T> {
  private readonly string debugName = debugName;
  private Parser<T>? inner;

  public Parser<T> Inner => inner ??= get();
  
  /// <summary>
  /// It grows the seed result by building a "ParseResult<T> -> ParseResult<T>" using a 'IFoundRecursion<T>'
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
  private FoundRecursion<T, T>? leftRecursion;
  private bool checkedLeftRecursion;
  enum RecursionState { FindingLeftRecursions, Parsing }
  private readonly ThreadLocal<RecursionState> findingRecursionState = new(() => RecursionState.Parsing);
  
  /// <summary>
  /// Alternatively we could store the 'entered' state either in the ITextPointer, so we would store which parsers
  /// we've entered instead of which offsets.
  ///
  /// Or we could pass this enteredParsers set down through the calls to 'Parse'
  /// However, I didn't want to let recursion effect either ITextPointer or the interface of Parse.
  /// If we had access to the call-stack, we would inspect it instead of using this field.
  /// 
  /// I'm hoping that when we move to a stackless system, we'll have access to the 'stack',
  /// and then we no longer need this field.
  /// </summary>
  private readonly ThreadLocal<SinglyLinkedList<int>> enteredStack = new(() => new Nil<int>());
  
  public override ParseResult<T> Parse(ITextPointer text) {
    
    var recursionState = findingRecursionState.Value;
    if (recursionState == RecursionState.FindingLeftRecursions) {
      return new FoundRecursion<T, T>(Util.Identity);
    }
    
    if (!checkedLeftRecursion) {
      if (typeof(T).Name == "Statement") {
        var d = 3;
      }
      findingRecursionState.Value = RecursionState.FindingLeftRecursions;
      leftRecursion = (FoundRecursion<T, T>?)Inner.Parse(new DeadPointer()).FoundRecursion;
      findingRecursionState.Value = RecursionState.Parsing;
      checkedLeftRecursion = true;
    }

    var startingStack = enteredStack.Value!;
    if (startingStack is Cons<int> cons && cons.Head == text.Offset) {
      // Hit left recursion
      return new EmptyResult<T>();
    }

    if (leftRecursion == null) {
      return Inner.Parse(text);
    }

    enteredStack.Value = new Cons<int>(text.Offset, startingStack!);
    // TODO caching here seems pointless
    var seedResult = Inner.Parse(text);
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