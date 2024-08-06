namespace CompilerBuilder;

interface ISequenceLikeG {
  Type FirstType { get; }
  Type SecondType { get; }
  Type Type { get; }
  public Grammar First { get; set; }
  public Grammar Second { get; set; }
  public Orientation Mode { get; set; }
}

class SequenceG<TFirst, TSecond, T>(Grammar<TFirst> first, Grammar<TSecond> second, Orientation mode, 
  Func<TFirst, TSecond, T> construct, Func<T, (TFirst, TSecond)?> destruct) : Grammar<T>, ISequenceLikeG {
  public Type FirstType => typeof(TFirst);
  public Type SecondType => typeof(TSecond);
  public Type Type => typeof(T);
  
  Grammar ISequenceLikeG.First {
    get => First;
    set => First = (Grammar<TFirst>)value;
  }

  Grammar ISequenceLikeG.Second {
    get => Second;
    set => Second = (Grammar<TSecond>)value;
  }

  Orientation ISequenceLikeG.Mode { get; set; }
  public Grammar<TFirst> First { get; set; } = first;
  public Grammar<TSecond> Second { get; set; } = second;

  public Orientation Mode => mode;

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    var firstPrinter = (Printer<TFirst>)recurse(First);
    var secondPrinter = (Printer<TSecond>)recurse(Second);
    return new SequenceW<TFirst,TSecond,T>(firstPrinter, secondPrinter, destruct, mode);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    var leftParser = (Parser<TFirst>)recurse(First);
    var rightParser = (Parser<TSecond>)recurse(Second);
    return new SequenceR<TFirst, TSecond, T>(leftParser, rightParser, construct);
  }

  public IEnumerable<Grammar> Children => [First, Second];
}

class SkipLeftG<T>(VoidGrammar first, Grammar<T> second, Orientation mode = Orientation.Spaced) : Grammar<T>, ISequenceLikeG {
  public Type FirstType => typeof(Unit);
  public Type SecondType => typeof(T);
  public Type Type => typeof(T);
  Grammar ISequenceLikeG.First {
    get => First;
    set => First = (VoidGrammar)value;
  }

  Grammar ISequenceLikeG.Second {
    get => Second;
    set => Second = (Grammar<T>)value;
  }

  public Orientation Mode { get; set; }
  public VoidGrammar First { get; set; } = first;
  public Grammar<T> Second { get; set; } = second;

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    var first = (VoidPrinter)recurse(First);
    var second = (Printer<T>)recurse(Second);
    return new SkipLeftW<T>(first, second, mode);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new SkipLeft<T>((VoidParser)recurse(First), (Parser<T>)recurse(Second));
  }

  public IEnumerable<Grammar> Children => [First, Second];
}

class SkipRightG<T>(Grammar<T> first, VoidGrammar second, Orientation mode = Orientation.Spaced) : Grammar<T>, ISequenceLikeG {
  public Type FirstType => typeof(T);
  public Type SecondType => typeof(Unit);
  public Type Type => typeof(T);
  
  Grammar ISequenceLikeG.First {
    get => First;
    set => First = (Grammar<T>)value;
  }

  Grammar ISequenceLikeG.Second {
    get => Second;
    set => Second = (VoidGrammar)value;
  }

  public Orientation Mode { get; set; }
  public Grammar<T> First { get; set; } = first;
  public VoidGrammar Second { get; set; } = second;
  
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    var firstParser = (Printer<T>)recurse(First);
    var secondParser = (VoidPrinter)recurse(Second);
    return new SkipRightW<T>(firstParser, secondParser, mode);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new SkipRight<T>((Parser<T>)recurse(First), (VoidParser)recurse(Second));
  }

  public IEnumerable<Grammar> Children => [First, Second];
}