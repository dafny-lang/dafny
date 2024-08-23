// See https://aka.ms/new-console-template for more information

namespace CompilerBuilder;

record IndentW<T>(Printer<T> Inner, int Amount) : Printer<T> {
  public PrintResult Print(T value) {
    var innerValue = Inner.Print(value);
    return innerValue.Continue(v => v.Indent(Amount));
  }
}

public record PrintResult(Document? Success, Document LongestResult) {

  public Document ForceSuccess {
    get {
      if (Success == null) {
        throw new Exception($"Printing failed. Longest print was {LongestResult.RenderAsString()}");
      }

      return Success;
    }
  }
  public PrintResult() : this(null, Empty.Instance) { }
  
  public PrintResult(Document Success) : this(Success, Success) {
    
  }

  public PrintResult Continue(Func<Document, Document> f) {
    return new PrintResult(Success == null ? null : f(Success), f(LongestResult));
  }
}

public interface Printer<in T> : Printer {

  public PrintResult Print(T value);
}

class FailW<T> : Printer<T> {
  public PrintResult Print(T value) {
    return new PrintResult();
  }
}

class RecursiveW<T>(Func<Printer<T>> get) : Printer<T> {
  private Printer<T>? inner;
  public Printer<T> Inner => inner ??= get();
  
  public PrintResult Print(T value) {
    return Inner.Print(value);
  }
}

class ChoiceW<T>(Printer<T> first, Printer<T> second): Printer<T> {
  public PrintResult Print(T value) {
    var firstResult = first.Print(value);
    if (firstResult.Success == null) {
      var secondResult = second.Print(value);
      var longest = firstResult.LongestResult.Size >= secondResult.LongestResult.Size
        ? firstResult.LongestResult
        : secondResult.LongestResult;
      return secondResult with { LongestResult = longest };
    }

    
    

    // TODO should I always also print the second, to use its LongestResult?
    return firstResult;
  }
}

class Cast<T, U>(Printer<T> printer) : Printer<U> {
  public PrintResult Print(U value) {
    if (value is T t) {
      return printer.Print(t);
    }

    return new PrintResult();
  }
}

public interface Printer;

public interface VoidPrinter : Printer {
  
  public Document Print();
}

class EmptyW : VoidPrinter {
  public static readonly EmptyW Instance = new();

  private EmptyW() { }
  public Document Print() {
    return Empty.Instance;
  }
}

class VerbatimW : Printer<string> {
  public static readonly Printer<string> Instance = new VerbatimW();

  private VerbatimW() { }
  public PrintResult Print(string value) {
    return new PrintResult(new Verbatim(value));
  }
}

class MapWithoutFailW<T, U>(Printer<T> printer, Func<U, T> map) : Printer<U> {
  public PrintResult Print(U value) {
    var newValue = map(value);
    return printer.Print(newValue);
  }
}

class MapW<T, U>(Printer<T> printer, Func<U, T> map) : Printer<U> {
  public PrintResult Print(U value) {
    return printer.Print(map(value));
  }
}

class OptionMapW<T, U>(Printer<T> printer, Func<U, MapResult<T>> map) : Printer<U> {
  public PrintResult Print(U value) {
    var newValue = map(value);
    if (newValue is MapSuccess<T> success) {
      return printer.Print(success.Value);
    }
    return new PrintResult();
  }
}

class ValueW<T>(T expected, VoidPrinter printer) : Printer<T> {
  public PrintResult Print(T value) {
    if (Equals(expected, value)) {
      return new PrintResult(printer.Print());
    }

    return new PrintResult();
  }
}

class IgnoreW<T>(VoidPrinter printer) : Printer<T> {
  public PrintResult Print(T value) {
    return new PrintResult(printer.Print());
  }
}

// TODO rename TextW and VerbatimW to make the difference more clear?
internal class TextW(string value) : VoidPrinter {
  public Document Print() {
    return new Verbatim(value);
  }
}

// TODO replace by map and VerbatimW?
internal class NumberW : Printer<int> {
  public PrintResult Print(int value) {
    return new PrintResult(new Verbatim(value.ToString()));
  }
}

class SequenceW<TFirst, TSecond, T>(Printer<TFirst> first, Printer<TSecond> second, 
  Func<T, (TFirst, TSecond)?> destruct, Separator separator) : Printer<T> {
  public PrintResult Print(T value) {
    var t = destruct(value);
    if (t == null) {
      return new PrintResult();
    }

    var (firstValue, secondValue) = t.Value;
    var firstDoc = first.Print(firstValue);
    if (firstDoc.Success == null) {
      return new PrintResult();
    }
    var secondDoc = second.Print(secondValue);
    if (secondDoc.Success == null) {
      return firstDoc with { Success = null };
    }

    return new PrintResult(firstDoc.Success.Then(secondDoc.Success, separator));
  }
}

class SkipLeftW<T>(VoidPrinter first, Printer<T> second, Separator separator) : Printer<T> {
  public PrintResult Print(T value) {
    var firstValue = first.Print();
    var secondValue = second.Print(value);
    return secondValue.Continue(s => firstValue.Then(s, separator));
  }
}

class SkipRightW<T>(Printer<T> first, VoidPrinter second, Separator separator) : Printer<T> {
  public PrintResult Print(T value) {
    var firstValue = first.Print(value);
    return firstValue.Continue(f => f.Then(second.Print(), separator));
  }
}

class NeitherW(VoidPrinter first, VoidPrinter second, Separator separator) : VoidPrinter {
  public Document Print() {
    return first.Print().Then(second.Print(), separator);
  }
}

public static class PrinterExtensions {
  public static Printer<U> Map<T, U>(this Printer<T> printer, Func<U, MapResult<T>> map) {
    return new OptionMapW<T, U>(printer, map);
  }
  
  public static Printer<U> Map<T, U>(this Printer<T> printer, Func<U, T> map) {
    return new MapW<T, U>(printer, map);
  }
}