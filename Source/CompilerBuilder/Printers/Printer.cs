// See https://aka.ms/new-console-template for more information

namespace CompilerBuilder;

record IndentW<T>(Printer<T> Inner, int Amount) : Printer<T> {
  public PrintResult Print(T value) {
    var innerValue = Inner.Print(value);
    return innerValue.Continue(v => v.Indent(Amount));
  }
}

public record Failure(object? Value, Printer Printer, Document SoFar, string Message) {
  public static Failure? Max(Failure? first, Failure? second) {
    if (first == null) {
      return second;
    }

    if (second == null) {
      return first;
    }
    return first.SoFar.Size >= second.SoFar.Size ? first : second;
  }
}

public record PrintResult(Document? Success, Failure? LongestFailure) {

  public Document ForceSuccess {
    get {
      if (Success == null) {
        var soFarString = LongestFailure!.SoFar.RenderAsString();
        throw new Exception($"Printing failed with message {LongestFailure!.Message}. Longest print was:\n{soFarString}");
      }

      return Success;
    }
  }
  public PrintResult(object? value, Printer printer, string message) : this(null, new Failure(value, printer, Empty.Instance, message)) { }
  
  public PrintResult(Document Success) : this(Success, null) { }

  public PrintResult Continue(Func<Document, Document> f) {
    return new PrintResult(Success == null ? null : f(Success), LongestFailure == null ? null : LongestFailure with { SoFar = f(LongestFailure.SoFar) });
  }

  public PrintResult WithFailure(Failure? failure, bool priority) {
    if (failure == null) {
      return this;
    }
    
    if (Success != null) {
      // TODO we have a curious situation with "true" -> Constant(true) leading to a longer SoFar than a success
      if (Success.Size >= failure.SoFar.Size) {
        return this;
      }
    }

    return this with { LongestFailure = priority ? Failure.Max(failure, LongestFailure) : Failure.Max(LongestFailure, failure) };
  }
}

public interface Printer<in T> : Printer {

  public PrintResult Print(T value);
}

class FailW<T>(string message) : Printer<T> {
  public string Message => message;
  
  public PrintResult Print(T value) {
    return new PrintResult(value, this, message);
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

  public Printer<T> First => first;
  public Printer<T> Second => second;
  
  public PrintResult Print(T value) {
    var firstResult = First.Print(value);
    var secondResult = Second.Print(value);
    if (firstResult.Success == null) {
      return secondResult.WithFailure(firstResult.LongestFailure, true);
    }

    return firstResult.WithFailure(secondResult.LongestFailure, false);
  }
}

class Cast<T, U>(Printer<T> printer) : Printer<U> {
  public PrintResult Print(U value) {
    if (value is T t) {
      return printer.Print(t);
    }

    return new PrintResult(value, this, $"Value {value + ""} was not of type {typeof(T)}");
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

  public Printer<T> Printer => printer;
  
  public PrintResult Print(U value) {
    var newValue = map(value);
    if (newValue is MapSuccess<T> success) {
      return printer.Print(success.Value);
    }

    if (value?.ToString() == "i := i + 1;") {
      var e = 3;
    }
    return new PrintResult(value, this, "OptionMap failure");
  }
}

class ValueW<T>(Func<T, bool> check, VoidPrinter printer) : Printer<T> {

  public Func<T, bool> Check => check;
  
  public PrintResult Print(T value) {
    if (check(value)) {
      return new PrintResult(printer.Print());
    }

    return new PrintResult(value, this, "ValueW check failure");
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
  
  public Printer<TFirst> First => first;
  public Printer<TSecond> Second => second;
  
  public PrintResult Print(T value) {
    var t = destruct(value);
    if (t == null) {
      return new PrintResult(value, this, "sequence destruct failure");
    }

    var (firstValue, secondValue) = t.Value;
    var firstDoc = first.Print(firstValue);
    if (firstDoc.Success == null) {
      return firstDoc;
    }

    var secondResult = second.Print(secondValue);
    var printResult = secondResult.Continue(s => firstDoc.Success.Then(s, separator));
    return printResult.WithFailure(firstDoc.LongestFailure, false);
  }
}

class SkipLeftW<T>(VoidPrinter first, Printer<T> second, Separator separator) : Printer<T> {
  public VoidPrinter First => first;
  public Printer<T> Second => second;
  
  public PrintResult Print(T value) {
    var firstValue = first.Print();
    var secondValue = second.Print(value);
    return secondValue.Continue(s => firstValue.Then(s, separator));
  }
}

class SkipRightW<T>(Printer<T> first, VoidPrinter second, Separator separator) : Printer<T> {
  public Printer<T> First => first;
  public VoidPrinter Second => second;
  
  public PrintResult Print(T value) {
    var firstValue = first.Print(value);
    if (firstValue.Success == null) {
      return firstValue;
    }
    // TODO maybe we should not copy the firstValue to the LongestFailure here, because in a way it failed as well.
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