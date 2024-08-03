// See https://aka.ms/new-console-template for more information

using System.Collections.Immutable;
using System.Net.Mime;

namespace CompilerBuilder;

record Unit;
public abstract class VoidParser : Parser {
  public static implicit operator VoidParser(string keyword) => new TextR(keyword);
  
  internal abstract ParseResult<Unit> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives);
}

public abstract class Parser {
  
  internal virtual void Schedule(ParseState state) {
    throw new NotImplementedException();
  }
}



public abstract class Parser<T> : Parser {
  internal abstract ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives);
  
  public ConcreteResult<T> Parse(string text) {
    ITextPointer pointer = new PointerFromString(text);
    return Parse(pointer, ImmutableHashSet<Parser>.Empty).Concrete!;
  }
}

class PointerFromString(string text) : ITextPointer {
  public PointerFromString(string text, int offset, int line, int column) : this(text) {
    Offset = offset;
    Line = line;
    Column = column;
  }

  public int Offset { get; }
  public int Line { get; }
  public int Column { get; }
  public ITextPointer Drop(int amount) {
    var sequence = SubSequence(amount);
    var lines = sequence.Split("\n");
    return new PointerFromString(text, Offset + amount, Line + lines.Length - 1, lines.Last().Length);
  }

  public char First => At(0);
  public int Length => text.Length - Offset;

  public char At(int offset) {
    return text[Offset + offset];
  }

  public string SubSequence(int length) {
    return text.Substring(Offset, Math.Min(Length, length));
  }
}

class SequenceR<TContainer>(Parser<TContainer> left, Parser<Action<TContainer>> right) : Parser<TContainer> {
  internal override ParseResult<TContainer> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var leftResult = left.Parse(text, recursives);
    return leftResult.Continue(leftConcrete => {
      var rightResult = right.Parse(leftConcrete.Remainder, recursives);
      return rightResult.Continue(rightConcrete => {
        rightConcrete.Value(leftConcrete.Value);
        return leftConcrete with { Remainder = rightConcrete.Remainder };
      });
    });
  }

  internal override void Schedule(ParseState state) {
    state.Plan(left, right, (container, value) => {
      value(container);
      state.Store(container!);
    });
  }
}

class ChoiceR<T>(Parser<T> first, Parser<T> second): Parser<T> {
  internal override ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var firstResult = first.Parse(text, recursives);
    var secondResult = second.Parse(text, recursives);
    return firstResult.Combine(secondResult);
  }

  internal override void Schedule(ParseState state) {
    state.Plan(first, () => {
      state.Todos.Push(second);
    });
  }
}

class RecursiveR<T>(Func<Parser<T>> get) : Parser<T> {
  private Parser<T>? inner;
  
  internal override ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    inner ??= get();

    if (recursives.Contains(this)) {
      return new FoundRecursion<T, T>(s => s);
    }
    
    var innerResult = inner.Parse(text, recursives.Add(this));
    if (innerResult.Success == null) {
      return innerResult;
    }

    ConcreteSuccess<T> bestResult = innerResult.Success;
    foreach (var recursion in innerResult.Recursions) {
      var currentBase = innerResult.Success;
      while (true) {
        var recursiveResult = recursion.Apply(currentBase.Value!, currentBase.Remainder);
        if (recursiveResult.Success != null) {
          currentBase = recursiveResult.Success;
        } else {
          break;
        }
      }

      if (currentBase.Remainder.Offset > bestResult.Remainder.Offset) {
        bestResult = currentBase;
      }
    }

    return bestResult;
  }
}

class PositionR : Parser<IPosition> {
  public static readonly PositionR Instance = new();

  private PositionR()
  {
  }

  internal override ParseResult<IPosition> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    return new ConcreteSuccess<IPosition>(text, text);
  }

  internal override void Schedule(ParseState state) {
    state.Results.Push(state.Location);
  }
}

class WithRangeR<T, U>(Parser<T> parser, Func<ParseRange, T, U> map) : Parser<U> {
  internal override ParseResult<U> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var start = text;
    var innerResult = parser.Parse(text, recursives);
    return innerResult.Continue(success => {
      var end = success.Remainder;
      return new ConcreteSuccess<U>(map(new ParseRange(start, end), success.Value), success.Remainder);
    });
  }

  internal override void Schedule(ParseState state) {
    state.Todos.Push(() => {
      var end = (IPosition)state.Results.Pop();
      var result = (T)state.Results.Pop();
      var start = (IPosition)state.Results.Pop();
      var range = new ParseRange(start, end);
      state.Results.Push(map(range, result)!);
    });
    state.Todos.Push(PositionR.Instance);
    state.Todos.Push(parser);
    state.Todos.Push(PositionR.Instance);
  }
}

class SkipLeft<T>(VoidParser left, Parser<T> right) : Parser<T> {
  internal override ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var leftResult = left.Parse(text, recursives);
    return leftResult.Continue(leftConcrete => right.Parse(leftConcrete.Remainder, recursives));
  }

  internal override void Schedule(ParseState state) {
    state.Todos.Push(left);
    state.Todos.Push(right);
  }
}

class SkipRight<T>(Parser<T> left, VoidParser right) : Parser<T> {
  internal override ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var leftResult = left.Parse(text, recursives);
    return leftResult.Continue(leftConcrete => right.Parse(leftConcrete.Remainder, recursives).
      Continue(rightSuccess => leftConcrete with { Remainder = rightSuccess.Remainder }));
  }

  internal override void Schedule(ParseState state) {
    state.Todos.Push(right);
    state.Todos.Push(left);
  }
}

class TextR(string value) : VoidParser {
  internal override void Schedule(ParseState state) {
    throw new NotImplementedException();
  }

  internal override ParseResult<Unit> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var actual = text.SubSequence(value.Length);
    if (actual.Equals(value)) {
      return new ConcreteSuccess<Unit>(new Unit(), text.Drop(value.Length));
    }

    return new FailureR<Unit>($"Expected '{value}' but found '{actual}'", text);
  }
}

internal class NumberR : Parser<int> {
  internal override ParseResult<int> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var offset = 0;
    while (text.Length > offset) {
      var c = text.At(offset);
      if (Char.IsDigit(c)) {
        offset++;
      } else {
        break;
      }
    }

    if (offset > 0) {
      var sequence = text.SubSequence(offset);
      if (int.TryParse(sequence, out var parsed))
      {
        return new ConcreteSuccess<int>(parsed, text.Drop(offset));
      }
      return new FailureR<int>($"{sequence} is not a number", text);
    }

    return new FailureR<int>($"{text.First} is not a digit", text);
  }
}

internal class IdentifierR : Parser<string> {
  internal override ParseResult<string> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var offset = 0;
    while (text.Length > offset) {
      var c = text.At(offset);
      if (Char.IsLetter(c)) {
        offset++;
      } else {
        break;
      }
    }

    if (offset > 0) {
      var sequence = text.SubSequence(offset);
      return new ConcreteSuccess<string>(sequence, text.Drop(offset));
    }

    return new FailureR<string>($"{text.First} is not an identifier", text);
  }
}

class ValueR<T>(T value) : Parser<T> {
  internal override ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    return new ConcreteSuccess<T>(value, text);
  }
}