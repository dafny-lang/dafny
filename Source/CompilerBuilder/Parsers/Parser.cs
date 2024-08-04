﻿// See https://aka.ms/new-console-template for more information

using System.Collections.Immutable;

namespace CompilerBuilder;

record Unit {
  public static readonly Unit Instance = new();

  private Unit() { }
}
public abstract class VoidParser : Parser {
  public static implicit operator VoidParser(string keyword) => new TextR(keyword);
  
  internal abstract ParseResult<Unit> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives);
}

class IgnoreR<T>(Parser<T> parser) : VoidParser {
  internal override ParseResult<Unit> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    return parser.Parse(text, recursives).Continue(
      s => new ConcreteSuccess<Unit>(Unit.Instance, s.Remainder));
  }
}

public interface Parser {
}
public interface Parser<T> : Parser {
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives);
  
  public ConcreteResult<T> Parse(string text) {
    ITextPointer pointer = new PointerFromString(text);
    var withEnd = new EndOfText<T>(this);
    return withEnd.Parse(pointer, ImmutableHashSet<Parser>.Empty).Concrete!;
  }
}

class EndOfText<T>(Parser<T> inner) : Parser<T> {
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var innerResult = inner.Parse(text, recursives);
    if (innerResult.Success == null) {
      return innerResult;
    }

    var end = innerResult.Success.Remainder;
    if (end.Length <= 0) {
      return innerResult.Success;
    }

    var endFail = end.Fail<T>("the end of the text");
    if (innerResult.Failure != null) {
      return innerResult.Failure.Location.Offset > innerResult.Success.Remainder.Offset
        ? innerResult.Failure
        : end.Fail<T>("the end of the text");
    }

    return endFail;
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

// TODO maybe change the right to an aggregate function of TLeft and TRight
// And leave the container concept for the extensions

public class SequenceR<TLeft, TRight, T>(Parser<TLeft> first, Parser<TRight> second, Func<TLeft, TRight, T> combine) : Parser<T> {
  
  public Parser<TLeft> First { get; set; } = first;
  public Parser<TRight> Second { get; set; } = second;
  
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var leftResult = First.Parse(text, recursives);
    return leftResult.Continue(leftConcrete => {
      var rightResult = Second.Parse(leftConcrete.Remainder, ImmutableHashSet<Parser>.Empty);
      return rightResult.Continue(rightConcrete => {
        var value = combine(leftConcrete.Value, rightConcrete.Value);
        return new ConcreteSuccess<T>(value, rightConcrete.Remainder);
      });
    });
  }
}

class ChoiceR<T>(Parser<T> first, Parser<T> second): Parser<T> {

  public Parser<T> First { get; set; } = first;
  public Parser<T> Second { get; set; } = second;
  
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var firstResult = First.Parse(text, recursives);
    var secondResult = Second.Parse(text, recursives);
    return firstResult.Combine(secondResult);
  }
}

class RecursiveR<T>(Func<Parser<T>> get) : Parser<T> {
  private Parser<T>? inner;

  public Parser<T> Inner => inner ??= get();

  public static T Identity<T>(T value) {
    return value;
  }
  
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {

    if (recursives.Contains(this)) {
      return new FoundRecursion<T, T>(Identity);
    }
    
    var seedResult = Inner.Parse(text, recursives.Add(this));
    if (seedResult.Success == null) {
      return seedResult;
    }

    ParseResult<T> combinedResult = seedResult;
    foreach (var recursion in seedResult.Recursions) {
      var current = seedResult;
      while (current.Success != null) {
        current = recursion.Apply(current.Success.Value!, current.Success.Remainder);
      }

      combinedResult = combinedResult.Combine(current);
    }

    return combinedResult;
  }
}

class PositionR : Parser<IPosition> {
  public static readonly PositionR Instance = new();

  private PositionR()
  {
  }

  public ParseResult<IPosition> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    return new ConcreteSuccess<IPosition>(text, text);
  }
}

class WithRangeR<T, U>(Parser<T> parser, Func<ParseRange, T, U> map) : Parser<U> {

  public Parser<T> Parser { get; set; } = parser;
  
  public ParseResult<U> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var start = text;
    var innerResult = Parser.Parse(text, recursives);
    return innerResult.Continue(success => {
      var end = success.Remainder;
      return new ConcreteSuccess<U>(map(new ParseRange(start, end), success.Value), success.Remainder);
    });
  }
}

class SkipLeft<T>(VoidParser left, Parser<T> right) : Parser<T> {
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var leftResult = left.Parse(text, recursives);
    return leftResult.Continue(leftConcrete => right.Parse(leftConcrete.Remainder, ImmutableHashSet<Parser>.Empty));
  }
}

class SkipRight<T>(Parser<T> first, VoidParser second) : Parser<T> {

  public Parser<T> First { get; set; } = first;
  public VoidParser Second { get; set; } = second;
  
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var leftResult = First.Parse(text, recursives);
    return leftResult.Continue(leftConcrete => Second.Parse(leftConcrete.Remainder, ImmutableHashSet<Parser>.Empty).
      Continue(rightSuccess => leftConcrete with { Remainder = rightSuccess.Remainder }));
  }
}

class TextR(string value) : VoidParser {
  internal override ParseResult<Unit> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var actual = text.SubSequence(value.Length);
    if (actual.Equals(value)) {
      return new ConcreteSuccess<Unit>(Unit.Instance, text.Drop(value.Length));
    }

    return new FailureResult<Unit>($"Expected '{value}' but found '{actual}'", text);
  }
}

internal class Whitespace : Parser<string> {
  public ParseResult<string> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var offset = 0;
    while (text.Length > offset) {
      var c = text.At(offset);
      if (Char.IsWhiteSpace(c)) {
        offset++;
      } else {
        break;
      }
    }

    if (offset > 0) {
      var result = text.SubSequence(offset);
      return new ConcreteSuccess<string>(result, text.Drop(offset));
    }

    return text.Fail<string>("whitespace");
  }
}

internal class LineComment : Parser<string> {
  public ParseResult<string> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var start = text.SubSequence(2);
    if (!start.Equals("//")) {
      return text.Fail<string>("a // line comment");
    }

    var offset = 2;
    while (text.Length > offset) {
      var c = text.At(offset);
      if (c != '\n') {
        offset++;
      } else {
        break;
      }
    }

    var comment = text.SubSequence(offset);
    return new ConcreteSuccess<string>(comment, text.Drop(offset + 1));
  }
}

internal class NumberR : Parser<int> {
  public ParseResult<int> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
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
      return new FailureResult<int>($"'{sequence}' is not a number", text);
    }

    return text.Fail<int>("a digit");
  }
}

internal class IdentifierR : Parser<string> {
  public ParseResult<string> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
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

    return text.Fail<string>("an identifier");
  }
}

class ValueR<T>(Func<T> value) : Parser<T> {

  public T Evaluated => value();
  
  public ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    return new ConcreteSuccess<T>(value(), text);
  }
}