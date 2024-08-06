using System.Collections.Immutable;

namespace CompilerBuilder;

record Unit {
  public static readonly Unit Instance = new();

  private Unit() { }
}
public abstract class VoidParser : Parser {
  public static implicit operator VoidParser(string keyword) => new TextR(keyword);
  
  internal abstract ParseResult<Unit> Parse(ITextPointer text);
}

class IgnoreR<T>(Parser<T> parser) : VoidParser {
  public Parser<T> Parser => parser;

  internal override ParseResult<Unit> Parse(ITextPointer text) {
    return parser.Parse(text).Continue(
      s => new ConcreteSuccess<Unit>(Unit.Instance, s.Remainder));
  }
}

public interface Parser;

public interface Parser<T> : Parser {
  
  // TODO make internal??
  public ParseResult<T> Parse(ITextPointer text);
  
  public ConcreteResult<T> Parse(string text) {
    ITextPointer pointer = new PointerFromString(text);
    var withEnd = new EndOfText<T>(this);
    return withEnd.Parse(pointer).Concrete!;
  }
}

class EndOfText<T>(Parser<T> inner) : Parser<T> {
  public ParseResult<T> Parse(ITextPointer text) {
    var innerResult = inner.Parse(text);
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

/*
 * TODO
 * it might be a cool idea to use PointerFromString to determine which parts of the cache to keep
 * However, when you call Drop, you do not know if the old pointer is still used.
 * We make have to introduce .Ref() and .DropAndUnref() methods
 * That enable the cache to know when a text pointer is disposed
 * Or maybe we can use the C# dispose mechanic
 */
class PointerFromString : ITextPointer {
  public PointerFromString(string text) {
    Text = text;
    Seen = ImmutableHashSet<Parser>.Empty;
  }

  public PointerFromString(string text, int offset, int line, int column, ImmutableHashSet<Parser> seen) {
    Offset = offset;
    Line = line;
    Column = column;
    Seen = seen;
    Text = text;
  }

  public string Upcoming => SubSequence(5);
  
  public string Text { get; }

  public int Offset { get; }
  public int Line { get; }
  public int Column { get; }
  private ImmutableHashSet<Parser> Seen;
  public bool SeenHere(Parser parser) {
    return Seen.Contains(parser);
  }

  public ITextPointer Add(Parser parser) {
    return new PointerFromString(Text, Offset, Line, Column, Seen.Add(parser));
  }

  public ITextPointer Remove(Parser parser) {
    return new PointerFromString(Text, Offset, Line, Column, Seen.Remove(parser));
  }

  public ITextPointer Drop(int amount) {
    var sequence = SubSequence(amount);
    var lines = sequence.Split("\n");
    return new PointerFromString(Text, Offset + amount, 
      Line + lines.Length - 1, 
      lines.Length > 1 ? lines.Last().Length : Column + amount, 
      ImmutableHashSet<Parser>.Empty);
  }

  public char First => At(0);
  public int Length => Text.Length - Offset;

  public char At(int offset) {
    return Text[Offset + offset];
  }

  public string SubSequence(int length) {
    return Text.Substring(Offset, Math.Min(Length, length));
  }
}

public class SequenceR<TLeft, TRight, T>(Parser<TLeft> first, Parser<TRight> second, Func<TLeft, TRight, T> combine) : Parser<T> {
  
  public Parser<TLeft> First { get; set; } = first;
  public Parser<TRight> Second { get; set; } = second;
  
  public ParseResult<T> Parse(ITextPointer text) {
    var leftResult = First.Parse(text);
    return leftResult.Continue(leftConcrete => {
      var rightResult = Second.Parse(leftConcrete.Remainder);
      return rightResult.Continue(rightConcrete => {
        var value = combine(leftConcrete.Value, rightConcrete.Value);
        return new ConcreteSuccess<T>(value, rightConcrete.Remainder);
      });
    });
  }
}

/// <summary>
/// Prefer the first over the second choice, also when it comes to error messages
/// </summary>
class ChoiceR<T>(Parser<T> first, Parser<T> second): Parser<T> {

  public Parser<T> First { get; set; } = first;
  public Parser<T> Second { get; set; } = second;
  
  public ParseResult<T> Parse(ITextPointer text) {
    var firstResult = First.Parse(text);
    var secondResult = Second.Parse(text);
    return firstResult.Combine(secondResult);
  }
}

class FailR<T>(string expectation) : Parser<T> {
  public ParseResult<T> Parse(ITextPointer text) {
    return text.Fail<T>(expectation);
  }
}

class PositionR : Parser<IPosition> {
  public static readonly PositionR Instance = new();

  private PositionR()
  {
  }

  public ParseResult<IPosition> Parse(ITextPointer text) {
    return new ConcreteSuccess<IPosition>(text, text);
  }
}

class WithRangeR<T, U>(Parser<T> parser, Func<ParseRange, T, U?> map) : Parser<U> {

  public Parser<T> Parser { get; set; } = parser;
  
  public ParseResult<U> Parse(ITextPointer text) {
    var start = text;
    var innerResult = Parser.Parse(text);
    return innerResult.Continue<U>(success => {
      var end = success.Remainder;
      var newValue = map(new ParseRange(start, end), success.Value);
      if (newValue == null) {
        return new FailureResult<U>("Mapping failure", end);
      }
      return new ConcreteSuccess<U>(newValue, success.Remainder);
    });
  }
}

class SkipLeft<T>(VoidParser left, Parser<T> right) : Parser<T> {
  public ParseResult<T> Parse(ITextPointer text) {
    var leftResult = left.Parse(text);
    return leftResult.Continue(leftConcrete => right.Parse(leftConcrete.Remainder));
  }
}

class SkipRight<T>(Parser<T> first, VoidParser second) : Parser<T> {

  public Parser<T> First { get; set; } = first;
  public VoidParser Second { get; set; } = second;
  
  public ParseResult<T> Parse(ITextPointer text) {
    var leftResult = First.Parse(text);
    return leftResult.Continue(leftConcrete => Second.Parse(leftConcrete.Remainder).
      Continue(rightSuccess => leftConcrete with { Remainder = rightSuccess.Remainder }));
  }
}

class TextR(string value) : VoidParser {
  public string Value => value;

  public override string ToString() {
    return Value;
  }

  internal override ParseResult<Unit> Parse(ITextPointer text) {
    var actual = text.SubSequence(value.Length);
    if (actual.Equals(value)) {
      return new ConcreteSuccess<Unit>(Unit.Instance, text.Drop(value.Length));
    }

    return new FailureResult<Unit>($"Expected '{value}' but found '{actual}'", text);
  }
}

internal class Whitespace : Parser<string> {
  public ParseResult<string> Parse(ITextPointer text) {
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
  public ParseResult<string> Parse(ITextPointer text) {
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
  public ParseResult<int> Parse(ITextPointer text) {
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
  public ParseResult<string> Parse(ITextPointer text) {
    var offset = 0;
    var allowDigit = false;
    while (text.Length > offset) {
      var c = text.At(offset);
      if (Char.IsLetter(c)) {
        allowDigit = true;
        offset++;
      }
      else if (allowDigit && Char.IsDigit(c)) {
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
  
  public ParseResult<T> Parse(ITextPointer text) {
    return new ConcreteSuccess<T>(value(), text);
  }
}