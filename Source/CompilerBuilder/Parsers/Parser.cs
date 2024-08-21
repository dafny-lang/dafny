using System.Diagnostics;
using System.Text.RegularExpressions;

namespace CompilerBuilder;

public record Unit {
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
    return text.ParseWithCache(parser).Continue(
      s => new ConcreteSuccess<Unit>(Unit.Instance, s.Remainder));
  }
}

public abstract class Parser
{
  public override string ToString() {
    return "Parser";
  }
}

public abstract class Parser<T> : Parser
{
  public abstract ParseResult<T> Parse(ITextPointer text);

  public ConcreteResult<T> Parse(string text) {
    ITextPointer pointer = new PointerFromString(text);
    var withEnd = new EndOfText<T>(this);
    return withEnd.Parse(pointer).Concrete!;
  }
}

class EndOfText<T>(Parser<T> inner) : Parser<T> {
  public override ParseResult<T> Parse(ITextPointer text) {
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

public class SequenceR<TLeft, TRight, T>(Parser<TLeft> first, Parser<TRight> second, Func<TLeft, TRight, T> combine) : Parser<T> {
  
  public Parser<TLeft> First { get; set; } = first;
  public Parser<TRight> Second { get; set; } = second;
  
  public override ParseResult<T> Parse(ITextPointer text) {
    var leftResult = text.ParseWithCache(First);
    return leftResult.Continue(leftConcrete => {
      var rightResult = leftConcrete.Remainder.ParseWithCache(Second);
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
  
  public override ParseResult<T> Parse(ITextPointer text) {
    text.Ref();
    var firstResult = text.ParseWithCache(First);
    text.UnRef();
    var secondResult = text.ParseWithCache(Second);
    return firstResult.Combine(secondResult);
  }
}

class FailR<T>(string expectation) : Parser<T> {
  public override ParseResult<T> Parse(ITextPointer text) {
    return text.Fail<T>(expectation);
  }
}

class PositionR : Parser<IPosition> {
  public static readonly PositionR Instance = new();

  private PositionR()
  {
  }

  public override ParseResult<IPosition> Parse(ITextPointer text) {
    return new ConcreteSuccess<IPosition>(text, text);
  }
}

class WithRangeR<T, U>(Parser<T> parser, Func<ParseRange, T, MapResult<U>> map) : Parser<U> {

  public Parser<T> Parser { get; set; } = parser;
  
  public override ParseResult<U> Parse(ITextPointer text) {
    var start = text;
    var innerResult = text.ParseWithCache(Parser);
    return innerResult.Continue<U>(success => {
      var end = success.Remainder;
      var newValue = map(new ParseRange(start, end), success.Value);
      if (newValue is MapSuccess<U> s) {
        return new ConcreteSuccess<U>(s.Value, success.Remainder);
      }
      return new FailureResult<U>("Mapping failure", end);
    });
  }
}

class SkipLeft<T>(VoidParser left, Parser<T> right) : Parser<T> {
  public override ParseResult<T> Parse(ITextPointer text) {
    var leftResult = text.ParseWithCache(left);
    return leftResult.Continue(leftConcrete => leftConcrete.Remainder.ParseWithCache(right));
  }
}

class SkipRight<T>(Parser<T> first, VoidParser second) : Parser<T> {

  public Parser<T> First { get; set; } = first;
  public VoidParser Second { get; set; } = second;
  
  public override ParseResult<T> Parse(ITextPointer text) {
    var leftResult = text.ParseWithCache(First);
    return leftResult.Continue(leftConcrete => leftConcrete.Remainder.ParseWithCache(Second).
      Continue(rightSuccess => leftConcrete with { Remainder = rightSuccess.Remainder }));
  }
}

class TextR(string value) : VoidParser {
  public string Value => value;

  public override string ToString() {
    return Value;
  }

  internal override ParseResult<Unit> Parse(ITextPointer text) {
    var actual = text.SubSequence(value.Length).ToString();
    if (actual.Equals(value)) {
      return new ConcreteSuccess<Unit>(Unit.Instance, text.Drop(value.Length));
    }

    return new FailureResult<Unit>($"Expected '{value}' but found '{text.LocationDescription}'", text);
  }
}

class RegexR(string regex, string description) : Parser<string> {
  private Regex r = new("^" + regex);
  public override ParseResult<string> Parse(ITextPointer text) {
    var matches = r.EnumerateMatches(text.Remainder);
    while (matches.MoveNext()) {
      var match = matches.Current;
      Debug.Assert(match.Index == 0);
      var remainder = text.Drop(match.Length);
      return new ConcreteSuccess<string>(text.SubSequence(match.Length).ToString(), remainder);
    }

    return text.Fail<string>(description);
  }
}

internal class Whitespace : Parser<string> {
  public override ParseResult<string> Parse(ITextPointer text) {
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
      return new ConcreteSuccess<string>(result.ToString(), text.Drop(offset));
    }

    return text.Fail<string>("whitespace");
  }
}

internal class Comment(string opener, string closer, string description) : Parser<string> {
  bool Find(string expectation, ITextPointer text, int offset = 0) {
    if (text.Length < expectation.Length) {
      return false;
    }
    
    for (int index = 0; index < expectation.Length; index++) {
      if (text.At(offset + index) != expectation[index]) {
        return false;
      }
    }

    return true;
  }
  
  public override ParseResult<string> Parse(ITextPointer text) {
    if (!Find(opener, text)) {
      return text.Fail<string>(description);
    }

    bool foundExit = false;
    int offset = opener.Length;
    while (text.Length > offset) {
      if (Find(closer, text, offset)) {
        foundExit = true;
        offset += closer.Length;
        break;
      }

      offset++;
    }

    if (foundExit) {
      var comment = text.SubSequence(offset);
      return new ConcreteSuccess<string>(comment.ToString(), text.Drop(offset));
    }

    return text.Fail<string>(description);
  }
}

internal class NumberR : Parser<int> {
  public override ParseResult<int> Parse(ITextPointer text) {
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
  public override ParseResult<string> Parse(ITextPointer text) {
    var offset = 0;
    var allowOthers = false;
    while (text.Length > offset) {
      var c = text.At(offset);
      if (Char.IsLetter(c)) {
        allowOthers = true;
        offset++;
      }
      else if (allowOthers && (char.IsDigit(c) || c == '\'') || c == '_') {
        offset++;
      } else {
        break;
      }
    }

    if (offset > 0) {
      var sequence = text.SubSequence(offset).ToString();
      return new ConcreteSuccess<string>(sequence, text.Drop(offset));
    }

    return text.Fail<string>("an identifier");
  }
}

class ValueR<T>(Func<T> value) : Parser<T> {
  public T Evaluated => value();
  
  public override ParseResult<T> Parse(ITextPointer text) {
    return new ConcreteSuccess<T>(value(), text);
  }
}