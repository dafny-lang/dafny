// See https://aka.ms/new-console-template for more information

using System.Collections.Immutable;
using Microsoft.Dafny;

namespace CompilerBuilder;

// trait TextPointer extends OffsetPointer {
//   def safeIncrement: TextPointer = if (atEnd()) this else drop(1)
//   def atEnd(): Boolean = offset == length
//   def head: Char = charAt(offset)
//   def charAt(index: Int): Char
//     def length: Int
//     def end(): TextPointer = drop(length - offset)
//   def charSequence: CharSequence
//     def subSequence(from: Int, until: Int): CharSequence
//     def drop(amount: Int): TextPointer
//     def cache: mutable.HashMap[Any, Any]
//
//   def printRange(end: TextPointer) = subSequence(offset, end.offset).toString
//
// override def toString: String = {
// s"(${lineCharacter.line}, ${lineCharacter.character})" +
// subSequence(Math.max(0, offset - 10), offset) + " | " + subSequence(offset, Math.min(length, offset + 10))
// }
// }
// case class FixPointState(offset: Int, // TODO try to remove this offset, since we can also clear the callStack whenever we move forward.
// stackDepth: Int,
// callStack: Set[BuiltParser[Any]])


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
}

class SequenceR<TContainer>(Parser<TContainer> left, Parser<Action<TContainer>> right) : Parser<TContainer> {
  internal override ParseResult<TContainer> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    var leftResult = left.Parse(text, recursives);
    if (leftResult is SuccessResult<TContainer> leftSuccess) {
      return leftSuccess.Continue(leftConcrete => {

        var rightResult = right.Parse(leftConcrete.Remainder, recursives);
        if (rightResult is SuccessResult<Action<TContainer>> rightSuccess) {
          return rightSuccess.Continue(rightConcrete => {
            rightConcrete.Value(leftConcrete.Value);
            return leftConcrete with { Remainder = rightConcrete.Remainder };
          });
        }

        return rightResult.CastFailure<TContainer>();
      });
    }

    return leftResult.CastFailure<TContainer>();
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
    if (firstResult is not FailureR<T> firstFailure) {
      return firstResult;
    }

    var secondResult = second.Parse(text, recursives);
    if (secondResult is not FailureR<T> secondFailure) {
      return secondResult;
    }

    return firstFailure.Location.Offset > secondFailure.Location.Offset ? firstFailure : secondFailure;
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

class WithRangeR<T, U>(Parser<T> parser, Func<RangeToken, T, U> map) : Parser<U> {
  internal override void Schedule(ParseState state) {
    state.Todos.Push(() => {
      var end = (IToken)state.Results.Pop();
      var result = (T)state.Results.Pop();
      var start = (IToken)state.Results.Pop();
      var range = new RangeToken(start, end);
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

    return new FailureR<Unit>($"Expected {value} but found {actual}", text);
  }
}

internal class NumberR : Parser<int>;

internal class IdentifierR : Parser<string>;

class ValueR<T>(T value) : Parser<T> {
  internal override ParseResult<T> Parse(ITextPointer text, ImmutableHashSet<Parser> recursives) {
    return new ConcreteSuccess<T>(value, text);
  }
}

class ManyR<T>(Parser<T> one) : Parser<List<T>>;

public static class ParserExtensions {
  public static Parser<T> InBraces<T>(this Parser<T> parser) {
    return ParserBuilder.Keyword("{").Then(parser).Then("}");
  }  
  
  public static Parser<T> Then<T>(this Parser<T> left, VoidParser right) {
    return new SkipRight<T>(left, right);
  }  
  
  public static Parser<T> Then<T>(this VoidParser left, Parser<T> right) {
    return new SkipLeft<T>(left, right);
  }
  public static Parser<List<T>> Many<T>(this Parser<T> one) {
    return new ManyR<T>(one);
  }
  
  public static Parser<U> Map<T, U>(this Parser<T> parser, Func<RangeToken, T,U> map) {
    return new WithRangeR<T, U>(parser, map);
  }
  
  public static Parser<U> Map<T, U>(this Parser<T> parser, Func<T,U> map) {
    return new WithRangeR<T, U>(parser, (_, original) => map(original));
  }

  public static Parser<TContainer> Then<TContainer, TValue>(
    this Parser<TContainer> containerParser, 
    Parser<TValue> value, 
    Action<TContainer, TValue> set) {
    var right = value.Map<TValue, Action<TContainer>>(v => container => set(container, v));
    return new SequenceR<TContainer>(containerParser, right);
  }
}

public static class ParserBuilder {

  public static Parser<T> Value<T>(T value) => new ValueR<T>(value);
  public static VoidParser Keyword(string keyword) => new TextR(keyword);
  public static readonly Parser<string> Identifier = new IdentifierR();
  public static readonly Parser<int> Number = new NumberR();
}
