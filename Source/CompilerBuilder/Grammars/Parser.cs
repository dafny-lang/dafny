// See https://aka.ms/new-console-template for more information

using System.Net.Http.Headers;
using Microsoft.Dafny;

namespace CompilerBuilder;

public abstract class Parser {
  public static implicit operator Parser(string keyword) => new TextR(keyword);
}

public interface Parser<T>;

class ManyR<T>(Parser<T> one) : Parser<List<T>>;

class SkipLeft<T>(Parser left, Parser<T> right) : Parser<T>;

class SkipRight<T>(Parser<T> left, Parser right) : Parser<T>;
  
class TextR(string value) : Parser;

internal class NumberR : Parser<int>;

internal class IdentifierR : Parser<string>;

class WithRangeR<T, U>(Parser<T> parser, Func<RangeToken, T, U> map) : Parser<U>;

class ValueR<T>(T value) : Parser<T>;

class SequenceR<TContainer>(Parser<TContainer> left, Parser<Action<TContainer>> right) : Parser<TContainer>;

public static class ParserExtensions {
  public static Parser<T> InBraces<T>(this Parser<T> parser) {
    return ParserBuilder.Keyword("{").Then(parser).Then("}");
  }  
  
  public static Parser<T> Then<T>(this Parser<T> left, Parser right) {
    return new SkipRight<T>(left, right);
  }  
  
  public static Parser<T> Then<T>(this Parser left, Parser<T> right) {
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
  public static Parser Keyword(string keyword) => new TextR(keyword);
  public static readonly Parser<string> Identifier = new IdentifierR();
  public static readonly Parser<int> Number = new NumberR();
}
