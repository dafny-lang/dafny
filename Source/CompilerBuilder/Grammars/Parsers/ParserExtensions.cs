using Microsoft.Dafny;

namespace CompilerBuilder;

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
  
  public static Parser<T> Or<T>(this Parser<T> left, Parser<T> right) {
    return new ChoiceR<T>(left, right);
  }

  public static Parser<List<T>> Many<T>(this Parser<T> one) {
    Parser<List<T>>? many = null;
    many = new RecursiveR<List<T>>(() => {
      return ParserBuilder.Value(new List<T>()).Or(many!.Then(one, (l, e) => l.Add(e)));
    });
    return many;
  }
  
  public static Parser<U> Map<T, U>(this Parser<T> parser, Func<ParseRange, T,U> map) {
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