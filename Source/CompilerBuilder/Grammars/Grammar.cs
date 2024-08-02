// See https://aka.ms/new-console-template for more information

using System.Linq.Expressions;
using Microsoft.Dafny;

namespace CompilerBuilder;

public abstract class Grammar {
  public static implicit operator Grammar(string keyword) => new TextG(keyword);

  public abstract Printer ToPrinter();
  public abstract Parser ToParser();
}

public interface Grammar<T> {
  public Printer<T> ToPrinter();
  public Parser<T> ToParser();
}

public class Recursive<T>(Func<Grammar<T>> get) : Grammar<T>;

class ManyG<T>(Grammar<T> one) : Grammar<List<T>> {
  public Printer<List<T>> ToPrinter() {
    return new ManyW<T>(one.ToPrinter());
  }

  public Parser<List<T>> ToParser() {
    return new ManyR<T>(one.ToParser());
  }
}

class SkipLeftG<T>(Grammar left, Grammar<T> right) : Grammar<T> {
  public Printer<T> ToPrinter() {
    return new SequenceW<T>(new Ignore<T>(left.ToPrinter()), right.ToPrinter());
  }

  public Parser<T> ToParser() {
    return new SkipLeft<T>(left.ToParser(), right.ToParser());
  }
}

class SkipRightG<T>(Grammar<T> left, Grammar right) : Grammar<T> {
  
  public Printer<T> ToPrinter() {
    return new SequenceW<T>(left.ToPrinter(), new Ignore<T>(right.ToPrinter()));
  }

  public Parser<T> ToParser() {
    return new SkipRight<T>(left.ToParser(), right.ToParser());
  }
}
  
class TextG(string value) : Grammar {
  public override Printer ToPrinter() {
    return new TextW(value);
  }

  public override Parser ToParser() {
    return new TextR(value);
  }
}

internal class NumberG : Grammar<int> {
  public Printer<int> ToPrinter() {
    return new NumberW();
  }

  public Parser<int> ToParser() {
    return new NumberR();
  }
}

internal class IdentifierG : Grammar<string> {
  public Printer<string> ToPrinter() {
    return new Verbatim();
  }

  public Parser<string> ToParser() {
    return new IdentifierR();
  }
}

class WithRangeG<T, U>(Grammar<T> grammar, Func<RangeToken, T, U> map, Func<U, T?> destruct) : Grammar<U> {
  public Printer<U> ToPrinter() {
    return grammar.ToPrinter().Map(destruct);
  }

  public Parser<U> ToParser() {
    return new WithRangeR<T, U>(grammar.ToParser(), map);
  }
}

class Choice<T>(Grammar<T> first, Grammar<T> second) : Grammar<T> {
  public Printer<T> ToPrinter() {
    // Reverse order, on purpose. Needs testing.
    return new ChoiceW<T>(second.ToPrinter(), first.ToPrinter());
  }

  public Parser<T> ToParser() {
    return new ChoiceR<T>(first.ToParser(), second.ToParser());
  }
}

class Value<T>(T value) : Grammar<T> {
  public Printer<T> ToPrinter() {
    return new Ignore<T>(new Empty());
  }

  public Parser<T> ToParser() {
    return new ValueR<T>(value);
  }
}

class SequenceG<TContainer, TValue>(Grammar<TContainer> left, Grammar<TValue> right, 
  Action<TContainer, TValue> setter, Func<TContainer, TValue> getter) : Grammar<TContainer> {
  public Printer<TContainer> ToPrinter() {
    return new SequenceW<TContainer>(left.ToPrinter(), right.ToPrinter().Map(getter));
  }

  public Parser<TContainer> ToParser() {
    return new SequenceR<TContainer>(left.ToParser(), right.ToParser().Map<TValue, Action<TContainer>>(v =>
      container => setter(container, v)));
  }
}

public static class GrammarExtensions {
  public static Grammar<T> Default<T>(this Grammar<T> grammar, T value) {
    return grammar.Or(GrammarBuilder.Value(value));
  }
  
  public static Grammar<T> Or<T, U>(this Grammar<T> grammar, Grammar<U> other) 
    where U : T
  {
    return new Choice<T>(grammar, other.UpCast<U, T>());
  }
  
  public static Grammar<T> InParens<T>(this Grammar<T> grammar) {
    return GrammarBuilder.Keyword("(").Then(grammar).Then(")");
  }  
  
  public static Grammar<T> InBraces<T>(this Grammar<T> grammar) {
    return GrammarBuilder.Keyword("{").Then(grammar).Then("}");
  }  
  
  public static Grammar<T> Then<T>(this Grammar<T> left, Grammar right) {
    return new SkipRightG<T>(left, right);
  }  
  
  public static Grammar<T> Then<T>(this Grammar left, Grammar<T> right) {
    return new SkipLeftG<T>(left, right);
  }
  public static Grammar<List<T>> Many<T>(this Grammar<T> one) {
    return new ManyG<T>(one);
  }
  
  public static Grammar<U> Map<T, U>(this Grammar<T> grammar, Func<RangeToken, T,U> construct, 
    Func<U, T?> destruct) {
    return new WithRangeG<T, U>(grammar, construct, destruct);
  }
  
  public static Grammar<TSuper> UpCast<TSub, TSuper>(this Grammar<TSub> grammar)
    where TSub : TSuper
  {
    return grammar.Map<TSub, TSuper>(t => t, u => u is TSub t ? t : default);
  }
  
  public static Grammar<U> Map<T, U>(this Grammar<T> grammar, Func<T,U> construct, Func<U, T?> destruct) {
    return new WithRangeG<T, U>(grammar, (_, original) => construct(original), destruct);
  }
  
  public static Grammar<List<T>> OptionToList<T>(this Grammar<T?> grammar) {
    return grammar.Map(o => o == null ? new List<T>() : new List<T>() { o },
      l => l.FirstOrDefault());
  }
  
  public static Grammar<TContainer> Then<TContainer, TValue>(
    this Grammar<TContainer> containerGrammar, 
    Grammar<TValue> value,
    Func<TContainer, TValue> get,
    Action<TContainer, TValue> set) {
    return new SequenceG<TContainer, TValue>(containerGrammar, value, set, get);
  }
  
  public static Grammar<TContainer> Then<TContainer, TValue>(
    this Grammar<TContainer> containerGrammar, 
    Grammar<TValue> value, 
    Expression<Func<TContainer, TValue>> get) {
    throw new Exception("magic");
    //return new SequenceG<TContainer, TValue>(containerGrammar, value, set, get);
  }

  public static Grammar<T> SetRange<T>(this Grammar<T> grammar, Action<T, RangeToken> set) {
    return grammar.Map((t, v) => {
      set(v, t);
      return v;
    }, x => x);
  }

  public static Grammar<T?> Option<T>(this Grammar<T> grammar, Grammar fallback) {
    var r = fallback.Then(GrammarBuilder.Value<T?>(default));
    return grammar.Map<T, T?>(t => t, t => t).Or(r);
  }
}

public static class GrammarBuilder {

  public static Grammar<T> Value<T>(T value) => new Value<T>(value);
  public static Grammar Keyword(string keyword) => new TextG(keyword);
  public static Grammar<T> Fail<T>() => new TextG(keyword);
  public static readonly Grammar<string> Identifier = new IdentifierG();
  public static readonly Grammar<int> Number = new NumberG();
}
