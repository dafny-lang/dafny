// See https://aka.ms/new-console-template for more information

using System.Linq.Expressions;
using Microsoft.Dafny;

namespace CompilerBuilder;

public interface IGrammar;

public abstract class VoidGrammar : IGrammar {
  public static implicit operator VoidGrammar(string keyword) => new TextG(keyword);

  public abstract VoidPrinter ToPrinter();
  public abstract VoidParser ToParser();
}

public interface Grammar<T> : IGrammar {
  public Printer<T> ToPrinter(Func<IGrammar, IPrinter> recurse);
  public Parser<T> ToParser(Func<IGrammar, IParser> recurse);
}

public class Recursive<T>(Func<Grammar<T>> get) : Grammar<T> {
  public Printer<T> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    return new RecursiveW<T>(() => (Printer<T>)recurse(get()));
  }

  public Parser<T> ToParser(Func<IGrammar, IParser> recurse) {
    return new RecursiveR<T>(() => (Parser<T>)recurse(get()));
  }
}

class ManyG<T>(Grammar<T> one) : Grammar<List<T>> {
  public Printer<List<T>> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    return new ManyW<T>((Printer<T>)recurse(one));
  }

  public Parser<List<T>> ToParser(Func<IGrammar, IParser> recurse) {
    return new ManyR<T>((Parser<T>)recurse(one));
  }
}

public enum Orientation {
  Horizontal,
  Vertical
};

class SkipLeftG<T>(VoidGrammar left, Grammar<T> right, Orientation mode) : Grammar<T> {
  public Printer<T> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    var first = new Ignore<T>((VoidPrinter)recurse(left));
    var second = (Printer<T>)recurse(right);
    return mode == Orientation.Horizontal 
      ? new LeftRight<T>(first, second) 
      : new TopBottom<T>(first, second);
  }

  public Parser<T> ToParser(Func<IGrammar, IParser> recurse) {
    return new SkipLeft<T>((VoidParser)recurse(left), (Parser<T>)recurse(right));
  }
}

class SkipRightG<T>(Grammar<T> left, VoidGrammar right, Orientation mode) : Grammar<T> {
  public Printer<T> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    var leftPrinter = (Printer<T>)recurse(left);
    var rightPrinter = new Ignore<T>((VoidPrinter)recurse(right));
    return mode == Orientation.Horizontal 
      ? new LeftRight<T>(leftPrinter, rightPrinter) 
      : new TopBottom<T>(leftPrinter, rightPrinter);
  }

  public Parser<T> ToParser(Func<IGrammar, IParser> recurse) {
    return new SkipRight<T>((Parser<T>)recurse(left), (VoidParser)recurse(right));
  }
}
  
class TextG(string value) : VoidGrammar {
  public override VoidPrinter ToPrinter() {
    return new TextW(value);
  }

  public override VoidParser ToParser() {
    return new TextR(value);
  }
}

internal class NumberG : Grammar<int> {
  public Printer<int> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    return new NumberW();
  }

  public Parser<int> ToParser(Func<IGrammar, IParser> recurse) {
    return new NumberR();
  }
}

internal class IdentifierG : Grammar<string> {
  public Printer<string> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    return new Verbatim();
  }

  public Parser<string> ToParser(Func<IGrammar, IParser> recurse) {
    return new IdentifierR();
  }
}

class WithRangeG<T, U>(Grammar<T> grammar, Func<RangeToken, T, U> map, Func<U, T?> destruct) : Grammar<U> {
  public Printer<U> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    return ((Printer<T>)recurse(grammar)).Map(destruct);
  }

  public Parser<U> ToParser(Func<IGrammar, IParser> recurse) {
    return new WithRangeR<T, U>((Parser<T>)recurse(grammar), map);
  }
}

class Choice<T>(Grammar<T> first, Grammar<T> second) : Grammar<T> {
  public Printer<T> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    // Reverse order, on purpose. Needs testing.
    return new ChoiceW<T>((Printer<T>)recurse(second), (Printer<T>)recurse(first));
  }

  public Parser<T> ToParser(Func<IGrammar, IParser> recurse) {
    return new ChoiceR<T>((Parser<T>)recurse(first), (Parser<T>)recurse(second));
  }
}

class Value<T>(T value) : Grammar<T> {
  public Printer<T> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    return new Ignore<T>(new Empty());
  }

  public Parser<T> ToParser(Func<IGrammar, IParser> recurse) {
    return new ValueR<T>(value);
  }
}

class SequenceG<TContainer, TValue>(Grammar<TContainer> left, Grammar<TValue> right, Orientation mode, 
  Action<TContainer, TValue> setter, Func<TContainer, TValue> getter) : Grammar<TContainer> {
  public Printer<TContainer> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    var first = (Printer<TContainer>)recurse(left);
    var second = ((Printer<TValue>)recurse(right)).Map(getter);
    return mode == Orientation.Horizontal 
      ? new LeftRight<TContainer>(first, second) 
      : new TopBottom<TContainer>(first, second);
  }

  public Parser<TContainer> ToParser(Func<IGrammar, IParser> recurse) {
    return new SequenceR<TContainer>((Parser<TContainer>)recurse(left), 
      ((Parser<TValue>)recurse(right)).Map<TValue, Action<TContainer>>(v =>
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
    return GrammarBuilder.Keyword("{").Then(grammar, Orientation.Vertical).Then("}", Orientation.Vertical);
  }  
  
  public static Grammar<T> Then<T>(this Grammar<T> left, VoidGrammar right, Orientation mode = Orientation.Horizontal) {
    return new SkipRightG<T>(left, right, Orientation.Horizontal);
  }  
  
  public static Grammar<T> Then<T>(this VoidGrammar left, Grammar<T> right, Orientation mode = Orientation.Horizontal) {
    return new SkipLeftG<T>(left, right, Orientation.Horizontal);
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
    return new SequenceG<TContainer, TValue>(containerGrammar, value, Orientation.Horizontal, set, get);
  }
  
  public static Grammar<TContainer> Then<TContainer, TValue>(
    this Grammar<TContainer> containerGrammar, 
    Grammar<TValue> value, 
    Expression<Func<TContainer, TValue>> get, Orientation mode = Orientation.Horizontal) {
    Func<TContainer, TValue> getter = null; 
    Action<TContainer, TValue> setter = null;
    return containerGrammar.Then(value, getter, setter);
  }

  public static Grammar<T> SetRange<T>(this Grammar<T> grammar, Action<T, RangeToken> set) {
    return grammar.Map((t, v) => {
      set(v, t);
      return v;
    }, x => x);
  }

  public static Grammar<T?> Option<T>(this Grammar<T> grammar, VoidGrammar fallback) {
    var r = fallback.Then(GrammarBuilder.Value<T?>(default));
    return grammar.Map<T, T?>(t => t, t => t).Or(r);
  }
}

class Fail<T> : Grammar<T> {
  public Printer<T> ToPrinter(Func<IGrammar, IPrinter> recurse) {
    throw new NotImplementedException();
  }

  public Parser<T> ToParser(Func<IGrammar, IParser> recurse) {
    throw new NotImplementedException();
  }
}

public static class GrammarBuilder {

  public static Grammar<T> Value<T>(T value) => new Value<T>(value);
  public static VoidGrammar Keyword(string keyword) => new TextG(keyword);
  public static Grammar<T> Fail<T>() => new Fail<T>();
  public static readonly Grammar<string> Identifier = new IdentifierG();
  public static readonly Grammar<int> Number = new NumberG();
}
