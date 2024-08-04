// See https://aka.ms/new-console-template for more information

using System.Collections;
using System.Linq.Expressions;
using CompilerBuilder.Generic;
using Microsoft.Dafny;

namespace CompilerBuilder;

public interface Grammar {
  internal Parser ToGenParser(Func<Grammar, Parser> recurse);
}

public abstract class VoidGrammar : Grammar {
  public static implicit operator VoidGrammar(string keyword) => new TextG(keyword);

  public abstract VoidPrinter ToPrinter();
  public abstract VoidParser ToParser(Func<Grammar, Parser> recurse);
  public Parser ToGenParser(Func<Grammar, Parser> recurse) {
    return ToParser(recurse);
  }
}

public interface Grammar<T> : Grammar {
  internal Printer<T> ToPrinter(Func<Grammar, IPrinter> recurse);

  public Parser<T> ToParser() {
    var map = new Dictionary<Grammar, Parser>();
    Func<Grammar, Parser>? recurse = null;
    recurse = grammar => {
      return map.GetOrCreate(grammar, () => grammar.ToGenParser(recurse!));
    };
    return (Parser<T>)recurse(this);
  }
  
  internal Parser<T> ToParser(Func<Grammar, Parser> recurse);

  Parser Grammar.ToGenParser(Func<Grammar, Parser> recurse) {
    return ToParser(recurse);
  }
}

public class RecursiveG<T>(Func<Grammar<T>> get) : Grammar<T> {
  private Grammar<T>? inner;

  public Grammar<T> Inner => inner ??= get();

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    return new RecursiveW<T>(() => (Printer<T>)recurse(Inner));
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new RecursiveR<T>(() => (Parser<T>)recurse(Inner));
  }
}

class ManyG<T>(Grammar<T> one) : Grammar<List<T>> {
  Printer<List<T>> Grammar<List<T>>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    return new ManyW<T>((Printer<T>)recurse(one));
  }

  Parser<List<T>> Grammar<List<T>>.ToParser(Func<Grammar, Parser> recurse) {
    var oneParser = (Parser<T>)recurse(one);
    return oneParser.Many();
  }
}

public enum Orientation {
  Horizontal,
  Vertical
};

class SkipLeftG<T>(VoidGrammar left, Grammar<T> right, Orientation mode = Orientation.Horizontal) : Grammar<T> {
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    var first = (VoidPrinter)recurse(left);
    var second = (Printer<T>)recurse(right);
    return new SkipLeftW<T>(first, second, mode);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new SkipLeft<T>((VoidParser)recurse(left), (Parser<T>)recurse(right));
  }
}

class SkipRightG<T>(Grammar<T> left, VoidGrammar right, Orientation mode) : Grammar<T> {
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    var first = (Printer<T>)recurse(left);
    var second = (VoidPrinter)recurse(right);
    return new SkipRightW<T>(first, second, mode);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new SkipRight<T>((Parser<T>)recurse(left), (VoidParser)recurse(right));
  }
}
  
class TextG(string value) : VoidGrammar {
  public override VoidPrinter ToPrinter() {
    return new TextW(value);
  }

  public override VoidParser ToParser(Func<Grammar, Parser> recurse) {
    return new TextR(value);
  }
}

internal class NumberG : Grammar<int> {
  Printer<int> Grammar<int>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    return new NumberW();
  }

  Parser<int> Grammar<int>.ToParser(Func<Grammar, Parser> recurse) {
    return new NumberR();
  }
}

internal class IdentifierG : Grammar<string> {
  Printer<string> Grammar<string>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    return Verbatim.Instance;
  }

  Parser<string> Grammar<string>.ToParser(Func<Grammar, Parser> recurse) {
    return new IdentifierR();
  }
}

class WithRangeG<T, U>(Grammar<T> grammar, Func<ParseRange, T, U> map, Func<U, T?> destruct) : Grammar<U> {

  public Grammar<T> Grammar { get; set; } = grammar;

  Printer<U> Grammar<U>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    return ((Printer<T>)recurse(Grammar)).Map(destruct);
  }

  Parser<U> Grammar<U>.ToParser(Func<Grammar, Parser> recurse) {
    return new WithRangeR<T, U>((Parser<T>)recurse(Grammar), map);
  }
}

class Choice<T>(Grammar<T> first, Grammar<T> second) : Grammar<T> {
  public Grammar<T> First { get; set; } = first;
  public Grammar<T> Second { get; set; } = second;
  
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    // Reverse order, on purpose. Needs testing.
    return new ChoiceW<T>((Printer<T>)recurse(Second), (Printer<T>)recurse(First));
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new ChoiceR<T>((Parser<T>)recurse(First), (Parser<T>)recurse(Second));
  }
}

class Value<T>(Func<T> value) : Grammar<T> {
  public T Evaluated => value();

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    return new IgnoreW<T>(Empty.Instance);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new ValueR<T>(value);
  }
}

class ParseOnly<T>(Grammar<T> grammar) : VoidGrammar {
  public override VoidPrinter ToPrinter() {
    return Empty.Instance;
  }

  public override VoidParser ToParser(Func<Grammar, Parser> recurse) {
    return new IgnoreR<T>(grammar.ToParser(recurse));
  }
}

class SequenceG<TLeft, TRight, T>(Grammar<TLeft> left, Grammar<TRight> right, Orientation mode, 
  Func<TLeft, TRight, T> construct, Func<T, (TLeft, TRight)> destruct) : Grammar<T> {

  public Grammar<TLeft> Left { get; set; } = left;
  public Grammar<TRight> Right { get; set; } = right;

  public Orientation Mode => mode;

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    var first = (Printer<TLeft>)recurse(Left);
    var second = (Printer<TRight>)recurse(Right);
    return new SequenceW<TLeft,TRight,T>(first, second, destruct, mode);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    var leftParser = (Parser<TLeft>)recurse(Left);
    var rightParser = (Parser<TRight>)recurse(Right);
    return new SequenceR<TLeft, TRight, T>(leftParser, rightParser, construct);
  }
}

public static class GrammarExtensions {
  public static Grammar<T> Default<T>(this Grammar<T> grammar, Func<T> value) {
    return grammar.Or(GrammarBuilder.Value(value));
  }
  
  public static Grammar<T> OrCast<T, U>(this Grammar<T> grammar, Grammar<U> other)
    where U : T
  {
    return new Choice<T>(grammar, other.UpCast<U, T>());
  }
  
  public static Grammar<T> Or<T>(this Grammar<T> grammar, Grammar<T> other)
  {
    return new Choice<T>(grammar, other);
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

  record Prepend<T>(T Head, IEnumerable<T> Tail) : IEnumerable<T> {
    public IEnumerator<T> GetEnumerator() {
      throw new NotImplementedException();
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }
  }
  
  public static Grammar<List<T>> Many<T>(this Grammar<T> one, Orientation orientation = Orientation.Horizontal) {
    var numerable = GrammarBuilder.Recursive<IEnumerable<T>>(self => 
      GrammarBuilder.Value<IEnumerable<T>>(() => []).Or(one.Then(self, orientation,
        
        (head, tail) => (IEnumerable<T>)new Prepend<T>(head, tail),
        // Reading the code, it seems that l.Skip checks if l is a list, and if so does the optimal thing
        // ReSharper disable once PossibleMultipleEnumeration
        l => (l.First(), l.Skip(1))
      )));
    return numerable.Map(e => e.ToList(), l => l);
  }
  
  public static Grammar<U> Map<T, U>(this Grammar<T> grammar, Func<ParseRange, T,U> construct, 
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
  
  public static Grammar<T> Then<TLeft, TRight, T>(
    this Grammar<TLeft> left, 
    Grammar<TRight> right,
    Orientation mode,
    Func<TLeft, TRight, T> construct,
    Func<T, (TLeft, TRight)> destruct) {
    return new SequenceG<TLeft, TRight, T>(left, right, mode, construct, destruct);
  }
  
  public static Grammar<TContainer> Then<TContainer, TValue>(
    this Grammar<TContainer> containerGrammar, 
    Grammar<TValue> value,
    Func<TContainer, TValue> get,
    Action<TContainer, TValue> set) {
    return new SequenceG<TContainer, TValue, TContainer>(containerGrammar, value, Orientation.Horizontal,
      (c, v) => {
        set(c, v);
        return c;
      }, c => (c, get(c)));
  }
  
  public static Grammar<TContainer> Then<TContainer, TValue>(
    this Grammar<TContainer> containerGrammar, 
    Grammar<TValue> value, 
    Expression<Func<TContainer, TValue>> get, Orientation mode = Orientation.Horizontal) {
    var property = get.GetProperty();
    return containerGrammar.Then(value, property.Get, property.Set);
  }

  public static Grammar<T> SetRange<T>(this Grammar<T> grammar, Action<T, ParseRange> set) {
    return grammar.Map((t, v) => {
      set(v, t);
      return v;
    }, x => x);
  }

  public static Grammar<T?> Option<T>(this Grammar<T> grammar, VoidGrammar fallback) {
    var r = fallback.Then(GrammarBuilder.Value<T?>(default));
    return grammar.Map<T, T?>(t => t, t => t).Or(r);
  }

  public static VoidGrammar Ignore<T>(this Grammar<T> grammar) {
    return new ParseOnly<T>(grammar);
  }
}

class Fail<T> : Grammar<T> {
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    throw new NotImplementedException();
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    throw new NotImplementedException();
  }
}

class ExplicitGrammar<T>(Parser<T> parser, Printer<T> printer) : Grammar<T> {
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, IPrinter> recurse) {
    return printer;
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return parser;
  }
}

public static class GrammarBuilder {

  
  public static Grammar<T> Recursive<T>(Func<Grammar<T>, Grammar<T>> build) {
    Grammar<T>? result = null;
    // ReSharper disable once AccessToModifiedClosure
    result = new RecursiveG<T>(() => {
      var builtInner = build(result!);
      return builtInner;
    });
    return result;
  }
  
  public static Grammar<T> Value<T>(Func<T> value) => new Value<T>(value);
  public static Grammar<T> Constant<T>(T value) => new Value<T>(() => value);
  public static VoidGrammar Keyword(string keyword) => new TextG(keyword);
  public static Grammar<T> Fail<T>() => new Fail<T>();
  public static readonly Grammar<string> Identifier = new IdentifierG();
  public static readonly Grammar<int> Number = new NumberG();
  public static readonly Grammar<string> Whitespace = new ExplicitGrammar<string>(ParserBuilder.Whitespace, Verbatim.Instance);
}
