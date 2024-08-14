// See https://aka.ms/new-console-template for more information

using System.Collections;
using System.Linq.Expressions;
using CompilerBuilder.Generic;
using Microsoft.Dafny;

namespace CompilerBuilder;

public interface Grammar {
  internal Parser ToGenParser(Func<Grammar, Parser> recurse);
  internal Printer ToGenPrinter(Func<Grammar, Printer> recurse);
  
  public IEnumerable<Grammar> Children { get; }

  public IEnumerable<Grammar> SelfAndDescendants {
    get {
      var visited = new HashSet<Grammar>();
      var toVisit = new Stack<Grammar>();
      var result = new List<Grammar>();
      toVisit.Push(this);
      while (toVisit.Any()) {
        var current = toVisit.Pop();
        if (!visited.Add(current)) {
          continue;
        }

        result.Add(current);
        foreach (var child in current.Children.Reverse()) {
          toVisit.Push(child);
        }
      }
      return result;
    }
  }
}

public abstract class VoidGrammar : Grammar {
  public static implicit operator VoidGrammar(string keyword) => new TextG(keyword);

  public abstract VoidPrinter ToPrinter(Func<Grammar, Printer> recurse);
  public abstract VoidParser ToParser(Func<Grammar, Parser> recurse);
  public Parser ToGenParser(Func<Grammar, Parser> recurse) {
    return ToParser(recurse);
  }

  public Printer ToGenPrinter(Func<Grammar, Printer> recurse) {
    return ToPrinter(recurse);
  }

  public abstract IEnumerable<Grammar> Children { get; }
}

record IndentG<T>(Grammar<T> Inner, int Amount) : Grammar<T> {

  public IEnumerable<Grammar> Children => Inner.Children;
  public Printer<T> ToPrinter(Func<Grammar, Printer> recurse) {
    return new IndentW<T>((Printer<T>)recurse(Inner), Amount);
  }

  public Parser<T> ToParser(Func<Grammar, Parser> recurse) {
    return Inner.ToParser(recurse);
  }
}
public interface Grammar<T> : Grammar {
  internal Printer<T> ToPrinter(Func<Grammar, Printer> recurse);

  public Parser<T> ToParser() {
    var map = new Dictionary<Grammar, Parser>();
    Func<Grammar, Parser>? recurse = null;
    recurse = grammar => {
      return map.GetOrCreate(grammar, () => grammar.ToGenParser(recurse!));
    };
    return (Parser<T>)recurse(this);
  }
  
  public Printer<T> ToPrinter() {
    var map = new Dictionary<Grammar, Printer>();
    Func<Grammar, Printer>? recurse = null;
    recurse = grammar => {
      return map.GetOrCreate(grammar, () => grammar.ToGenPrinter(recurse!));
    };
    return (Printer<T>)recurse(this);
  }
  
  internal Parser<T> ToParser(Func<Grammar, Parser> recurse);

  Parser Grammar.ToGenParser(Func<Grammar, Parser> recurse) {
    return ToParser(recurse);
  }
  
  Printer Grammar.ToGenPrinter(Func<Grammar, Printer> recurse) {
    return ToPrinter(recurse);
  }
}

public class RecursiveG<T>(Func<Grammar<T>> get) : Grammar<T> {
  private Grammar<T>? inner;

  public Grammar<T> Inner => inner ??= get();

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    return new RecursiveW<T>(() => (Printer<T>)recurse(Inner));
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new RecursiveR<T>(() => (Parser<T>)recurse(Inner));
  }

  public IEnumerable<Grammar> Children => [Inner];
}
  
class TextG(string value) : VoidGrammar {
  public string Value => value;

  public override VoidPrinter ToPrinter(Func<Grammar, Printer> recurse) {
    return new TextW(value);
  }

  public override VoidParser ToParser(Func<Grammar, Parser> recurse) {
    return new TextR(value);
  }

  public override IEnumerable<Grammar> Children => [];

  public override string ToString() {
    return Value;
  }
}

internal class NumberG : Grammar<int> {
  Printer<int> Grammar<int>.ToPrinter(Func<Grammar, Printer> recurse) {
    return new NumberW();
  }

  Parser<int> Grammar<int>.ToParser(Func<Grammar, Parser> recurse) {
    return new NumberR();
  }

  public IEnumerable<Grammar> Children => [];
}

internal class IdentifierG : Grammar<string> {
  Printer<string> Grammar<string>.ToPrinter(Func<Grammar, Printer> recurse) {
    return VerbatimW.Instance;
  }

  Parser<string> Grammar<string>.ToParser(Func<Grammar, Parser> recurse) {
    return new IdentifierR();
  }

  public IEnumerable<Grammar> Children => [];
}

class WithRangeG<T, U>(Grammar<T> grammar, Func<ParseRange, T, U?> construct, Func<U, MapResult<T>> destruct) : Grammar<U> {

  public Grammar<T> Grammar { get; set; } = grammar;

  Printer<U> Grammar<U>.ToPrinter(Func<Grammar, Printer> recurse) {
    return ((Printer<T>)recurse(Grammar)).Map(destruct);
  }

  Parser<U> Grammar<U>.ToParser(Func<Grammar, Parser> recurse) {
    return new WithRangeR<T, U>((Parser<T>)recurse(Grammar), construct);
  }

  public IEnumerable<Grammar> Children => [Grammar];
}

class Choice<T>(Grammar<T> first, Grammar<T> second) : Grammar<T> {
  public Grammar<T> First { get; set; } = first;
  public Grammar<T> Second { get; set; } = second;
  
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    // Reverse order, on purpose. Needs testing.
    return new ChoiceW<T>((Printer<T>)recurse(Second), (Printer<T>)recurse(First));
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new ChoiceR<T>((Parser<T>)recurse(First), (Parser<T>)recurse(Second));
  }

  public IEnumerable<Grammar> Children => [First, Second];
}

class Constructor<T>(Func<T> construct) : Grammar<T> {

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    return new IgnoreW<T>(EmptyW.Instance);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new ValueR<T>(construct);
  }

  public IEnumerable<Grammar> Children => [];
}

class Value<T>(T value) : Grammar<T> {

  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    return new ValueW<T>(value, EmptyW.Instance);
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new ValueR<T>(() => value);
  }

  public IEnumerable<Grammar> Children => [];
}

class ParseOnly<T>(Grammar<T> grammar) : VoidGrammar {
  public override VoidPrinter ToPrinter(Func<Grammar, Printer> recurse) {
    return EmptyW.Instance;
  }

  public override VoidParser ToParser(Func<Grammar, Parser> recurse) {
    return new IgnoreR<T>(grammar.ToParser(recurse));
  }

  public override IEnumerable<Grammar> Children => grammar.Children;
}

public static class GrammarExtensions {
  public static Grammar<T> Default<T>(this Grammar<T> grammar, T value) {
    return grammar.Or(GrammarBuilder.Constant(value));
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
    return GrammarBuilder.Keyword("(").Then(grammar, Separator.Nothing).Then(")", Separator.Nothing);
  }  
  
  public static Grammar<T> InBraces<T>(this Grammar<T> grammar, bool indent = true) {
    var inner = indent ? new IndentG<T>(grammar, 1) : grammar;
    return GrammarBuilder.Keyword("{").Then(inner, Separator.Linebreak).Then("}", Separator.Linebreak);
  }  
  
  public static Grammar<T> Then<T>(this Grammar<T> left, VoidGrammar right, Separator mode = Separator.Space) {
    return new SkipRightG<T>(left, right, mode);
  }  
  
  public static Grammar<T> Then<T>(this VoidGrammar left, Grammar<T> right, Separator mode = Separator.Space) {
    return new SkipLeftG<T>(left, right, mode);
  }
  
  public static Grammar<List<T>> CommaSeparated<T>(this Grammar<T> inner) {
    return inner.Separated(",", Separator.Nothing);
  }
  
  public static Grammar<List<T>> Separated<T>(this Grammar<T> inner, VoidGrammar separator, 
    Separator beforeSep = Separator.Space, 
    Separator afterSep = Separator.Space) {
    var r = ManyInner(inner.Then(separator, beforeSep), afterSep).Then<SinglyLinkedList<T>, T, SinglyLinkedList<T>>(
      inner, afterSep, 
      (l, e) => new Cons<T>(e, l), 
      l => l.Fold((head, tail) => (tail, head), () => ((SinglyLinkedList<T>, T)?)null));
    return r.Map(e => e.ToList(), l => new LinkedListFromList<T>(l));
  }
  
  public static Grammar<List<T>> Many<T>(this Grammar<T> one, Separator separator = Separator.Space) {
    var numerable = ManyInner(one, separator);
    return numerable.Map(e => e.ToList(), l => new LinkedListFromList<T>(l));
  }

  private static Grammar<SinglyLinkedList<T>> ManyInner<T>(Grammar<T> one, Separator separator)
  {
    return GrammarBuilder.Recursive<SinglyLinkedList<T>>(self => 
      new Constructor<SinglyLinkedList<T>>(() => new Nil<T>()).Or(one.Then(self, separator,
        
        (head, tail) => (SinglyLinkedList<T>)new Cons<T>(head, tail),
        // Reading the code, it seems that l.Skip checks if l is a list, and if so does the optimal thing
        // ReSharper disable once PossibleMultipleEnumeration
        l => l.Fold((head, tail) => (head, tail), () => ((T,SinglyLinkedList<T>)?)null))));
  }

  public static Grammar<U> Map<T, U>(this Grammar<T> grammar, Func<ParseRange, T,U> construct, 
    Func<U, T> destruct) {
    return new WithRangeG<T, U>(grammar, construct, v => new MapSuccess<T>(destruct(v)));
  }
  
  public static Grammar<U> Map<T, U>(this Grammar<T> grammar, Func<ParseRange, T,U> construct, 
    Func<U, MapResult<T>> destruct) {
    return new WithRangeG<T, U>(grammar, construct, destruct);
  }
  
  public static Grammar<TSub> DownCast<TSuper, TSub>(this Grammar<TSuper> grammar)
    where TSub : class, TSuper
  {
    return grammar.Map<TSuper, TSub>(t => t as TSub, u => new MapSuccess<TSuper>(u));
  }
  
  public static Grammar<TSuper> UpCast<TSub, TSuper>(this Grammar<TSub> grammar)
    where TSub : TSuper
  {
    return grammar.Map<TSub, TSuper>(t => t, 
      u => u is TSub t ? new MapSuccess<TSub>(t) : new MapFail<TSub>());
  }
  
  
  public static Grammar<U> Map<T, U>(this Grammar<T> grammar, Func<T,U?> construct, Func<U, T> destruct) {
    return new WithRangeG<T, U>(grammar, (_, original) => construct(original), 
      v => new MapSuccess<T>(destruct(v)));
  }
  
  public static Grammar<U> Map<T, U>(this Grammar<T> grammar, Func<T,U?> construct, Func<U, MapResult<T>> destruct) {
    return new WithRangeG<T, U>(grammar, (_, original) => construct(original), destruct);
  }
  
  
  public static Grammar<List<U>> Singleton<T, U>(this Grammar<T> grammar)
    where T : class, U
  {
    return grammar.Map(o => new List<U>() { o },
      l => MapResult<T>.FromNullable(l.FirstOrDefault() as T));
  }
  
  public static Grammar<List<T>> Singleton<T>(this Grammar<T> grammar) {
    return grammar.Map(o => new List<T>() { o },
      l => MapResult<T>.FromNullable(l.FirstOrDefault()));
  }
  
  public static Grammar<List<T>> OptionToList<T>(this Grammar<T?> grammar) {
    return grammar.Map(o => o == null ? new List<T>() : new List<T>() { o },
      l => new MapSuccess<T?>(l.FirstOrDefault()));
  }
  
  public static Grammar<T> Then<TLeft, TRight, T>(
    this Grammar<TLeft> left, 
    Grammar<TRight> right,
    Separator mode,
    Func<TLeft, TRight, T> construct,
    Func<T, (TLeft, TRight)?> destruct) {
    return new SequenceG<TLeft, TRight, T>(left, right, mode, construct, destruct);
  }
  
  public static Grammar<TContainer> Then<TContainer, TValue>(
    this Grammar<TContainer> containerGrammar, 
    Grammar<TValue> value,
    Func<TContainer, TValue> get,
    Action<TContainer, TValue> set, 
    Separator mode = Separator.Space) {
    return new SequenceG<TContainer, TValue, TContainer>(containerGrammar, value, mode,
      (c, v) => {
        set(c, v);
        return c;
      }, c => (c, get(c)));
  }
  
  public static Grammar<TContainer> Assign<TContainer, TValue>(
    this Grammar<TValue> value, 
    Expression<Func<TContainer, TValue>> getExpression, Separator mode = Separator.Space) 
    where TContainer : new() {
    var property = getExpression.GetProperty();
    return value.Map(v => {
      var container = new TContainer();
      property.Set(container, v);
      return container;
    }, container => property.Get(container));
  }
  
  public static Grammar<TContainer> Assign<TContainer, TValue>(
    this Grammar<TValue> value, 
    Func<TContainer> createContainer, 
    Expression<Func<TContainer, TValue>> getExpression, Separator mode = Separator.Space) {
    var property = getExpression.GetProperty();
    return value.Map(v => {
      var container = createContainer();
      property.Set(container, v);
      return container;
    }, container => property.Get(container));
  }
  
  public static Grammar<TContainer> Then<TContainer, TValue>(
    this Grammar<TContainer> containerGrammar, 
    Grammar<TValue> value, 
    Expression<Func<TContainer, TValue>> get, Separator mode = Separator.Space) {
    var property = get.GetProperty();
    return containerGrammar.Then(value, property.Get, property.Set, mode);
  }

  public static Grammar<T> Indent<T>(this Grammar<T> grammar, int amount = 1) {
    return new IndentG<T>(grammar, amount);
  }
  
  public static Grammar<T> SetRange<T>(this Grammar<T> grammar, Action<T, ParseRange> set) {
    return grammar.Map((t, v) => {
      set(v, t);
      return v;
    }, x => x);
  }

  public static Grammar<T?> Option<T>(this Grammar<T> grammar) {
    return grammar.Map<T, T?>(t => t, t => t).Or(new Constructor<T?>(() => default));
  }
  
  public static Grammar<T?> Option<T>(this Grammar<T> grammar, VoidGrammar fallback) {
    var r = fallback.Then(GrammarBuilder.Constant<T?>(default));
    return grammar.Map<T, T?>(t => t, t => t).Or(r);
  }

  public static VoidGrammar Ignore<T>(this Grammar<T> grammar) {
    return new ParseOnly<T>(grammar);
  }
}

public interface MapResult<T> {
  public static MapResult<T> FromNullable(T? nullable) {
    if (nullable == null) {
      return new MapFail<T>();
    }
    return new MapSuccess<T>(nullable);
  }
}

public record MapSuccess<T>(T Value) : MapResult<T>;
public record MapFail<T>() : MapResult<T>;

class Fail<T>(string expectation) : Grammar<T> {
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    return new FailW<T>();
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return new FailR<T>(expectation);
  }

  public IEnumerable<Grammar> Children => [];
}

class ExplicitGrammar<T>(Parser<T> parser, Printer<T> printer) : Grammar<T> {
  Printer<T> Grammar<T>.ToPrinter(Func<Grammar, Printer> recurse) {
    return printer;
  }

  Parser<T> Grammar<T>.ToParser(Func<Grammar, Parser> recurse) {
    return parser;
  }

  public IEnumerable<Grammar> Children => [];
}

public static class GrammarBuilder {

  
  public static Grammar<T> Recursive<T>(Func<Grammar<T>, Grammar<T>> build) {
    RecursiveG<T>? result = null;
    // ReSharper disable once AccessToModifiedClosure
    result = new RecursiveG<T>(() => build(result!));
    var resolved = result.Inner;
    return result;
  }
  
  public static Grammar<T> Constructor<T>() where T : new() => new Constructor<T>(() => new T());
  public static Grammar<T> Constant<T>(T value) => new Value<T>(value);
  public static VoidGrammar Keyword(string keyword) => new TextG(keyword);
  public static Grammar<T> Fail<T>(string expectation) => new Fail<T>(expectation);
  public static readonly Grammar<string> Identifier = new IdentifierG();
  public static readonly Grammar<int> Number = new NumberG();
  public static readonly Grammar<string> Whitespace = new ExplicitGrammar<string>(ParserBuilder.Whitespace, VerbatimW.Instance);
  
  public static readonly Grammar<IPosition> Position = 
    new ExplicitGrammar<IPosition>(PositionR.Instance, new IgnoreW<IPosition>(EmptyW.Instance));
}
