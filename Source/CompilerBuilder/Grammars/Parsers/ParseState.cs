using Microsoft.Dafny;

namespace CompilerBuilder;


/*
 * Caching during parser is great
 * But when do I make items go stale?
 * What's the latest position for which I remember things?
 *
 * Choices are areas where I need the cache, because if one options fails, I need the cache to evaluate other options.
 * One the choice is done, I no longer need to cache at that position.
 * However, suppose I'm in a choice at the top level, and I have to parse almost everything within that choice,
 * then I'd never clear the cache.
 * Can I avoid being in that position?
 *
 * I only have to cache in a choice if the two options start with the same thing, like for many binary expressions
 * Or maybe I only need to do caching when doing a choice between parsers that fail late.
 *
 * How do I avoid using the call-stack?
 */

record Failure(int Location, string Message);

class ParseState {
  public Stack<object> Results = new();
  public Stack<object> Todos { get; } = new();
  public bool Recovering { get; set; }
  public Failure FurthestFailure { get; set; }
  public IToken Location { get; }

  public void Run(Parser root) {
    Todos.Push(root);
    while (Todos.Any()) {
      var current = Todos.Pop();
      if (current is Parser parser) {
      } else if (current is Action action) {
        action();
      }
    }
  }
  
  public void Plan(VoidParser parser) {
    
  }
  
  public void Plan<A>(Parser<A> first, Action recover) {
    Todos.Push(() => {
      if (Recovering) {
        Recovering = false;
        recover();
      }
    });
    Todos.Push(first);
  }
  
  public void Plan<A,B>(Parser<A> first, Parser<B> second, Action<A,B> useResults) {
    Todos.Push(() => {
      var firstResult = Results.Pop();
      var secondResult = Results.Pop();
      useResults((A)firstResult, (B)secondResult);
    });
    Todos.Push(second);
    Todos.Push(first);
  }

  public void Store(object container) {
    Results.Push(container);
  }
}