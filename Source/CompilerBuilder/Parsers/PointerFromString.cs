using System.Collections.Immutable;

namespace CompilerBuilder;

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
    seen = ImmutableHashSet<Parser>.Empty;
    pointerCache = new();
  }

  public PointerFromString(string text, int offset, int line, int column,
    Dictionary<CacheKey, PointerFromString> pointerCache,
    ImmutableHashSet<Parser> seen) {
    Offset = offset;
    Line = line;
    Column = column;
    this.seen = seen;
    Text = text;
    this.pointerCache = pointerCache;
  }

  public string Upcoming => SubSequence(5).ToString();
  
  public string Text { get; }

  public int Offset { get; }
  public int Line { get; }
  public int Column { get; }
  private readonly ImmutableHashSet<Parser> seen;
  
  public bool SeenHere(Parser parser) {
    return seen.Contains(parser);
  }

  public ITextPointer Add(Parser parser) {
    var newSeen = seen.Add(parser);
    var key = new CacheKey(Offset, newSeen);
    if (pointerCache.TryGetValue(key, out var existingPointer)) {
      return existingPointer;
    }

    return new PointerFromString(Text, Offset, Line, Column, pointerCache, newSeen);
  }

  public ITextPointer Remove(Parser parser) {
    var newSeen = seen.Remove(parser);
    var key = new CacheKey(Offset, newSeen);
    if (pointerCache.TryGetValue(key, out var existingPointer)) {
      return existingPointer;
    }
    return new PointerFromString(Text, Offset, Line, Column, pointerCache, newSeen);
  }

  public ITextPointer Drop(int amount) {
    var sequence = SubSequence(amount);
    var lines = sequence.ToString().Split("\n"); // TODO optimize
    // if (references == 0) {
    //   cache.Clear();
    // })
    var newOffset = Offset + amount;
    var key = new CacheKey(newOffset, seen);
    if (pointerCache.TryGetValue(key, out var existingPointer)) {
      return existingPointer;
    } else {
      var result = new PointerFromString(Text, newOffset, 
        Line + lines.Length - 1, 
        lines.Length > 1 ? lines.Last().Length : Column + amount, 
        pointerCache,
        ImmutableHashSet<Parser>.Empty);
      pointerCache[key] = result;
      return result;
    }
  }

  public char First => At(0);
  public int Length => Text.Length - Offset;

  public char At(int offset) {
    return Text[Offset + offset];
  }

  public ReadOnlySpan<char> Remainder => Text.AsSpan(Offset);

  public ReadOnlySpan<char> SubSequence(int length) {
    return Text.AsSpan(Offset, Math.Min(Length, length));
  }

  private int references = 0;
  public void Ref() {
    references++;
  }

  public void UnRef() {
    references--;
  }

  internal record CacheKey(int Offset, ImmutableHashSet<Parser> Seen);

  // private readonly Dictionary<Parser, ParseResult> simpleCache;
  private static readonly Dictionary<(int, Parser), ParseResult> globalSimpleCache = new();
  private readonly Dictionary<Parser, ParseResult> cache = new();
  private readonly Dictionary<CacheKey, PointerFromString> pointerCache;

  public ParseResult<Unit> ParseWithCache(VoidParser parser) {
    if (cache.TryGetValue(parser, out var result)) {
      return (ParseResult<Unit>)result;
    }

    var globalKey = (Offset, parser);
    if (globalSimpleCache.TryGetValue(globalKey, out result)) {
      return (ParseResult<Unit>)result;
    }
    // if (simpleCache.ContainsKey(parser)) {
    //   var c = 3;
    // }
    
    result = parser.Parse(this);
    cache[parser] = result;
    // simpleCache[parser] = result;
    globalSimpleCache[globalKey] = result;

    return (ParseResult<Unit>)result;
  }
  
  public ParseResult<Unit> ParseWithCache2(VoidParser parser) {
    if (cache.TryGetValue(parser, out var result)) {
      return (ParseResult<Unit>)result;
    }
    var globalKey = (Offset, parser);

    if (globalSimpleCache.TryGetValue(globalKey, out result)) {
      return (ParseResult<Unit>)result;
    }
    // if (simpleCache.ContainsKey(parser)) {
    //   var c = 3;
    // }
    
    result = parser.Parse(this);
    cache[parser] = result;
    // simpleCache[parser] = result;
    globalSimpleCache[globalKey] = result;

    return (ParseResult<Unit>)result;
  }

  public ParseResult<T> ParseWithCache2<T>(Parser<T> parser) {
    if (cache.TryGetValue(parser, out var result)) {
      return (ParseResult<T>)result;
    }
    
    var globalKey = (Offset, parser);
    if (globalSimpleCache.TryGetValue(globalKey, out result)) {
      return (ParseResult<T>)result;
    }
    // if (simpleCache.ContainsKey(parser)) {
    //   var c = 3;
    // }
    
    result = parser.Parse(this);
    cache[parser] = result;
    // simpleCache[parser] = result;
    globalSimpleCache[globalKey] = result;

    return (ParseResult<T>)result;
  }
  
  public ParseResult<T> ParseWithCache<T>(Parser<T> parser) {
    if (cache.TryGetValue(parser, out var result)) {
      return (ParseResult<T>)result;
    }

    var globalKey = (Offset, parser);
    if (globalSimpleCache.TryGetValue(globalKey, out result)) {
      return (ParseResult<T>)result;
    }
    // if (simpleCache.ContainsKey(parser)) {
    //   var c = 3;
    // }
    
    result = parser.Parse(this);
    cache[parser] = result;
    // simpleCache[parser] = result;
    globalSimpleCache[globalKey] = result;

    return (ParseResult<T>)result;
  }
}