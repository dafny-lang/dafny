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
    cache = new();
    pointerCache = new();
  }

  public PointerFromString(string text, int offset, int line, int column,
    Dictionary<int, PointerFromString> pointerCache,
    Dictionary<Parser, ParseResult> cache,
    ImmutableHashSet<Parser> seen) {
    Offset = offset;
    Line = line;
    Column = column;
    this.seen = seen;
    Text = text;
    this.cache = cache;
    this.pointerCache = pointerCache;
  }

  public string Upcoming => SubSequence(5).ToString();
  
  public string Text { get; }

  public int Offset { get; }
  public int Line { get; }
  public int Column { get; }
  private readonly ImmutableHashSet<Parser> seen;
  
  public bool FindingRecursionFor(Parser parser) {
    return false;
  }

  public ITextPointer Add(Parser parser) {
    var newSeen = seen.Add(parser);
    return new PointerFromString(Text, Offset, Line, Column, pointerCache, cache, newSeen);
  }

  public ITextPointer Remove(Parser parser) {
    var newSeen = seen.Remove(parser);
    if (pointerCache.TryGetValue(Offset, out var existingPointer)) {
      return existingPointer;
    }
    return new PointerFromString(Text, Offset, Line, Column, pointerCache, cache, newSeen);
  }

  public ITextPointer Drop(int amount) {
    // if (references == 0) {
    //   cache.Clear();
    // })
    var newOffset = Offset + amount;
    if (pointerCache.TryGetValue(newOffset, out var existingPointer)) {
      return existingPointer;
    } else {
      var sequence = SubSequence(amount);
      var lines = sequence.ToString().Split("\n"); // TODO optimize
      var result = new PointerFromString(Text, newOffset, 
        Line + lines.Length - 1, 
        lines.Length > 1 ? lines.Last().Length : Column + amount, 
        pointerCache,
        new(),
        ImmutableHashSet<Parser>.Empty);
      pointerCache[newOffset] = result;
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

  private readonly Dictionary<Parser, ParseResult> cache;
  private readonly Dictionary<int, PointerFromString> pointerCache;

  public ParseResult<Unit> ParseWithCache(VoidParser parser) {
    // if (cache.TryGetValue(parser, out var result)) {
    //   return (ParseResult<Unit>)result;
    // }
    
    var result = parser.Parse(this);
    cache[parser] = result;

    return (ParseResult<Unit>)result;
  }
  
  public ParseResult<Unit> ParseWithCache2(VoidParser parser) {
    return ParseWithCache(parser);
  }

  public ParseResult<T> ParseWithCache2<T>(Parser<T> parser) {
    return ParseWithCache(parser);
  }
  
  public ParseResult<T> ParseWithCache<T>(Parser<T> parser) {
    // if (cache.TryGetValue(parser, out var result)) {
    //   return (ParseResult<T>)result;
    // }
    
    var result = parser.Parse(this);
    cache[parser] = result;

    return (ParseResult<T>)result;
  }
}