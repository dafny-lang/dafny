namespace CompilerBuilder;

public static class ParserBuilder {
  
  public static Parser<T> Recursive<T>(Func<Parser<T>, Parser<T>> build) {
    Parser<T>? result = null;
    // ReSharper disable once AccessToModifiedClosure
    result = new RecursiveR<T>(() => build(result!));
    return result;
  }
  
  public static Parser<T> Value<T>(Func<T> value) => new ValueR<T>(value);
  
  // TODO should this exist? Could be dangerous
  public static Parser<T> Value<T>(T value) => new ValueR<T>(() => value);
  public static VoidParser Keyword(string keyword) => new TextR(keyword);
  public static readonly Parser<string> Identifier = new IdentifierR();
  public static readonly Parser<int> Number = new NumberR();
  public static readonly Parser<string> SlashSlashLineComment = new LineComment();
  public static readonly Parser<string> Whitespace = new Whitespace();
}