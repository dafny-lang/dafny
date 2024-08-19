using System.Text.RegularExpressions;

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
  public static Parser<T> Constant<T>(T value) => new ValueR<T>(() => value);
  public static VoidParser Keyword(string keyword) => new TextR(keyword);
  public static readonly Parser<string> Identifier = new RegexR(@"\w+", "identifier");
  public static readonly Parser<int> Number = new RegexR(@"\d+", "number").MapValue(s => 
    int.TryParse(s, out var result) ? result : default(int?));
  public static readonly Parser<char> CharInSingleQuotes = new RegexR(@"'\w'", "char").Map(s => s[1]);
  
  public static Parser<T> Fail<T>(string expectation) => new FailR<T>(expectation);
  public static readonly Parser<string> SlashSlashLineComment = new Comment("//", "\n", "a line comment");
  public static readonly Parser<string> BlockComment = new Comment("/**", "*/", "a block comment");
  public static readonly Parser<string> Whitespace = new Whitespace();
}