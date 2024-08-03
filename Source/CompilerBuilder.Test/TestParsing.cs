namespace CompilerBuilder.Test;

using static ParserBuilder;

public class TestParsing {
  
  [Fact]
  public void TestNumber() {
    var number = Number;
    var parsed = number.Parse("123124").Success!.Value;
    Assert.Equal(123124, parsed);
  }
  
  [Fact]
  public void TestIdentifier() {
    var number = Identifier;
    var parsed = number.Parse("abcdefg").Success!.Value;
    Assert.Equal("abcdefg", parsed);
  }
  
  [Fact]
  public void TestKeyword() {
    var parser = Keyword("hello").Then(Value(true));
    var parsed = parser.Parse("hello").Success!.Value;
    Assert.True(parsed);

    var byeResult = parser.Parse("bye");
    Assert.Contains("Expected", byeResult.Failure!.Message);
  }
  
  [Fact]
  public void TestChoice() {
    var number = Number.Map(i => (object)i).Or<object>(Identifier.Map(s => (object)s));
    var parsed = number.Parse("123124").Success!.Value;
    Assert.Equal(123124, parsed);
  }
}