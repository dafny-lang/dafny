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
    var numberOrIdentifier = Number.Map(i => (object)i).Or(Identifier.Map(s => (object)s));
    Assert.Equal(123124, numberOrIdentifier.Parse("123124").Success!.Value);
    Assert.Equal("abcefg", numberOrIdentifier.Parse("abcefg").Success!.Value);
    Assert.Null(numberOrIdentifier.Parse("!@!@$#").Success);
  }

  record Person {
    public int Age;
    public string Name;
  }
  
  [Fact]
  public void TestSequence() {
    var person =
      Value(new Person()).
        Then(Number, (p, v) => p.Age = v).
        Then(Identifier, (p, v) => p.Name = v);
    var result = person.Parse("123124Jan");
    Assert.Equal(123124, result.Success!.Value.Age);
    Assert.Equal("Jan", result.Success!.Value.Name);
    Assert.Null(person.Parse("1231").Success);
  }
  
  [Fact]
  public void TestMany() {
    var person =
      Value(new Person()).
        Then(Number, (p, v) => p.Age = v).
        Then(Identifier, (p, v) => p.Name = v);
    var persons = person.Many();
    var goodResult = persons.Parse("123124Jan12313Henk12Remy");
    Assert.Equal(3, goodResult.Success!.Value.Count);
    Assert.Equal("Remy", goodResult.Success!.Value[2].Name);
    var badResult = persons.Parse("123124Jan12313Henk12");
    Assert.Null(badResult.Success);
  }
}