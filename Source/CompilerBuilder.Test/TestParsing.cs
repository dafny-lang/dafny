namespace CompilerBuilder.Test;

using static ParserBuilder;

public class TestParsing {
  
  [Fact]
  public void TestNumber() {
    var number = Number;
    var parsed = number.Parse("123124").ForceSuccess.Value;
    Assert.Equal(123124, parsed);
  }
  
  [Fact]
  public void TestChar() {
    var parsed = CharInSingleQuotes.Parse("'d'").ForceSuccess.Value;
    Assert.Equal("d", parsed);
  }
  
  [Fact]
  public void TestIdentifier() {
    var number = Identifier;
    var result = number.Parse("abcdefg");
    var parsed = result.ForceSuccess.Value;
    Assert.Equal("abcdefg", parsed);
  }
  
  [Fact]
  public void TestKeyword() {
    var parser = Keyword("hello").Then(Constant(true));
    var parsed = parser.Parse("hello").Success!.Value;
    Assert.True(parsed);

    var byeResult = parser.Parse("bye");
    Assert.Contains("Expected", byeResult.Failure!.Message);
  }
  
  [Fact]
  public void TestChoice() {
    var numberOrIdentifier = Fail<object>("a number or identifier").
      Or(Number.Map(i => (object)i).Or(Identifier.Map(s => (object)s)));
    Assert.Equal(123124, numberOrIdentifier.Parse("123124").Success!.Value);
    Assert.Equal("abcefg", numberOrIdentifier.Parse("abcefg").Success!.Value);
    Assert.Null(numberOrIdentifier.Parse("!@!@$#").Success);
    
    Assert.Equal("'!@#!@' is not the end of the text", numberOrIdentifier.Parse("123124!@#!@#").Failure!.Message);
    Assert.Equal("'!@#!@' is not a number or identifier", numberOrIdentifier.Parse("!@#!@#").Failure!.Message);
  }
  
  record Person {
    public int Age;
    public string Name;
  }
  
  [Fact]
  public void TestSequence() {
    var person =
      Value(() => new Person()).
        Then(Number, (p, v) => p.Age = v).
        Then(Identifier, (p, v) => p.Name = v);
    var result = person.Parse("123124Jan");
    Assert.Equal(123124, result.Success!.Value.Age);
    Assert.Equal("Jan", result.Success!.Value.Name);
    Assert.Null(person.Parse("1231").Success);
    
    Assert.Equal("'!@#!@' is not an identifier", person.Parse("123124!@#!@#").Failure!.Message);
  }
  
  [Fact]
  public void TestMany() {
    var person =
      Value(() => new Person()).
        Then(Number, (p, v) => p.Age = v).
        Then(Identifier, (p, v) => p.Name = v);
    var persons = person.Many();
    var goodResult = persons.Parse("123124Jan12313Henk12Remy");
    Assert.Equal(3, goodResult.Success!.Value.Count);
    Assert.Equal("Remy", goodResult.Success!.Value[2].Name);
    var badResult = persons.Parse("123124Jan12313Henk12");
    Assert.Null(badResult.Success);
  }

  [Fact]
  public void LeftRecursive() {
    var parser = Recursive<int>(self => Number.Or(self.Then("^")));
    var result = parser.Parse("13^^^");
    Assert.Equal(13, result.Success!.Value);
  }

  class PersonWithTrivia {
    public int Age;
    public string Name;
    public List<string> Trivia = new();

    public PersonWithTrivia() {
      Age = 0;
      Name = null;
    }
  }
  
  [Fact]
  public void ManualTrivia() {
    var trivia = SlashSlashLineComment.Or(Whitespace).Many();
    var person =
      Value(() => new PersonWithTrivia()).
        Then(Number, (p, v) => p.Age = v).
        Then(trivia, (p, newTrivia) => p.Trivia.AddRange(newTrivia)).
        Then(Identifier, (p, v) => p.Name = v);
    var input = "123  Remy";
    var result = person.Parse(input);
    Assert.NotNull(result.Success);
    Assert.Equal(123, result.Success?.Value.Age);
    Assert.Equal("  ", result.Success?.Value.Trivia[0]);

    var input2 = @"123// line comment
  
// another linecomment
Remy";
    var result2 = person.Parse(input2);
    Assert.NotNull(result2.Success);
    Assert.Equal("// another linecomment", result2.Success?.Value.Trivia[2]);
  }
  
  // There were a lot of issues in the following that this file should test, but did not.
  // Things like nested recursive things
  // And not dropping intermediate results when growing a seed.
  // class Div {
  //   int Foo(int x) {
  //     return 3 / x;
  //   }
  // }
}