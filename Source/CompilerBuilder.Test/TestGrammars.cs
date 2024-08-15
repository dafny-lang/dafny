using CompilerBuilder.Grammars;

namespace CompilerBuilder.Test;

using static GrammarBuilder;

public class TestGrammars {
  
  [Fact]
  public void TestNumber() {
    var number = Number;
    var parsed = number.ToParser().Parse("123124").Success!.Value;
    Assert.Equal(123124, parsed);
  }
  
  [Fact]
  public void TestIdentifier() {
    var number = Identifier;
    var parsed = number.ToParser().Parse("abcdefg").Success!.Value;
    Assert.Equal("abcdefg", parsed);
  }
  
  [Fact]
  public void TestKeyword() {
    var parser = Keyword("hello").Then(Constant(true));
    var parsed = parser.ToParser().Parse("hello").Success!.Value;
    Assert.True(parsed);

    var byeResult = parser.ToParser().Parse("bye");
    Assert.Contains("Expected", byeResult.Failure!.Message);
  }
  
  [Fact]
  public void TestChoice() {
    var numberOrIdentifier = Number.UpCast<int, object>().Or(Identifier.UpCast<string, object>());
    Assert.Equal(123124, numberOrIdentifier.ToParser().Parse("123124").Success!.Value);
    Assert.Equal("abcefg", numberOrIdentifier.ToParser().Parse("abcefg").Success!.Value);
    Assert.Null(numberOrIdentifier.ToParser().Parse("!@!@$#").Success);
  }

  record Person {
    public int Age;
    public string Name;
  }
  
  [Fact]
  public void TestSequence() {
    var person =
      Constructor<Person>().
        Then(Number, (p) => p.Age).
        Then(Identifier, (p) => p.Name);
    var result = person.ToParser().Parse("123124Jan");
    Assert.Equal(123124, result.Success!.Value.Age);
    Assert.Equal("Jan", result.Success!.Value.Name);
    Assert.Null(person.ToParser().Parse("1231").Success);
  }
  
  [Fact]
  public void TestMany() {
    var person =
      Constructor<Person>().
        Then(Number, (p) => p.Age).
        Then(Identifier, (p) => p.Name);
    var persons = person.Many();
    var parser = persons.ToParser();
    var goodResult = parser.Parse("123124Jan12313Henk12Remy");
    Assert.Equal(3, goodResult.Success!.Value.Count());
    Assert.Equal("Remy", goodResult.Success!.Value.ElementAt(2).Name);
    var badResult = parser.Parse("123124Jan12313Henk12");
    Assert.Null(badResult.Success);
  }

  [Fact]
  public void LeftRecursive() {
    var parser = Recursive<int>(self => Number.Or(self.Then("^")));
    var result = parser.ToParser().Parse("13^^^");
    Assert.Equal(13, result.Success!.Value);
  }

  record PersonWithTrivia {
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
    var trivia = Comments.SlashSlashLineComment().Or(Whitespace).Or(Comments.BlockComment()).Many();
    var person =
      Constructor<PersonWithTrivia>().
        Then(Number, (p) => p.Age).
        Then(trivia, (p) => p.Trivia).
        Then(Identifier, (p) => p.Name);
    var input = "123  Remy";
    var result = person.ToParser().Parse(input);
    Assert.NotNull(result.Success);
    Assert.Equal("  ", result.Success?.Value.Trivia[0]);

    var input2 = @"123// line comment
  
// another linecomment
/** block 

comment
*/
Remy";
    var result2 = person.ToParser().Parse(input2);
    Assert.NotNull(result2.Success);
    Assert.Equal("// another linecomment\n", result2.Success?.Value.Trivia[2]);
  }
  
}