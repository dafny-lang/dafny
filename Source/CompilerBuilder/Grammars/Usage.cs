// See https://aka.ms/new-console-template for more information

namespace CompilerBuilder;

using static GrammarBuilder;

class Person() {
  public string FirstName { get; set; }
  public int Age { get; set; }
  public string LastName { get; set; }
}

class Test {
  void ParseExample() {
    var g = Builder<Person>()
      .Then(Identifier, (p, v) => p.FirstName = v)
      .Then(Number, (p, v) => p.Age = v)
      .Then(Identifier, (p, v) => p.LastName = v);
  }
}