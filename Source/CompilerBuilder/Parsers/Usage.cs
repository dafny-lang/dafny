// See https://aka.ms/new-console-template for more information

namespace CompilerBuilder;

using static ParserBuilder;

class Person() {
  public string FirstName { get; set; }
  public int Age { get; set; }
  public string LastName { get; set; }
}

class Test {
  void ParseExample() {
    var g = Value(new Person())
      .Then(Identifier, (p, v) => p.FirstName = v)
      .Then(Number, (p, v) => p.Age = v)
      .Then(Identifier, (p, v) => p.LastName = v);
  }
}