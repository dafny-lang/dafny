// See https://aka.ms/new-console-template for more information

using CompilerBuilder;
using DAST;
using Microsoft.Dafny;
using static CompilerBuilder.ParserBuilder;
using Name = Microsoft.Dafny.Name;

class Person() {
  public string FirstName { get; set; }
  public int Age { get; set; }
  public string LastName { get; set; }
}

class Test {

  Parser<MemberDecl> Member() {
  }

  struct ClassDeclData {
    public Name Name { get; set; }
    public List<MemberDecl> Members { get; set; }
  }
  
  Parser<ClassDecl> Class() {
    var header = Value(new ClassDeclData()).
      Then("class").
      Then(NameParser, (cl, name) => cl.Name = name);
    
    var body = Member().Many().InBraces();
    var dataParser = header.
      Then(body, (data, members) => data.Members = members);
    
    return dataParser.Map((token, data) => new ClassDecl(token, data.Name, 
      module, typeArgs, data.Members, attributes, isRefining, traits));
  }

  private static readonly Parser<Name> NameParser = Identifier.Map((t, value) => new Name(t, value));
}

