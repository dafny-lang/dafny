// See https://aka.ms/new-console-template for more information

using CompilerBuilder;
using Microsoft.Dafny;
using static CompilerBuilder.GrammarBuilder;
using Name = Microsoft.Dafny.Name;

namespace JavaSupport;

class JavaGrammar {
  Grammar<ClassDecl> Class() {
    var header = Value(new ClassDecl()).
      Then("class").
      Then(Name, cl => cl.NameNode);
    
    var body = Member().Many().InBraces();

    return header.
      Then(body, cl => cl.Members).
      SetRange((cl, t) => cl.RangeToken = t);
  }

  Grammar<MemberDecl> Member() {
  }

  private static readonly Grammar<Name> Name = 
    Identifier.Map((t, value) => new Name(t, value), n => n.Value);
}