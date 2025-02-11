using Microsoft.Dafny;
using Microsoft.Extensions.Logging.Abstractions;
using Serilog.Core;
using Uri = System.Uri;

namespace DafnyCore.Test;

public class DeserializerTest {

  class Person {
    private int age;
    private string name;

    public Person(int age, string name) {
      this.age = age;
      this.name = name;
    }
  }

  [Fact]
  public Task DeserializeNull() {
    var d = new Deserializer(new Uri("file://bla.bla"), new TextDecoder("true "));
    var result = d.DeserializeLiteralExprOption();
    Assert.Null(result);
    return Task.CompletedTask;
  }
  
  [Fact]
  public Task DeserializeNonNull() {
    var d = new Deserializer(new Uri("file://bla.bla"), new TextDecoder("false 0; 0; 0; 0; 0; 0; Int32 23254; "));
    var result = d.DeserializeLiteralExprOption();
    Assert.Equal(23254, result.Value);
    return Task.CompletedTask;
  }
  
  [Fact]
  public async Task Deserialize() {
    var input =
      "0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; \"foo\" 0; 0; true true 1; ClassDecl 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; \"foo\" true 0; 1; Method 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; \"foo\" true true false 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; true 0; 0; 0; 0; 0; 0; 0; true 0; 0; 0; 0; 0; 0; 0; 0; true 0; 0; 0; 0; 0; 0; true 1; AssertStmt 0; 0; 0; 0; 0; 0; true LiteralExpr 0; 0; 0; 0; 0; 0; Boolean false true 0; true false 0; 0; false 0;";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.Set(CommonOptionBag.InputType, CommonOptionBag.InputTypeEnum.Binary);
    var reporter = new BatchErrorReporter(options);
    var output = await ProgramParser.Parse(input, new Uri("file://test.java"), reporter);
    Assert.True(output.Program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().First().Members.OfType<Method>()
      .First().Body.Body.OfType<AssertStmt>().First().Expr is LiteralExpr literalExpr && (bool)literalExpr.Value == false);
  }
  
  [Fact]
  public async Task Deserialize2() {
    var input =
      "0 1 0 1 0 1 0 1 0 1 0 1 \"unnamed\" ] 0 null null +ClassDecl:4 2 6 3 4 2 4 2 4 2 4 2 \"JSpec\" null ] ] ] false +ClassDecl:8 2 12 3 8 2 8 2 8 2 8 2 \"Main\" null ] +Method:9 4 11 5 9 16 9 16 9 16 9 16 \"Foo\" null true false ] ] ] ] 9 4 11 5 9 16 ] null 9 4 11 5 9 16 ] null ] 9 4 11 5 9 16 ] null 9 4 11 5 9 16 null +AssertStmt:10 6 10 26 10 19 null +LiteralExpr:10 20 10 25 10 20 +Boolean:false null] null false] ] false]";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.Set(CommonOptionBag.InputType, CommonOptionBag.InputTypeEnum.Binary);
    var reporter = new BatchErrorReporter(options);
    var output = await ProgramParser.Parse(input, new Uri("file://test.java"), reporter);
    Assert.True(output.Program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().ElementAt(1).Members.OfType<Method>()
      .First().Body.Body.OfType<AssertStmt>().First().Expr is LiteralExpr literalExpr && (bool)literalExpr.Value == false);
  }
}