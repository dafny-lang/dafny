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
    var result = d.ReadLiteralExprOption();
    Assert.Null(result);
    return Task.CompletedTask;
  }

  [Fact]
  public Task DeserializeNonNull() {
    var d = new Deserializer(new Uri("file://bla.bla"), new TextDecoder("false 0; 0; 0; 0; 0; 0; Int32 23254; "));
    var result = d.ReadLiteralExprOption();
    Assert.Equal(23254, result.Value);
    return Task.CompletedTask;
  }

  [Fact]
  public async Task Deserialize() {
    var input =
      "0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; \"unnamed\" 0; 0; null null 1; ClassDecl 3; 2; 7; 3; 3; 2; 3; 2; 3; 2; 3; 2; \"Main\" null 0; 1; Method 4; 4; 6; 5; 4; 16; 4; 16; 4; 16; 4; 16; \"Foo\" null true false 0; 0; 0; 0; 4; 4; 6; 5; 4; 16; 0; null 4; 4; 6; 5; 4; 16; 0; null 0; 4; 4; 6; 5; 4; 16; 0; null  4; 4; 6; 5; 4; 16; null 1; AssertStmt 5; 6; 5; 19; 5; 6; null LiteralExpr 5; 13; 5; 18; 5; 13; Boolean false null null false 0; false ";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.Set(CommonOptionBag.InputType, CommonOptionBag.InputTypeEnum.Binary);
    var reporter = new BatchErrorReporter(options);
    var output = await ProgramParser.Parse(input, new Uri("file://test.java"), reporter);
    Assert.True(output.Program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().First().Members.OfType<Method>()
      .First().Body!.Body.OfType<AssertStmt>().First().Expr is LiteralExpr literalExpr && (bool)literalExpr.Value == false);
  }
}