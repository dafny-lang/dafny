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
      "0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; \"foo\" 0; 0; true true 1; ClassDecl 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; \"foo\" true 0; 1; Method 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; \"foo\" true true false 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; true 0; 0; 0; 0; 0; 0; 0; true 0; 0; 0; 0; 0; 0; 0; 0; true 0; 0; 0; 0; 0; 0; true 1; AssertStmt 0; 0; 0; 0; 0; 0; true LiteralExpr 0; 0; 0; 0; 0; 0; Boolean false true true true 0; false 0; 0; 0; false 0; ";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.Set(CommonOptionBag.InputType, CommonOptionBag.InputTypeEnum.Binary);
    var reporter = new BatchErrorReporter(options);
    var output = await ProgramParser.Parse(input, new Uri("file://test.java"), reporter);
    Assert.True(output.Program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().First().Members.OfType<Method>()
      .First().Body!.Body.OfType<AssertStmt>().First().Expr is LiteralExpr literalExpr && (bool)literalExpr.Value == false);
  }
}