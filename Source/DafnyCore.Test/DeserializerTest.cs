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
    var d = new Deserializer(new TextDecoder("true "));
    var result = d.ReadLiteralExprOption();
    Assert.Null(result);
    return Task.CompletedTask;
  }

  [Fact]
  public Task DeserializeNonNull() {
    var d = new Deserializer(new TextDecoder("false 0; 0; 0; 0; 0; 0; Int32 23254; "));
    var result = d.ReadLiteralExprOption();
    Assert.Equal(23254, result.Value);
    return Task.CompletedTask;
  }

  [Fact]
  public async Task AssertFalseBinary() {
    var input =
      "0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; \"unnamed\" 0; 0; null null 1; ClassDecl 3; 2; 7; 3; 3; 2; 3; 2; 3; 2; 3; 2; \"Main\" null 0; 1; Method 4; 4; 6; 5; 4; 16; 4; 16; 4; 16; 4; 16; \"Foo\" null true false 0; 0; 0; 0; 4; 4; 6; 5; 4; 16; 0; null 4; 4; 6; 5; 4; 16; 0; null 0; 4; 4; 6; 5; 4; 16; 0; null  4; 4; 6; 5; 4; 16; null 1; AssertStmt 5; 6; 5; 19; 5; 6; null LiteralExpr 5; 13; 5; 18; 5; 13; Boolean false null null false 0; false ";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.Set(CommonOptionBag.InputType, CommonOptionBag.InputTypeEnum.Binary);
    var reporter = new BatchErrorReporter(options);
    var output = await ProgramParser.Parse(input, new Uri("file://test.java"), reporter);
    Assert.True(output.Program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().First().Members.OfType<Method>()
      .First().Body!.Body.OfType<AssertStmt>().First().Expr is LiteralExpr literalExpr && (bool)literalExpr.Value == false);
  }

  [Fact]
  public async Task FibonacciBinary() {
    var input =
      "1; \"string:///test.java\" 1; ClassDecl 5; 2; 37; 3; 5; 2; 5; 2; 5; 2; 5; 2; \"Fibonacci\" null 0; 2; Function 6; 6; 10; 7; 8; 33; 8; 33; 8; 33; 8; 33; \"Spec\" null true false 0; 1; 8; 38; 8; 59; 8; 58; 8; 58; 8; 58; 8; 58; \"n\" UserDefinedType 8; 54; 8; 57; 8; 54; NameSegment 8; 54; 8; 57; 8; 54; \"nat\" null false true null null false false false null 0; 0; 6; 6; 10; 7; 8; 33; 0; null 6; 6; 10; 7; 8; 33; 0; null false null UserDefinedType 8; 29; 8; 32; 8; 29; NameSegment 8; 29; 8; 32; 8; 29; \"nat\" null ITEExpr 9; 17; 9; 54; 9; 23; false BinaryExpr 9; 17; 9; 22; 9; 19; 7; NameSegment 9; 17; 9; 18; 9; 17; \"n\" null LiteralExpr 9; 21; 9; 22; 9; 21; Int32 2; NameSegment 9; 25; 9; 26; 9; 25; \"n\" null BinaryExpr 9; 29; 9; 54; 9; 41; 16; ApplySuffix 9; 29; 9; 40; 9; 33; NameSegment 9; 29; 9; 33; 9; 29; \"Spec\" null null 9; 29; 9; 40; 9; 33; 1; 9; 29; 9; 40; 9; 33; null BinaryExpr 9; 34; 9; 39; 9; 36; 17; NameSegment 9; 34; 9; 35; 9; 34; \"n\" null LiteralExpr 9; 38; 9; 39; 9; 38; Int32 1; false 9; 40; ApplySuffix 9; 43; 9; 54; 9; 47; NameSegment 9; 43; 9; 47; 9; 43; \"Spec\" null null 9; 43; 9; 54; 9; 47; 1; 9; 43; 9; 54; 9; 47; null BinaryExpr 9; 48; 9; 53; 9; 50; 17; NameSegment 9; 48; 9; 49; 9; 48; \"n\" null LiteralExpr 9; 52; 9; 53; 9; 52; Int32 2; false 9; 54; null null null Method 12; 6; 36; 7; 12; 29; 12; 29; 12; 29; 12; 29; \"Implementation\" null true false 0; 1; 12; 44; 12; 54; 12; 53; 12; 53; 12; 53; 12; 53; \"n\" UserDefinedType 12; 49; 12; 52; 12; 49; NameSegment 12; 49; 12; 52; 12; 49; \"nat\" null false true null null false false false null 1; BinaryExpr 14; 19; 14; 39; 14; 27; 7; ApplySuffix 14; 19; 14; 26; 14; 23; NameSegment 14; 19; 14; 23; 14; 19; \"Spec\" null null 14; 19; 14; 26; 14; 23; 1; 14; 19; 14; 26; 14; 23; null NameSegment 14; 24; 14; 25; 14; 24; \"n\" null false 14; 26; LiteralExpr 14; 29; 14; 39; 14; 29; Int32 2147483647; null null 1; BinaryExpr 15; 33; 15; 45; 15; 35; 5; NameSegment 15; 33; 15; 34; 15; 33; \"r\" null ApplySuffix 15; 38; 15; 45; 15; 42; NameSegment 15; 38; 15; 42; 15; 38; \"Spec\" null null 15; 38; 15; 45; 15; 42; 1; 15; 38; 15; 45; 15; 42; null NameSegment 15; 43; 15; 44; 15; 43; \"n\" null false 15; 45; null null 12; 6; 36; 7; 12; 29; 0; null 12; 6; 36; 7; 12; 29; 0; null 1; 12; 25; 12; 28; 12; 25; 15; 18; 15; 45; 15; 18; \"r\" UserDefinedType 12; 25; 12; 28; 12; 25; NameSegment 12; 25; 12; 28; 12; 25; \"nat\" null false false null null false false false null 12; 6; 36; 7; 12; 29; 0; null 12; 6; 36; 7; 12; 29; null 6; IfStmt 17; 10; 19; 11; 17; 10; null false BinaryExpr 17; 14; 17; 20; 17; 16; 5; NameSegment 17; 14; 17; 15; 17; 14; \"n\" null LiteralExpr 17; 19; 17; 20; 17; 19; Int32 0; 17; 22; 19; 11; 17; 22; null 1; ReturnStmt 18; 14; 18; 23; 18; 14; null 1; ExprRhs 18; 21; 18; 22; 18; 21; null LiteralExpr 18; 21; 18; 22; 18; 21; Int32 1; null VarDeclStmt 21; 10; 21; 33; 21; 14; null 1; 21; 10; 21; 33; 21; 14; \"previousResult\" UserDefinedType 21; 10; 21; 13; 21; 10; NameSegment 21; 10; 21; 13; 21; 10; \"nat\" null false AssignStatement 21; 31; 21; 32; 21; 31; null 1; IdentifierExpr 21; 10; 21; 33; 21; 14; \"previousResult\" 1; ExprRhs 21; 31; 21; 32; 21; 31; null LiteralExpr 21; 31; 21; 32; 21; 31; Int32 0; false VarDeclStmt 22; 10; 22; 25; 22; 14; null 1; 22; 10; 22; 25; 22; 14; \"result\" UserDefinedType 22; 10; 22; 13; 22; 10; NameSegment 22; 10; 22; 13; 22; 10; \"nat\" null false AssignStatement 22; 23; 22; 24; 22; 23; null 1; IdentifierExpr 22; 10; 22; 25; 22; 14; \"result\" 1; ExprRhs 22; 23; 22; 24; 22; 23; null LiteralExpr 22; 23; 22; 24; 22; 23; Int32 1; false VarDeclStmt 23; 10; 23; 20; 23; 14; null 1; 23; 10; 23; 20; 23; 14; \"i\" UserDefinedType 23; 10; 23; 13; 23; 10; NameSegment 23; 10; 23; 13; 23; 10; \"nat\" null false AssignStatement 23; 18; 23; 19; 23; 18; null 1; IdentifierExpr 23; 10; 23; 20; 23; 14; \"i\" 1; ExprRhs 23; 18; 23; 19; 23; 18; null LiteralExpr 23; 18; 23; 19; 23; 18; Int32 1; false WhileStmt 24; 10; 34; 11; 24; 10; null 3; BinaryExpr 26; 24; 26; 41; 26; 31; 5; NameSegment 26; 24; 26; 30; 26; 24; \"result\" null ApplySuffix 26; 34; 26; 41; 26; 38; NameSegment 26; 34; 26; 38; 26; 34; \"Spec\" null null 26; 34; 26; 41; 26; 38; 1; 26; 34; 26; 41; 26; 38; null NameSegment 26; 39; 26; 40; 26; 39; \"i\" null false 26; 41; null null BinaryExpr 27; 24; 27; 53; 27; 39; 5; NameSegment 27; 24; 27; 38; 27; 24; \"previousResult\" null ApplySuffix 27; 42; 27; 53; 27; 46; NameSegment 27; 42; 27; 46; 27; 42; \"Spec\" null null 27; 42; 27; 53; 27; 46; 1; 27; 42; 27; 53; 27; 46; null BinaryExpr 27; 47; 27; 52; 27; 49; 17; NameSegment 27; 47; 27; 48; 27; 47; \"i\" null LiteralExpr 27; 51; 27; 52; 27; 51; Int32 1; false 27; 53; null null BinaryExpr 28; 24; 28; 30; 28; 26; 8; NameSegment 28; 24; 28; 25; 28; 24; \"i\" null NameSegment 28; 29; 28; 30; 28; 29; \"n\" null null null 24; 10; 34; 11; 24; 10; 0; null 24; 10; 34; 11; 24; 10; 0; null 24; 10; 34; 11; 24; 10; null 4; AssignStatement 30; 18; 30; 23; 30; 20; null 1; NameSegment 30; 14; 30; 15; 30; 14; \"i\" null 1; ExprRhs 30; 18; 30; 23; 30; 20; null BinaryExpr 30; 18; 30; 23; 30; 20; 16; NameSegment 30; 18; 30; 19; 30; 18; \"i\" null LiteralExpr 30; 22; 30; 23; 30; 22; Int32 1; false VarDeclStmt 31; 14; 31; 53; 31; 18; null 1; 31; 14; 31; 53; 31; 18; \"addition\" UserDefinedType 31; 14; 31; 17; 31; 14; NameSegment 31; 14; 31; 17; 31; 14; \"nat\" null false AssignStatement 31; 29; 31; 52; 31; 36; null 1; IdentifierExpr 31; 14; 31; 53; 31; 18; \"addition\" 1; ExprRhs 31; 29; 31; 52; 31; 36; null BinaryExpr 31; 29; 31; 52; 31; 36; 16; NameSegment 31; 29; 31; 35; 31; 29; \"result\" null NameSegment 31; 38; 31; 52; 31; 38; \"previousResult\" null false AssignStatement 32; 31; 32; 37; 32; 31; null 1; NameSegment 32; 14; 32; 28; 32; 14; \"previousResult\" null 1; ExprRhs 32; 31; 32; 37; 32; 31; null NameSegment 32; 31; 32; 37; 32; 31; \"result\" null false AssignStatement 33; 23; 33; 31; 33; 23; null 1; NameSegment 33; 14; 33; 20; 33; 14; \"result\" null 1; ExprRhs 33; 23; 33; 31; 33; 23; null NameSegment 33; 23; 33; 31; 33; 23; \"addition\" null false BinaryExpr 24; 16; 24; 21; 24; 18; 7; NameSegment 24; 16; 24; 17; 24; 16; \"i\" null NameSegment 24; 20; 24; 21; 24; 20; \"n\" null ReturnStmt 35; 10; 35; 24; 35; 10; null 1; ExprRhs 35; 17; 35; 23; 35; 17; null NameSegment 35; 17; 35; 23; 35; 17; \"result\" null null false 0; false ";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.Set(CommonOptionBag.InputType, CommonOptionBag.InputTypeEnum.Binary);
    var reporter = new BatchErrorReporter(options);
    var output = await ProgramParser.Parse(input, new Uri("file://test.java"), reporter);
    Assert.True(output.Program != null);
  }
}