using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test {
  [Collection("Singleton Test Collection - Trivia")]
  public class Trivia {
    [Fact]
    public void Test() {
      ErrorReporter reporter = new ConsoleErrorReporter();
      var options = DafnyOptions.Create();
      options.DafnyPrelude = "../../../../../Binaries/DafnyPrelude.bpl";
      DafnyOptions.Install(options);

      var programString = @"
/** Trait docstring */
trait Trait1 { }

// Just a comment
trait Trait2 extends Trait1
// Trait docstring
{ }
// This is attached to trait2

// This is attached to n
type n = x: int | x % 2 == 0
// This is attached to n as well

// Just a comment
class Class1 extends Trait1
// Class docstring
{ }
// This is attached to the class

// Comment attached to c
const c := 2;
// Docstring attached to c

// This is attached to f
function f(): int
// This is f docstring
ensures true
{ 1 }

/** This is the docstring */
function g(): int
// This is not the docstring
ensures true
{ 1 }

// Just a regular comment
method m() returns (r: int)
// This is the docstring
ensures true
{ assert true; }
";
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      Microsoft.Dafny.Type.ResetScopes();
      BuiltIns builtIns = new BuiltIns();
      Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
      var dafnyProgram = new Program("programName", module, builtIns, reporter);
      Assert.Equal(0, reporter.ErrorCount);
      Assert.Equal(5, dafnyProgram.DefaultModuleDef.TopLevelDecls.Count);
      var trait1 = dafnyProgram.DefaultModuleDef.TopLevelDecls[0];
      var trait2 = dafnyProgram.DefaultModuleDef.TopLevelDecls[1];
      var subsetType = dafnyProgram.DefaultModuleDef.TopLevelDecls[2];
      var class1 = dafnyProgram.DefaultModuleDef.TopLevelDecls[3] as ClassDecl;
      var defaultClass = dafnyProgram.DefaultModuleDef.TopLevelDecls[4] as ClassDecl;
      Assert.NotNull(class1);
      Assert.NotNull(defaultClass);
      Assert.Equal(4, defaultClass.Members.Count);
      var c = defaultClass.Members[0];
      var f = defaultClass.Members[1];
      var g = defaultClass.Members[2];
      var m = defaultClass.Members[3];
      Assert.Equal("\n/** Trait docstring */\n", trait1.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("// Just a comment\n", trait2.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("\n// Trait docstring\n", trait2.TokenBeforeDocstring.trailingTrivia);
      Assert.Equal("// This is attached to n\n", subsetType.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("\n// This is attached to n as well\n\n", subsetType.TokenBeforeDocstring.trailingTrivia);
      Assert.Equal("// Just a comment\n", class1.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("\n// Class docstring\n", class1.TokenBeforeDocstring.trailingTrivia);
      Assert.Equal("// Comment attached to c\n", c.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("\n// Docstring attached to c\n\n", c.TokenBeforeDocstring.trailingTrivia);
      Assert.Equal("// This is attached to f\n", f.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("\n// This is f docstring\n", f.TokenBeforeDocstring.trailingTrivia);
      Assert.Equal("/** This is the docstring */\n", g.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("\n// This is not the docstring\n", g.TokenBeforeDocstring.trailingTrivia);
      Assert.Equal("// Just a regular comment\n", m.FirstDeclarationToken.leadingTrivia);
      Assert.Equal("\n// This is the docstring\n", m.TokenBeforeDocstring.trailingTrivia);

      Assert.True(true);
    }
  }
}
