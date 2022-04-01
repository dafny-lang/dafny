using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit;
using Microsoft.Dafny;

namespace DafnyPipeline.Test;

[Collection("Dafny trivia tests")]
public class TriviaTest {
  public void TestPrintingTrivia(string programString) {
    var reporter = new ErrorReporterSink();
    var options = DafnyOptions.Create();
    options.ApplyDefaultOptions();
    DafnyOptions.Install(options);
    ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
    Type.ResetScopes();
    BuiltIns builtIns = new BuiltIns();
    Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
    var prog = new Program("programName", module, builtIns, reporter);
    var sw = new StringWriter();
    var printer = new Printer(sw);
    printer.PrintTopLevelDecls(prog.DefaultModuleDef.TopLevelDecls, 0, null, Path.GetFullPath(prog.FullName));
    Assert.Equal(programString, sw.GetStringBuilder().ToString().Replace("\r\n", "\n"));
  }

  [Fact]
  public void SimpleBinaryTrivia() {
    TestPrintingTrivia(@"function f(): int
{
  /*Number1*/ 1 /*opCode*/+/*Number2*/ 1
}
");
  }

  [Fact]
  public void EnsuresPrintingRestoresTrivia() {
    TestPrintingTrivia(@"
// Comment before function
function /*keyword*/test/*name*/(/*parenthesis*/x/*name*/:/*colon*/int/*type*/,/*comma*/y:int
  /*parenthesis*/)/*parenthesis2*/
  /*colon*/:/*colon2*/
  /*return type*/int/*returntype2*/
  /*opening*/{/*opening2*/
  /*leadingX*/x/*leadingX2*/+/*op1*/x/*x2*/+/*op2*/y/*y1*/
  /*closing*/}/*closing2*/
function other(): int { 1 }

const field := 1;
");
  }
}
