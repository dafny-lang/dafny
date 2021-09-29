using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit;
using BoogieProgram = Microsoft.Boogie.Program;
using Parser = Microsoft.Dafny.Parser;

namespace DafnyPipeline.Test {

  public class IntraMethodVerificationStability {
    [Fact]
    public void NoUniqueLinesWhenConcatenatingUnrelatedPrograms() {
      var program = $@"
datatype Friends = Agnes | Agatha | Jermaine

function SomeFunc(funcFormal: int): nat {{ 3 }}

method SomeMethod(methodFormal: int) returns (result: bool)
  ensures result == true 
{{
  result := methodFormal == 3;
}}
";

      var renamedProgram = $@"
datatype Friends2 = Agnes2 | Agatha2 | Jermaine2

function SomeFunc2(funcFormal: int): nat {{ 3 }}

method SomeMethod2(methodFormal: int) returns (result: bool) 
  ensures result == true
{{
  result := methodFormal == 3;
}}
";

      DafnyOptions.Install(new DafnyOptions());

      var regularBoogie = GetBoogieText(program);
      var renamedBoogie = GetBoogieText(renamedProgram);
      var separate = UniqueNonCommentLines(regularBoogie + renamedBoogie);
      var combinedBoogie = GetBoogieText(program + renamedProgram);
      var together = UniqueNonCommentLines(combinedBoogie);

      var uniqueLines = separate.Union(together).Except(separate.Intersect(together)).ToList();
      Assert.Equal(Enumerable.Empty<string>(), uniqueLines);
    }

    ISet<string> UniqueNonCommentLines(string input) {
      return input.Split('\n').Where(line => !line.TrimStart().StartsWith("//")).ToHashSet();
    }

    string PrintBoogie(BoogieProgram program) {
      var result = new StringWriter();
      var writer = new TokenTextWriter(result);
      program.Emit(writer);
      return result.ToString();
    }

    string GetBoogieText(string dafnyProgramText) {
      return string.Join('\n', GetBoogie(dafnyProgramText).Select(PrintBoogie));
    }

    IEnumerable<BoogieProgram> GetBoogie(string dafnyProgramText) {
      var module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var fullFilePath = "foo";
      var builtIns = new BuiltIns();
      var errorReporter = new ConsoleErrorReporter();
      var parseResult = Parser.Parse(dafnyProgramText, fullFilePath, "foo", module, builtIns, errorReporter);
      Assert.Equal(0, parseResult);
      var dafnyProgram = new Microsoft.Dafny.Program(fullFilePath, module, builtIns, errorReporter);
      Main.Resolve(dafnyProgram, errorReporter);
      var boogiePrograms = Translator.Translate(dafnyProgram, errorReporter).Select(t => t.Item2);
      return boogiePrograms;
    }
  }


}