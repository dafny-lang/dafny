using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Errors = Microsoft.Dafny.Errors;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class Utils {

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static Program? Parse(string source, string fileName = "") {
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var builtIns = new BuiltIns();
      var reporter = new ConsoleErrorReporter();
      var success = Parser.Parse(source, fileName, fileName, null, module, builtIns,
        new Errors(reporter)) == 0 && Microsoft.Dafny.Main.ParseIncludes(module, builtIns,
        new List<string>(), new Errors(reporter)) == null;
      Program? program = null;
      if (success) {
        program = new Program(fileName, module, builtIns, reporter);
      }
      return program;
    }

    /// <summary>
    /// Restore the original name of a Dafny method from its Boogie translation
    /// </summary>
    public static string GetDafnyMethodName(string boogieName) {
      // strip the Impl$$, Call$ or CheckWellFormed$$ prefixes:
      boogieName = boogieName.Split("$").Last();
      // convert Boogie name to Dafny name:
      boogieName = new DafnyModelType(boogieName).InDafnyFormat().Name;
      // Get the name of the method:
      var methodName = boogieName.Split(".").Last();
      // Get the fully qualified name of the class\module the method is defined in:
      var classPath = boogieName
        .Substring(0, boogieName.Length - methodName.Length).TrimEnd('.');
      // Merge everything using the dot as a separator:
      var fullPath = classPath.Split(".")
        .Where(m => m != "" && m[0] != '_').Append(methodName);
      return string.Join(".", fullPath);
    }

    /// <summary>
    /// Deep clone a Boogie program.
    /// </summary>
    public static Microsoft.Boogie.Program
      DeepCloneProgram(Microsoft.Boogie.Program program) {
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      var oldPrintFile = DafnyOptions.O.PrintFile;
      DafnyOptions.O.PrintInstrumented = true;
      DafnyOptions.O.PrintFile = "-";
      var output = new StringWriter();
      program.Emit(new TokenTextWriter(output, DafnyOptions.O));
      var textRepresentation = output.ToString();
      Microsoft.Boogie.Parser.Parse(textRepresentation, "", out var copy);
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;
      DafnyOptions.O.PrintFile = oldPrintFile;
      return copy;
    }
  }
}