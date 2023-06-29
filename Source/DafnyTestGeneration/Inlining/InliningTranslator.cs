#nullable disable

using System.Collections.Generic;
using System.Threading;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration.Inlining; 

public static class InliningTranslator {

  /// <summary>
  /// Take an unresolved <param name="dafnyProgram"></param> and translate it to Boogie while enabling inlining.
  /// </summary>
  public static Microsoft.Boogie.Program TranslateAndInline(Program dafnyProgram, DafnyOptions options) {
    // Substitute all :testInline-annotated functions with function-by-methods and remove all opaque attributes
    new AddByMethodRewriter(new ConsoleErrorReporter(options)).PreResolve(dafnyProgram);
    // Remove short-circuiting expressions from method and byMethod bodies
    new RemoveShortCircuitingCloner().Visit(dafnyProgram);
    // Resolve the program (in particular, resolve all function calls)
    new ProgramResolver(dafnyProgram).Resolve(CancellationToken.None); // now resolved
    // Change by-method function calls to method calls
    new FunctionCallToMethodCallCloner().Visit(dafnyProgram);
    // Separate by-method methods into standalone methods so that translator adds Call$$ procedures for them
    new SeparateByMethodRewriter(new ConsoleErrorReporter(options)).PostResolve(dafnyProgram);
    // Translate Dafny to Boogie. 
    var boogiePrograms = Utils.Translate(dafnyProgram);
    // If translation returns several modules, merge them all together to enable inlining across modules
    var program = MergeBoogiePrograms(boogiePrograms);
    // Finally, create bodies for the Call$$ procedures that call out to Impl$$ procedures
    program = new AddImplementationsForCallsRewriter(options).VisitProgram(program);
    return program;
  }
  
  /// <summary>
  /// Merge Boogie Programs by removing any duplicate top level declarations
  /// </summary>
  private static Microsoft.Boogie.Program MergeBoogiePrograms(IEnumerable<Microsoft.Boogie.Program> programs) {
    // Add all top-level declarations into one program
    var program = new Microsoft.Boogie.Program();
    foreach (var p in programs) {
      program.AddTopLevelDeclarations(p.TopLevelDeclarations);
    }
    // Remove duplicates:
    var declarations = new Dictionary<string, HashSet<string/*?*/>>();
    var toRemove = new List<Microsoft.Boogie.Declaration>();
    foreach (var declaration in program.TopLevelDeclarations) {
      var typeName = declaration.GetType().Name;
      if (!declarations.ContainsKey(typeName)) {
        declarations[typeName] = new();
      }
      var declarationAsString = declaration.ToString();
      if (declarationAsString != null &&
          declarations[typeName].Contains(declarationAsString)) {
        toRemove.Add(declaration);
      } else {
        declarations[typeName].Add(declarationAsString);
      }
    }
    toRemove.ForEach(x => program.RemoveTopLevelDeclaration(x));
    return program;
  }
  
}