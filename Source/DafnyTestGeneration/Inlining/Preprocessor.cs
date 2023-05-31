#nullable disable

using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration.Inlining; 

public static class Preprocessor {

  /// <summary>
  /// Precondition: dafnyProgram must not be resolved
  /// </summary>
  public static Microsoft.Boogie.Program PreprocessDafny(Program dafnyProgram, DafnyOptions options, Uri uri = null) {
    uri ??= new Uri(Path.GetTempPath());
    var defaultModuleDefinition = new DefaultModuleDefinition(new List<Uri>() { uri });
    // Substitute functions with function-by-methods
    new AddByMethodRewriter(new ConsoleErrorReporter(options, defaultModuleDefinition)).PreResolve(dafnyProgram);
    // Remove short-circuiting expressions from method bodies
    new RemoveShortCircuitingRewriter().Visit(dafnyProgram);
    // Resolve to figure out where all function calls are
    new Resolver(dafnyProgram).ResolveProgram(dafnyProgram); // now resolved
    // Change by-method function calls to method calls
    new FunctionCallToMethodCallRewriter().Visit(dafnyProgram);
    new SeparateByMethodRewriter(new ConsoleErrorReporter(options, defaultModuleDefinition)).PostResolve(dafnyProgram);
    // Translate Dafny to Boogie. 
    var boogiePrograms = Utils.Translate(dafnyProgram);
    var program = MergeBoogiePrograms(options, boogiePrograms);
    // Finally, create bodies for the call-annotated procedures
    program = new AddImplementationsForCallsRewriter(options).VisitProgram(program);
    return program;
  }
  
  /// <summary>
  /// Merge Boogie Programs by removing any duplicate top level declarations
  /// </summary>
  private static Microsoft.Boogie.Program MergeBoogiePrograms(DafnyOptions options, IEnumerable<Microsoft.Boogie.Program> programs) {
    // Merge all programs into one first:
    var program = new Microsoft.Boogie.Program();
    foreach (var p in programs) {
      program.AddTopLevelDeclarations(p.TopLevelDeclarations);
    }
    // Remove duplicates afterwards:
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