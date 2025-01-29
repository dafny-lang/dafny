// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration.Inlining;

public static class InliningTranslator {
  private static bool ShouldProcessForInlining(MemberDecl memberDecl) {
    return memberDecl.HasUserAttribute(TestGenerationOptions.TestEntryAttribute, out var _) ||
           memberDecl.HasUserAttribute(TestGenerationOptions.TestInlineAttribute, out var _);
  }

  /// <summary>
  /// Take an unresolved <param name="dafnyProgram"></param> and translate it to Boogie while enabling inlining.
  /// Return false if encountered any errors along the way
  /// </summary>
  public static bool TranslateForFutureInlining(Program dafnyProgram, DafnyOptions options, out Microsoft.Boogie.Program boogieProgram) {
    boogieProgram = null;
    // Substitute all :testInline-annotated functions with function-by-methods and remove all opaque attributes
    new AddByMethodRewriter(new ConsoleErrorReporter(options), ShouldProcessForInlining).PreResolve(dafnyProgram);
    // Remove short-circuiting expressions from method and byMethod bodies
    new RemoveShortCircuitingRewriter(ShouldProcessForInlining).PreResolve(dafnyProgram);
    // Resolve the program (in particular, resolve all function calls)
#pragma warning disable VSTHRD002
    new ProgramResolver(dafnyProgram).Resolve(CancellationToken.None).Wait(); // now resolved
#pragma warning restore VSTHRD002
    if (dafnyProgram.Reporter.HasErrors) {
      return false;
    }
    // Change by-method function calls to method calls
    new FunctionCallToMethodCallRewriter(ShouldProcessForInlining).PostResolve(dafnyProgram);
    // Separate by-method methods into standalone methods so that translator adds Call$$ procedures for them
    new SeparateByMethodRewriter(new ConsoleErrorReporter(options)).PostResolve(dafnyProgram);
    // Translate Dafny to Boogie. 
    var boogiePrograms = Utils.Translate(dafnyProgram);
    if (dafnyProgram.Reporter.HasErrors) {
      return false;
    }
    // If translation returns several modules, merge them all together to enable inlining across modules
    boogieProgram = MergeBoogiePrograms(boogiePrograms);
    // Finally, create bodies for the Call$$ procedures that call out to Impl$$ procedures
    boogieProgram = new AddImplementationsForCallsRewriter(options).VisitProgram(boogieProgram);
    // Remove proof dependency ids because they lead to errors when attempting inlining
    boogieProgram = new ProofDependencyIdRemover().VisitProgram(boogieProgram);
    return true;
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
        declarations[typeName] = [];
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

  private class ProofDependencyIdRemover : StandardVisitor {
    public override Absy Visit(Absy node) {
      if (node is ICarriesAttributes carriesAttributes) {
        carriesAttributes.Attributes = RemoveIdAttribute(carriesAttributes.Attributes, "id");
      }
      return base.Visit(node);
    }

    private QKeyValue RemoveIdAttribute(QKeyValue attributes, string attributeName) {
      if (attributes == null) {
        return null;
      }
      if (attributes.Key == attributeName) {
        return RemoveIdAttribute(attributes.Next, attributeName);
      }
      attributes.Next = RemoveIdAttribute(attributes.Next, attributeName);
      return attributes;
    }
  }

}