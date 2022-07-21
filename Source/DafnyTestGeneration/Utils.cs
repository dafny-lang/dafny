using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Errors = Microsoft.Dafny.Errors;
using Function = Microsoft.Dafny.Function;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  public static class Utils {
    
    public static Type GetNonNullable(Type type) {
      if (type is not UserDefinedType userType) {
        return type;
      }

      var newType = new UserDefinedType(new Token(), 
        userType.Name.TrimEnd('?'), userType.TypeArgs);
      if (type is DafnyModelTypeUtils.DatatypeType) {
        return new DafnyModelTypeUtils.DatatypeType(newType);
      }
      return newType;
    }

    public static Type ReplaceTypeVariables(Type type, Type with) {
      return ReplaceType(type, t => t.Name.Contains('$'), _ => with);
    }
    
    public static Type UseFullName(Type type) {
      return ReplaceType(type, _ => true, type => 
        new UserDefinedType(new Token(), type?.ResolvedClass?.FullName ?? type.Name, type.TypeArgs));
    }

    public static Type CopyWithReplacements(Type type, List<string> from, List<Type> to) {
      if (from.Count != to.Count) {
        return type;
      }
      Dictionary<string, Type> replacements = new();
      for (int i = 0; i < from.Count; i++) {
        replacements[from[i]] = to[i];
      }
      replacements["_System.string"] =
        new UserDefinedType(new Token(), "string", new List<Type>());
      replacements["_System.nat"] =
        new UserDefinedType(new Token(), "nat", new List<Type>());
      replacements["_System.object"] =
        new UserDefinedType(new Token(), "object", new List<Type>());
      return ReplaceType(type, _ => true,
        type => replacements.ContainsKey(type.Name) ? 
          replacements[type.Name] :
          new UserDefinedType(type.tok, type.Name, type.TypeArgs));
    }
    
    /// <summary>
    /// Recursively replace all types within <param>type</param> that satisfy
    /// <param>condition</param>
    /// </summary>
    public static Type ReplaceType(Type type, Func<UserDefinedType, Boolean> condition, 
      Func<UserDefinedType, Type> replacement) {
      if ((type is not UserDefinedType userType) || (type is ArrowType)) {
        return DafnyModelTypeUtils.TransformType(type, t => ReplaceType(t, condition, replacement));
      }
      var newType = condition(userType) ? replacement(userType) : type;
      newType.TypeArgs = newType.TypeArgs.ConvertAll(t => 
          DafnyModelTypeUtils.TransformType(t, t => ReplaceType(t, condition, replacement)));
      return newType;
    }

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static Program? Parse(string source, string fileName = "") {
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var builtIns = new BuiltIns();
      var reporter = new ConsoleErrorReporter();
      var success = Parser.Parse(source, fileName, fileName, null, module, builtIns,
        new Errors(reporter)) == 0 && Microsoft.Dafny.Main.ParseIncludesDepthFirstNotCompiledFirst(module, builtIns,
        new HashSet<string>(), new Errors(reporter)) == null;
      Program? program = null;
      if (success) {
        program = new Program(fileName, module, builtIns, reporter);
      }
      if (program == null) {
        return null;
      }
      // Substitute function methods with function-by-methods
      new AddByMethodRewriter(new ConsoleErrorReporter()).PreResolve(program);
      program.Reporter = new ErrorReporterSink();
      new Resolver(program).ResolveProgram(program);
      return program;
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
    
    public static string GetStringRepresentation(Microsoft.Boogie.Program program) {
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      var oldPrintFile = DafnyOptions.O.PrintFile;
      DafnyOptions.O.PrintInstrumented = true;
      DafnyOptions.O.PrintFile = "-";
      var output = new StringWriter();
      program.Emit(new TokenTextWriter(output, DafnyOptions.O));
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;
      DafnyOptions.O.PrintFile = oldPrintFile;
      return output.ToString();
    }
    
    private class AddByMethodRewriter : IRewriter {

      protected internal AddByMethodRewriter(ErrorReporter reporter) : base(reporter) { }

      /// <summary>
      /// Turns each function-method into a function-by-method.
      /// Copies body of the function into the body of the corresponding method.
      /// </summary>
      internal void PreResolve(Program program) {
        AddByMethod(program.DefaultModule);
      }

      private static void AddByMethod(TopLevelDecl d) {
        if (d is LiteralModuleDecl moduleDecl) {
          moduleDecl.ModuleDef.TopLevelDecls.ForEach(AddByMethod);
        } else if (d is TopLevelDeclWithMembers withMembers) {
          withMembers.Members.OfType<Function>().Iter(AddByMethod);
        }
      }

      private static void AddByMethod(Function func) {
        if (func.IsGhost || func.Body == null || func.ByMethodBody != null) {
          return;
        }
        var returnStatement = new ReturnStmt(new Token(), new Token(),
          new List<AssignmentRhs> { new ExprRhs(func.Body) });
        func.ByMethodBody = new BlockStmt(new Token(), new Token(),
          new List<Statement> { returnStatement });
      }
    }
  }
}