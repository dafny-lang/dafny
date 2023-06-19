#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Errors = Microsoft.Dafny.Errors;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  public static class Utils {

    /// <summary>
    /// Call Translator with larger stack to prevent stack overflow
    /// </summary>
    public static List<Microsoft.Boogie.Program> Translate(Program program) {
      var ret = new List<Microsoft.Boogie.Program> { };
      var thread = new System.Threading.Thread(
        () => {
          var oldPrintInstrumented = program.Reporter.Options.PrintInstrumented;
          program.Reporter.Options.PrintInstrumented = true;
          ret = Translator
            .Translate(program, program.Reporter)
            .ToList().ConvertAll(tuple => tuple.Item2);
          program.Reporter.Options.PrintInstrumented = oldPrintInstrumented;
        },
        0x10000000); // 256MB stack size to prevent stack overflow
      thread.Start();
      thread.Join();
      return ret;
    }

    /// <summary>
    /// Take a resolved type and change all names to fully-qualified.
    /// </summary>
    public static Type UseFullName(Type type) {
      return DafnyModelTypeUtils
        .ReplaceType(type, _ => true, typ => new UserDefinedType(
          new Token(),
          RemoveSystemPrefixForTuples(
            typ?.ResolvedClass?.FullName == null ?
            typ.Name :
            typ.ResolvedClass.FullName + (typ.Name.Last() == '?' ? "?" : "")),
          typ.TypeArgs));
    }

    private static string RemoveSystemPrefixForTuples(string typeName) {
      if (typeName.ToLower().StartsWith("_system._tuple#")) {
        return typeName[8..];
      }
      if (typeName.StartsWith("_System.Tuple")) {
        return "_tuple#" + typeName[13..];
      }
      return typeName;
    } 

    /// <summary>
    /// Copy a <param name="type"></param> and recursively replace type
    /// arguments named as in <param name="from"></param> with types from
    /// <param name="to"></param>.
    /// </summary>
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
      return DafnyModelTypeUtils.ReplaceType(type, _ => true,
        typ => replacements.ContainsKey(typ.Name) ?
          replacements[typ.Name] :
          new UserDefinedType(typ.tok, typ.Name, typ.TypeArgs));
    }

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static Program/*?*/ Parse(DafnyOptions options, string source, bool resolve = true, Uri uri = null) {
      uri ??= new Uri(Path.GetTempPath());
      var reporter = new BatchErrorReporter(options);

      var program = new ProgramParser().ParseFiles(uri.LocalPath, new DafnyFile[] { new(reporter.Options, uri, new StringReader(source)) },
        reporter, CancellationToken.None);

      if (!resolve) {
        return program;
      }
      new Resolver(program).ResolveProgram(program,  CancellationToken.None);
      return program;
    }

    /// <summary>
    /// Deep clone a Boogie program.
    /// </summary>
    public static Microsoft.Boogie.Program DeepCloneProgram(DafnyOptions options, Microsoft.Boogie.Program program) {
      var textRepresentation = GetStringRepresentation(options, program);
      Microsoft.Boogie.Parser.Parse(textRepresentation, "", out var copy);
      return copy;
    }

    /// <summary>
    /// Deep clone and re-resolve a Boogie program.
    /// </summary>
    public static Microsoft.Boogie.Program DeepCloneResolvedProgram(Microsoft.Boogie.Program program, DafnyOptions options) {
      program = DeepCloneProgram(options, program);
      program.Resolve(options);
      program.Typecheck(options);
      return program;
    }

    public static string GetStringRepresentation(DafnyOptions options, Microsoft.Boogie.Program program) {
      var oldPrintInstrumented = options.PrintInstrumented;
      var oldPrintFile = options.PrintFile;
      options.PrintInstrumented = true;
      options.PrintFile = "-";
      var output = new StringWriter();
      program.Emit(new TokenTextWriter(output, options));
      options.PrintInstrumented = oldPrintInstrumented;
      options.PrintFile = oldPrintFile;
      return output.ToString();
    }
    
    public static void PrintCfg(DafnyOptions options,
      Microsoft.Boogie.Program program) {
      program = DeepCloneResolvedProgram(program, options);
      var implementation = program.Implementations.First(
        implementation =>
          implementation.VerboseName.Split(" ")[0] ==
          options.TestGenOptions.TargetMethod &&
          implementation.Name.StartsWith("Impl$$"));
      using var streamWriter = new StreamWriter(options.TestGenOptions.PrintCfg);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      engine.Inline(program);
      streamWriter.Write(program.ProcessLoops(options, implementation)
        .ToDot(GetBlockId));
    }

    /// <summary>
    /// Extract the unique id assigned to the block during test generation.
    /// </summary>
    public static string GetBlockId(Block block) {
      var state = block.cmds.OfType<AssumeCmd>().FirstOrDefault(
        cmd => cmd.Attributes != null &&
               cmd.Attributes.Key == "captureState" &&
               cmd.Attributes.Params != null &&
               cmd.Attributes.Params.Count() == 1)
        ?.Attributes.Params[0].ToString();
      return state ?? block.Label;
    }

    /// <summary>
    /// Scan an unresolved dafny program to look for a specific attribute
    /// </summary>
    internal class AttributeFinder {

      public static bool ProgramHasAttribute(Program program, string attribute) {
        return DeclarationHasAttribute(program.DefaultModule, attribute);
      }

      private static bool DeclarationHasAttribute(TopLevelDecl decl, string attribute) {
        if (decl is LiteralModuleDecl moduleDecl) {
          return moduleDecl.ModuleDef.TopLevelDecls
            .Any(declaration => DeclarationHasAttribute(declaration, attribute));
        }
        if (decl is TopLevelDeclWithMembers withMembers) {
          return withMembers.Members
            .Any(member => MembersHasAttribute(member, attribute));
        }
        return false;
      }

      public static bool MembersHasAttribute(MemberDecl member, string attribute) {
        var attributes = member.Attributes;
        while (attributes != null) {
          if (attributes.Name == attribute) {
            return true;
          }
          attributes = attributes.Prev;
        }
        return false;
      }
    }
  }
}
