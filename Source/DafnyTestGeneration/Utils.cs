// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging.Abstractions;
using Declaration = Microsoft.Boogie.Declaration;
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
      var thread = new Thread(
        () => {
          var oldPrintInstrumented = program.Reporter.Options.PrintInstrumented;
          program.Reporter.Options.PrintInstrumented = true;
          ret = BoogieGenerator
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
          DafnyModelTypeUtils.ConvertTupleName(
            typ?.ResolvedClass?.FullName == null ?
            typ.Name :
            typ.ResolvedClass.FullName + (typ.Name.Last() == '?' ? "?" : "")),
          typ.TypeArgs));
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
        new UserDefinedType(new Token(), "string", []);
      replacements["_System.nat"] =
        new UserDefinedType(new Token(), "nat", []);
      replacements["_System.object"] =
        new UserDefinedType(new Token(), "object", []);
      return DafnyModelTypeUtils.ReplaceType(type, _ => true,
        typ => replacements.TryGetValue(typ.Name, out var replacement) ?
          replacement :
          new UserDefinedType(typ.Origin, typ.Name, typ.TypeArgs));
    }

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static async Task<Program> /*?*/ Parse(ErrorReporter reporter, string source, bool resolve = true, Uri uri = null, CancellationToken cancellationToken = default) {
      uri ??= new Uri(Path.Combine(Path.GetTempPath(), "parseUtils.dfy"));

      var fs = new InMemoryFileSystem(ImmutableDictionary<Uri, string>.Empty.Add(uri, source));
      var dafnyFile = DafnyFile.HandleDafnyFile(fs, reporter, reporter.Options, uri, Token.NoToken, false);
      var parseResult = await new ProgramParser(NullLogger<ProgramParser>.Instance, OnDiskFileSystem.Instance).ParseFiles(uri.LocalPath,
        new[] { dafnyFile }, reporter, cancellationToken);

      if (!resolve) {
        return parseResult.Program;
      }
      await new ProgramResolver(parseResult.Program).Resolve(cancellationToken);
      return parseResult.Program;
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
      var resolutionErrors = program.Resolve(options);
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

    /// <summary>
    /// Extract string mapping this basic block to a location in Dafny code.
    /// </summary>
    public static string GetBlockId(Block block, DafnyOptions options) {
      return AllBlockIds(block, options).FirstOrDefault((string)null);
    }

    /// <summary>
    /// Extract string mapping this basic block to locations in Dafny code.
    /// </summary>
    [ItemCanBeNull]
    public static List<string> AllBlockIds(Block block, DafnyOptions options) {
      string uniqueId = options.TestGenOptions.Mode != TestGenerationOptions.Modes.Block ? "#" + block.UniqueId : "";
      var state = block.Cmds.OfType<AssumeCmd>()
        .Where(
          cmd => cmd.Attributes != null &&
                 cmd.Attributes.Key == "captureState" &&
                 cmd.Attributes.Params != null &&
                 cmd.Attributes.Params.Count() == 1)
        .Select(
          cmd => cmd.Attributes.Params[0].ToString())
        .Select(cmd => Regex.Replace(cmd, @"\s+", "") + uniqueId);
      return state.ToList();
    }

    public static IList<object> GetAttributeValue(Implementation implementation, string attribute) {
      var attributes = implementation.Attributes;
      while (attributes != null) {
        if (attributes.Key == attribute) {
          return attributes.Params;
        }
        attributes = attributes.Next;
      }
      return new List<object>();
    }

    public static bool DeclarationHasAttribute(Declaration declaration, string attribute) {
      var attributes = declaration.Attributes;
      while (attributes != null) {
        if (attributes.Key == attribute) {
          return true;
        }
        attributes = attributes.Next;
      }
      return false;
    }

    public static bool ProgramHasAttribute(Program program, string attribute) {
      return AllMemberDeclarationsWithAttribute(program.DefaultModule, attribute).Count() != 0;
    }

    public static IEnumerable<MemberDecl> AllMemberDeclarationsWithAttribute(TopLevelDecl decl, string attribute) {
      HashSet<MemberDecl> allInlinedDeclarations = [];
      if (decl is LiteralModuleDecl moduleDecl) {
        foreach (var child in moduleDecl.ModuleDef.Children.OfType<TopLevelDecl>()) {
          allInlinedDeclarations.UnionWith(AllMemberDeclarationsWithAttribute(child, attribute));
        }
      }
      if (decl is TopLevelDeclWithMembers withMembers) {
        foreach (var memberDecl in withMembers.Members) {
          if (memberDecl.HasUserAttribute(attribute, out var _)) {
            allInlinedDeclarations.Add(memberDecl);
          }
        }
      }
      return allInlinedDeclarations;
    }
  }
}
