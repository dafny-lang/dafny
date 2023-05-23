using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace Microsoft.Dafny;

public record DfyParseResult(int ErrorCount, FileModuleDefinition Module);

public class ParseUtils {

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members) from "filename"
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner.
  ///</summary>
  public static DfyParseResult Parse(TextReader reader, Uri /*!*/ uri, BuiltIns builtIns, ErrorReporter /*!*/ errorReporter) /* throws System.IO.IOException */ {
    Contract.Requires(uri != null);
    var text = SourcePreprocessor.ProcessDirectives(reader, new List<string>());
    try {
      return Parse(text, uri, builtIns, errorReporter);
    } catch (Exception e) {
      var internalErrorDummyToken = new Token {
        Uri = uri,
        line = 1,
        col = 1,
        pos = 0,
        val = string.Empty
      };
      errorReporter.Error(MessageSource.Parser, internalErrorDummyToken,
        "[internal error] Parser exception: " + e.Message);
      throw;
    }
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members)
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner.
  ///</summary>
  public static DfyParseResult Parse(string /*!*/ s, Uri /*!*/ uri, BuiltIns builtIns, ErrorReporter reporter) {
    Contract.Requires(s != null);
    Contract.Requires(uri != null);
    Errors errors = new Errors(reporter);
    return Parse(s, uri, builtIns, errors);
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members)
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner with the given Errors sink.
  ///</summary>
  public static DfyParseResult Parse(string /*!*/ s, Uri /*!*/ uri,
    BuiltIns builtIns, Errors /*!*/ errors) {
    Parser parser = SetupParser(s, uri, builtIns, errors);
    parser.Parse();

    if (parser.theModule.DefaultClass.Members.Count == 0 && parser.theModule.Includes.Count == 0 && !parser.theModule.SourceDecls.Any()
        && (parser.theModule.PrefixNamedModules == null || parser.theModule.PrefixNamedModules.Count == 0)) {
      errors.Warning(new Token(1, 1) { Uri = uri }, "File contains no code");
    }

    return new DfyParseResult(parser.errors.ErrorCount, parser.theModule);
  }

  private static Parser SetupParser(string /*!*/ s, Uri /*!*/ uri,
    BuiltIns builtIns, Errors /*!*/ errors) {
    Contract.Requires(s != null);
    Contract.Requires(uri != null);
    Contract.Requires(errors != null);
    System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(typeof(ParseErrors).TypeHandle);
    System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(typeof(ResolutionErrors).TypeHandle);
    byte[] /*!*/
      buffer = cce.NonNull(Encoding.Default.GetBytes(s));
    MemoryStream ms = new MemoryStream(buffer, false);
    var firstToken = new Token {
      Uri = uri
    };

    // if ((module.RootToken.Filepath ?? "") == "") {
    //   // This is the first module
    //   module.RootToken.Uri = uri;
    //   firstToken = module.RootToken;
    // } else {
    //   firstToken = new Token(); // It's an included file
    // }

    Scanner scanner = new Scanner(ms, errors, uri, firstToken: firstToken);
    return new Parser(scanner, errors, builtIns);
  }

  public static Program Parse(string source, Uri uri, ErrorReporter reporter) {
    var files = new[] { new DafnyFile(reporter.Options, uri, new StringReader(source)) };
    return ParseFiles(uri.ToString(), files, reporter, CancellationToken.None);
  }

  public static Program ParseFiles(string programName, IReadOnlyList<DafnyFile> files, ErrorReporter errorReporter,
    CancellationToken cancellationToken) {
    var options = errorReporter.Options;
    var builtIns = new BuiltIns(options);
    var defaultModule = errorReporter.OuterModule;
    foreach (var dafnyFile in files) {
      if (options.Trace) {
        options.OutputWriter.WriteLine("Parsing " + dafnyFile.FilePath);
      }

      if (options.XmlSink is { IsOpen: true } && dafnyFile.Uri.IsFile) {
        options.XmlSink.WriteFileFragment(dafnyFile.Uri.LocalPath);
      }

      try {
        // We model a precompiled file, a library, as an include
        // var include = dafnyFile.IsPrecompiled ? new Include(new Token {
        //   Uri = dafnyFile.Uri,
        //   col = 1,
        //   line = 0
        // }, new Uri("cli://"), dafnyFile.Uri) : null;
        // if (include != null) {
        //   // TODO this can be removed once the include error message in ErrorReporter.Error is removed.
        //   defaultModuleDefinition.Includes.Add(include);
        // }

        var parseResult = Parse(
          dafnyFile.Content,
          dafnyFile.Uri,
          builtIns,
          errorReporter
        );

        if (parseResult.ErrorCount != 0) {
          // logger.LogDebug("encountered {ErrorCount} errors while parsing {DocumentUri}", parseResult.ErrorCount, document.Uri);
        }

        AddFileModuleToProgram(parseResult.Module, defaultModule);
        if (defaultModule.RangeToken.StartToken.Uri == null) {
          defaultModule.RangeToken = parseResult.Module.RangeToken;
        }

      } catch (Exception e) {
        var internalErrorDummyToken = new Token {
          Uri = dafnyFile.Uri,
          line = 1,
          col = 1,
          pos = 0,
          val = string.Empty
        };
        errorReporter.Error(MessageSource.Parser, internalErrorDummyToken, "[internal error] Parser exception: " + e.Message);
      }
    }

    if (!(options.DisallowIncludes || options.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate)) {
      var includedModules = TryParseIncludes(defaultModule.Includes.ToList(),
        builtIns, errorReporter, cancellationToken);

      foreach (var module in includedModules) {
        AddFileModuleToProgram(module, defaultModule);
      }
    }

    if (options.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate) {
      var dependencyMap = new DependencyMap();
      dependencyMap.AddIncludes(defaultModule.Includes);
      dependencyMap.PrintMap(options);
    }

    var verifiedRoots = files.Where(df => df.IsPreverified).Select(df => df.Uri).ToHashSet();
    var compiledRoots = files.Where(df => df.IsPrecompiled).Select(df => df.Uri).ToHashSet();
    var program = new Program(
      programName,
      new LiteralModuleDecl(errorReporter.OuterModule, null),
      builtIns,
      errorReporter, verifiedRoots, compiledRoots
    );

    DafnyMain.MaybePrintProgram(program, options.DafnyPrintFile, false);
    return program;
  }

  public static void AddFileModuleToProgram(FileModuleDefinition fileModule, DefaultModuleDefinition defaultModule) {
    foreach (var declToMove in fileModule.TopLevelDecls) {
      declToMove.EnclosingModuleDefinition = defaultModule;
      if (declToMove is LiteralModuleDecl literalModuleDecl) {
        literalModuleDecl.ModuleDef.EnclosingModule = defaultModule;
      }
      if (declToMove is DefaultClassDecl defaultClassDecl) {
        foreach (var member in defaultClassDecl.Members) {
          defaultModule.DefaultClass.Members.Add(member);
          member.EnclosingClass = defaultModule.DefaultClass;
        }
      } else {
        defaultModule.SourceDecls.Add(declToMove);
      }
    }

    foreach (var include in fileModule.Includes) {
      defaultModule.Includes.Add(include);
    }

    defaultModule.DefaultClass.SetMembersBeforeResolution();
  }

  public static IList<FileModuleDefinition> TryParseIncludes(
    IEnumerable<Include> roots,
    BuiltIns builtIns,
    ErrorReporter errorReporter,
    CancellationToken cancellationToken
  ) {
    var stack = new Stack<DafnyFile>();
    var result = new List<FileModuleDefinition>();
    var resolvedIncludes = new HashSet<Uri>();
    foreach (var root in roots) {
      resolvedIncludes.Add(root.IncluderFilename);

      var dafnyFile = IncludeToDafnyFile(builtIns, errorReporter, root);
      if (dafnyFile != null) {
        stack.Push(dafnyFile);
      }
    }

    while (stack.Any()) {
      var top = stack.Pop();
      if (!resolvedIncludes.Add(top.Uri)) {
        continue;
      }

      cancellationToken.ThrowIfCancellationRequested();
      try {
        var parseIncludeResult = Parse(
          top.Content,
          top.Uri,
          builtIns,
          errorReporter
        );
        result.Add(parseIncludeResult.Module);

        foreach (var include in parseIncludeResult.Module.Includes) {
          var dafnyFile = IncludeToDafnyFile(builtIns, errorReporter, include);
          if (dafnyFile != null) {
            stack.Push(dafnyFile);
          }
        }
      } catch (Exception) {
        // ignored
      }
    }

    return result;
  }

  private static DafnyFile IncludeToDafnyFile(BuiltIns builtIns, ErrorReporter errorReporter, Include include) {
    try {
      return new DafnyFile(builtIns.Options, include.IncludedFilename.LocalPath);
    } catch (IllegalDafnyFile) {
      errorReporter.Error(MessageSource.Parser, include.tok, $"Include of file '{include.IncludedFilename}' failed.");
      return null;
    } catch (IOException) {
      errorReporter.Error(MessageSource.Parser, include.tok,
        $"Unable to open the include {include.IncludedFilename}.");
      return null;
    }
  }
}