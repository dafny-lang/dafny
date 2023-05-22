using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Parser implementation that makes use of the parse of dafny-lang. It may only be initialized exactly once since
  /// it requires initial setup of static members.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this parser serializes all invocations.
  /// </remarks>
  public sealed class DafnyLangParser : IDafnyParser, IDisposable {
    private readonly DafnyOptions options;
    private readonly ILogger logger;
    private readonly SemaphoreSlim mutex = new(1);

    private DafnyLangParser(DafnyOptions options, ILogger<DafnyLangParser> logger) {
      this.options = options;
      this.logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the parser.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this parser instance.</param>
    /// <returns>A safely created dafny parser instance.</returns>
    public static DafnyLangParser Create(DafnyOptions options, ILogger<DafnyLangParser> logger) {
      return new DafnyLangParser(options, logger);
    }

    public Dafny.Program CreateUnparsed(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);
      try {
        return NewDafnyProgram(document, errorReporter);
      }
      finally {
        mutex.Release();
      }
    }

    public Dafny.Program Parse(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);
      var program = NewDafnyProgram(document, errorReporter);
      try {
        var parseResult = ParseUtils.Parse(
          document.Text,
          // We use the full path as filename so we can better re-construct the DocumentUri for the definition lookup.
          document.Uri.ToUri(),
          program.BuiltIns,
          errorReporter
        );
        if (parseResult.ErrorCount != 0) {
          logger.LogDebug("encountered {ErrorCount} errors while parsing {DocumentUri}", parseResult.ErrorCount, document.Uri);
        }

        AddFileModuleToProgram(parseResult.Module, program);
        program.DefaultModule.RangeToken = parseResult.Module.RangeToken;
        
        var includedModules = TryParseIncludesOfModule(document.Uri, parseResult.Module, 
          program.BuiltIns, errorReporter, cancellationToken);

        foreach (var module in includedModules) {
          AddFileModuleToProgram(module, program);
        }

        return program;
      } catch (Exception e) {
        logger.LogDebug(e, "encountered an exception while parsing {DocumentUri}", document.Uri);
        var internalErrorDummyToken = new Token {
          Uri = document.Uri.ToUri(),
          line = 1,
          col = 1,
          pos = 0,
          val = string.Empty
        };
        errorReporter.Error(MessageSource.Parser, internalErrorDummyToken, "[internal error] Parser exception: " + e.Message);
        return program;
      }
      finally {
        mutex.Release();
      }
    }

    private static void AddFileModuleToProgram(FileModuleDefinition module, Dafny.Program program)
    {
      foreach (var topLevelDecl in module.TopLevelDecls)
      {
        if (topLevelDecl is DefaultClassDecl defaultClassDecl)
        {
          foreach (var member in defaultClassDecl.Members)
          {
            program.DefaultModuleDef.DefaultClass.Members.Add(member);
          }
        }
        else
        {
          program.DefaultModuleDef.TopLevelDecls.Add(topLevelDecl);
        }
      }

      foreach (var include in module.Includes)
      {
        program.Includes.Add(include);
      }
      
      program.DefaultModuleDef.DefaultClass.SetMembersBeforeResolution();
    }

    private Dafny.Program NewDafnyProgram(TextDocumentItem document, ErrorReporter errorReporter) {
      // Ensure that the statically kept scopes are empty when parsing a new document.
      Type.ResetScopes();
      return new Dafny.Program(
        document.Uri.ToString(),
        new LiteralModuleDecl(errorReporter.OuterModule, null),
        // BuiltIns cannot be initialized without Type.ResetScopes() before.
        new BuiltIns(errorReporter.Options),
        errorReporter, Sets.Empty<Uri>(), Sets.Empty<Uri>()
      );
    }

    public void Dispose() {
      mutex.Dispose();
    }

    // TODO The following methods are based on the ones from DafnyPipeline/DafnyMain.cs.
    //      It could be convenient to adapt them in the main-repo so location info could be extracted.
    private IList<FileModuleDefinition> TryParseIncludesOfModule(
      DocumentUri root,
      FileModuleDefinition rootModule,
      BuiltIns builtIns,
      ErrorReporter errorReporter,
      CancellationToken cancellationToken
    ) {
      var errors = new Errors(errorReporter);

      var result = new List<FileModuleDefinition>();
      var resolvedIncludes = new HashSet<Uri>();
      resolvedIncludes.Add(root.ToUri());

      var stack = new Stack<DafnyFile>();
      foreach (var include in rootModule.Includes) {
        var dafnyFile = IncludeToDafnyFile(builtIns, errorReporter, include);
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
        var parseIncludeResult = TryParseDocument(top, builtIns, errorReporter, errors);
        result.Add(parseIncludeResult.Module);
        
        foreach (var include in parseIncludeResult.Module.Includes) {
          var dafnyFile = IncludeToDafnyFile(builtIns, errorReporter, include);
          if (dafnyFile != null) {
            stack.Push(dafnyFile);
          }
        }
      }

      return result;
    }

    private DafnyFile? IncludeToDafnyFile(BuiltIns builtIns, ErrorReporter errorReporter, Include include)
    {
      try
      {
        return new DafnyFile(builtIns.Options, include.IncludedFilename.LocalPath);
      }
      catch (IllegalDafnyFile e)
      {
        errorReporter.Error(MessageSource.Parser, include.tok, $"Include of file '{include.IncludedFilename}' failed.");
        logger.LogDebug(e, "encountered include of illegal dafny file {Filename}", include.IncludedFilename);
        return null;
      }
      catch (IOException e)
      {
        errorReporter.Error(MessageSource.Parser, include.tok,
          $"Unable to open the include {include.IncludedFilename}.");
        logger.LogDebug(e, "could not open file {Filename}", include.IncludedFilename);
        return null;
      }
    }

    private DfyParseResult TryParseDocument(DafnyFile dafnyFile, BuiltIns builtIns, ErrorReporter errorReporter,
      Errors errors) {
      return ParseUtils.Parse(
        dafnyFile.Content,
        dafnyFile.Uri,
        builtIns,
        errors
      );
    }
  }
}
