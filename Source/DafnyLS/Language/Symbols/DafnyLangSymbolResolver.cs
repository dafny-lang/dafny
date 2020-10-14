using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Symbol resolver that utilizes dafny-lang to resolve the symbols.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this resolver serializes all invocations.
  /// </remarks>
  internal class DafnyLangSymbolResolver : ISymbolResolver {
    // TODO accesses to the resolver may need synchronization.
    private readonly ILogger _logger;
    private readonly SemaphoreSlim _resolverMutex = new SemaphoreSlim(1);

    public DafnyLangSymbolResolver(ILogger<DafnyLangSymbolResolver> logger) {
      _logger = logger;
    }

    public async Task<CompilationUnit> ResolveSymbolsAsync(TextDocumentItem textDocument, Microsoft.Dafny.Program program, CancellationToken cancellationToken) {
      int parserErrors = GetErrorCount(program);
      if(parserErrors > 0) {
        _logger.LogTrace("document {} had {} parser errors, skipping symbol resolution", textDocument.Uri, parserErrors);
        return new CompilationUnit(program);
      }

      // TODO Check if mutual exclusion of the resolving process is necessary.
      await _resolverMutex.WaitAsync(cancellationToken);
      try {
        if(!RunDafnyResolver(textDocument, program)) {
          return new CompilationUnit(program);
        }
      } finally {
        _resolverMutex.Release();
      }
      return new SymbolDeclarationResolver(_logger, cancellationToken).ProcessProgram(program);
    }

    private static int GetErrorCount(Microsoft.Dafny.Program program) {
      return program.reporter.AllMessages[ErrorLevel.Error].Count;
    }

    private bool RunDafnyResolver(TextDocumentItem document, Microsoft.Dafny.Program program) {
      var resolver = new Resolver(program);
      resolver.ResolveProgram(program);
      int resolverErrors = GetErrorCount(program);
      if(resolverErrors > 0) {
        _logger.LogDebug("encountered {} errors while resolving {}", resolverErrors, document.Uri);
        return false;
      }
      return true;
    }

    private class SymbolDeclarationResolver {
      private readonly ILogger _logger;
      private readonly CancellationToken _cancellationToken;

      public SymbolDeclarationResolver(ILogger logger, CancellationToken cancellationToken) {
        _logger = logger;
        _cancellationToken = cancellationToken;
      }

      public CompilationUnit ProcessProgram(Microsoft.Dafny.Program program) {
        _cancellationToken.ThrowIfCancellationRequested();
        var compilationUnit = new CompilationUnit(program);
        foreach(var module in program.Modules()) {
          compilationUnit.Modules.Add(ProcessModule(compilationUnit, module));
        }
        return compilationUnit;
      }

      private ModuleSymbol ProcessModule(Symbol scope, ModuleDefinition moduleDefinition) {
        _cancellationToken.ThrowIfCancellationRequested();
        var moduleSymbol = new ModuleSymbol(scope, moduleDefinition);
        foreach(var declaration in moduleDefinition.TopLevelDecls) {
          var topLevelSymbol = ProcessTopLevelDeclaration(moduleSymbol, declaration);
          if(topLevelSymbol != null) {
            moduleSymbol.Declarations.Add(topLevelSymbol);
          }
        }
        return moduleSymbol;
      }

      private Symbol? ProcessTopLevelDeclaration(ModuleSymbol moduleSymbol, TopLevelDecl topLevelDeclaration) {
        _cancellationToken.ThrowIfCancellationRequested();
        switch(topLevelDeclaration) {
        case ClassDecl classDeclaration:
          return ProcessClassDeclaration(moduleSymbol, classDeclaration);
        default:
          _logger.LogWarning("encountered unknown top level declaration {}", topLevelDeclaration.GetType());
          return null;
        }
      }

      private ClassSymbol ProcessClassDeclaration(Symbol scope, ClassDecl classDeclaration) {
        _cancellationToken.ThrowIfCancellationRequested();
        var classSymbol = new ClassSymbol(scope, classDeclaration);
        foreach(var member in classDeclaration.Members) {
          var memberSymbol = ProcessClassMember(scope, member);
          if(memberSymbol != null) {
            // TODO upon completion, this should never be null.
            classSymbol.Members.Add(memberSymbol);
          }
        }
        return classSymbol;
      }

      private Symbol? ProcessClassMember(Symbol scope, MemberDecl memberDeclaration) {
        _cancellationToken.ThrowIfCancellationRequested();
        switch(memberDeclaration) {
        case Function function:
          return ProcessFunction(scope, function);
        case Method method:
          // TODO handle the constructors explicitely? The constructor is a sub-class of Method.
          return ProcessMethod(scope, method);
        case Field field:
          return ProcessField(scope, field);
        default:
          _logger.LogWarning("encountered unknown class member declaration {}", memberDeclaration.GetType());
          return null;
        }
      }

      private FunctionSymbol ProcessFunction(Symbol scope, Function function) {
        _cancellationToken.ThrowIfCancellationRequested();
        var functionSymbol = new FunctionSymbol(scope, function);
        foreach(var parameter in function.Formals) {
          functionSymbol.Parameters.Add(ProcessFormal(scope, parameter));
        }
        return functionSymbol;
      }

      private MethodSymbol ProcessMethod(Symbol scope, Method method) {
        _cancellationToken.ThrowIfCancellationRequested();
        var methodSymbol = new MethodSymbol(scope, method);
        foreach(var parameter in method.Ins) {
          methodSymbol.Parameters.Add(ProcessFormal(scope, parameter));
        }
        foreach(var result in method.Outs) {
          methodSymbol.Returns.Add(ProcessFormal(scope, result));
        }
        foreach(var local in GetLocalVariables(methodSymbol, method.Body)) {
          methodSymbol.Locals.Add(local);
        }
        return methodSymbol;
      }

      private IEnumerable<VariableSymbol> GetLocalVariables(Symbol symbol, BlockStmt blockStatement) {
        var localVisitor = new LocalVariableDeclarationVisitor(_logger, symbol);
        localVisitor.Visit(blockStatement);
        return localVisitor.Locals;
      }

      private FieldSymbol ProcessField(Symbol scope, Field field) {
        _cancellationToken.ThrowIfCancellationRequested();
        return new FieldSymbol(scope, field);
      }

      private VariableSymbol ProcessFormal(Symbol scope, Formal formal) {
        _cancellationToken.ThrowIfCancellationRequested();
        return new VariableSymbol(scope, formal);
      }
    }

    private class LocalVariableDeclarationVisitor : SyntaxTreeVisitor {
      private readonly ILogger _logger;
      private readonly ISymbol _scope;

      public LocalVariableDeclarationVisitor(ILogger logger, ISymbol scope) {
        // TODO support cancellation
        _logger = logger;
        _scope = scope;
      }

      public IList<VariableSymbol> Locals { get; } = new List<VariableSymbol>();

      public override void VisitUnknown(object node, Microsoft.Boogie.IToken token) {
        _logger.LogWarning("encountered unknown syntax node of type {} in {}@({},{})", node.GetType(), Path.GetFileName(token.filename), token.line, token.col);
      }

      public override void Visit(LocalVariable localVariable) {
        // TODO Adapt visitor so it supports returning values?
        Locals.Add(new VariableSymbol(_scope, localVariable));
      }
    }
  }
}
