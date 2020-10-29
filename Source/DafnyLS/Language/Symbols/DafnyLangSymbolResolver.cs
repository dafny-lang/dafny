using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Symbol resolver that utilizes dafny-lang to resolve the symbols.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this resolver serializes all invocations.
  /// </remarks>
  public class DafnyLangSymbolResolver : ISymbolResolver {
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

      // TODO Check if mutual exclusion of the resolution process is necessary.
      await _resolverMutex.WaitAsync(cancellationToken);
      try {
        if(!RunDafnyResolver(textDocument, program)) {
          // We cannot proceeed without a successful resolution. Due to the contracts in dafny-lang, we cannot
          // access a property without potential contract violations. For example, a variable may have an
          // unresolved type represented by null. However, the contract prohibits the use of the type property
          // because it must not be null.
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
        // TODO program.CompileModules would probably more suitable here, since we want the symbols of the System module as well.
        //      However, it appears that the AST of program.CompileModules does not hold the correct location of the nodes - at least of the declarations.
        foreach(var module in program.Modules()) {
          compilationUnit.Modules.Add(ProcessModule(compilationUnit, module));
        }
        compilationUnit.Modules.Add(ProcessModule(compilationUnit, program.BuiltIns.SystemModule));
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
          var memberSymbol = ProcessClassMember(classSymbol, member);
          if(memberSymbol != null) {
            // TODO upon completion, this should never be null.
            classSymbol.Members.Add(memberSymbol);
          }
        }
        return classSymbol;
      }

      private Symbol? ProcessClassMember(ClassSymbol scope, MemberDecl memberDeclaration) {
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

      private IEnumerable<VariableSymbol> GetLocalVariables(Symbol symbol, BlockStmt? blockStatement) {
        if(blockStatement == null) {
          // TODO capture all syntax node null possibilities in the visitor?
          return Enumerable.Empty<VariableSymbol>();
        }
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

      public IList<VariableSymbol> Locals { get; } = new List<VariableSymbol>();

      public LocalVariableDeclarationVisitor(ILogger logger, ISymbol scope) {
        // TODO support cancellation
        _logger = logger;
        _scope = scope;
      }

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
