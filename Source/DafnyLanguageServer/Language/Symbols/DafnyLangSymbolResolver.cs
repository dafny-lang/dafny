using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
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
    private readonly SemaphoreSlim _resolverMutex = new(1);

    public DafnyLangSymbolResolver(ILogger<DafnyLangSymbolResolver> logger) {
      _logger = logger;
    }

    public async Task<CompilationUnit> ResolveSymbolsAsync(TextDocumentItem textDocument, Dafny.Program program, CancellationToken cancellationToken) {
      // TODO The resolution requires mutual exclusion since it sets static variables of classes like Microsoft.Dafny.Type.
      //      Although, the variables are marked "ThreadStatic" - thus it might not be necessary. But there might be
      //      other classes as well.
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

    private static int GetErrorCount(Dafny.Program program) {
      return program.reporter.AllMessages[ErrorLevel.Error].Count;
    }

    private bool RunDafnyResolver(TextDocumentItem document, Dafny.Program program) {
      var resolver = new Resolver(program);
      resolver.ResolveProgram(program);
      int resolverErrors = GetErrorCount(program);
      if(resolverErrors > 0) {
        _logger.LogDebug("encountered {ErrorCount} errors while resolving {DocumentUri}", resolverErrors, document.Uri);
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

      public CompilationUnit ProcessProgram(Dafny.Program program) {
        _cancellationToken.ThrowIfCancellationRequested();
        var compilationUnit = new CompilationUnit(program);
        // program.CompileModules would probably more suitable here, since we want the symbols of the System module as well.
        // However, it appears that the AST of program.CompileModules does not hold the correct location of the nodes - at least of the declarations.
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
          return ProcessClass(moduleSymbol, classDeclaration);
        case LiteralModuleDecl literalModuleDeclaration:
          return ProcessModule(moduleSymbol, literalModuleDeclaration.ModuleDef);
        case ValuetypeDecl valueTypeDeclaration:
          return ProcessValueType(moduleSymbol, valueTypeDeclaration);
        default:
          _logger.LogDebug("encountered unknown top level declaration {Name} of type {Type}", topLevelDeclaration.Name, topLevelDeclaration.GetType());
          return null;
        }
      }

      private ClassSymbol ProcessClass(Symbol scope, ClassDecl classDeclaration) {
        _cancellationToken.ThrowIfCancellationRequested();
        var classSymbol = new ClassSymbol(scope, classDeclaration);
        foreach(var member in classDeclaration.Members) {
          var memberSymbol = ProcessClassMember(classSymbol, member);
          if(memberSymbol != null) {
            // TODO When respecting all possible class members, this should never be null.
            classSymbol.Members.Add(memberSymbol);
          }
        }
        return classSymbol;
      }

      private ValueTypeSymbol ProcessValueType(Symbol scope, ValuetypeDecl valueTypeDecarlation) {
        _cancellationToken.ThrowIfCancellationRequested();
        return new ValueTypeSymbol(scope, valueTypeDecarlation);
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
          // TODO The last missing member is AmbiguousMemberDecl which is created by the resolver.
          //      When is this class exactly used?
          _logger.LogDebug("encountered unknown class member declaration {DeclarationType}", memberDeclaration.GetType());
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
        ProcessAndRegisterMethodBody(methodSymbol, method.Body);
        return methodSymbol;
      }

      private void ProcessAndRegisterMethodBody(MethodSymbol methodSymbol, BlockStmt? blockStatement) {
        if(blockStatement == null) {
          return;
        }
        var rootBlock = new ScopeSymbol(methodSymbol, blockStatement);
        var localVisitor = new LocalVariableDeclarationVisitor(_logger, rootBlock);
        localVisitor.Resolve(blockStatement);
        methodSymbol.Block = rootBlock;
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

      private ScopeSymbol _block;

      public LocalVariableDeclarationVisitor(ILogger logger, ScopeSymbol rootBlock) {
        // TODO support cancellation
        _logger = logger;
        _block = rootBlock;
      }

      public void Resolve(BlockStmt blockStatement) {
        // The base is directly visited to avoid doubly nesting the root block of the method.
        base.Visit(blockStatement);
      }

      public override void VisitUnknown(object node, Boogie.IToken token) {
        _logger.LogDebug("encountered unknown syntax node of type {NodeType} in {Filename}@({Line},{Column})",
          node.GetType(), Path.GetFileName(token.filename), token.line, token.col);
      }

      public override void Visit(BlockStmt blockStatement) {
        var oldBlock = _block;
        _block = new ScopeSymbol(_block, blockStatement);
        oldBlock.Symbols.Add(_block);
        base.Visit(blockStatement);
        _block = oldBlock;
      }

      public override void Visit(LocalVariable localVariable) {
        _block.Symbols.Add(new VariableSymbol(_block, localVariable));
      }
    }
  }
}
