using Microsoft.Dafny.LanguageServer.Util;
using IntervalTree;
using MediatR;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using AstElement = System.Object;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class SymbolTableFactory : ISymbolTableFactory {
    private readonly ILogger _logger;

    public SymbolTableFactory(ILogger<SymbolTableFactory> logger) {
      _logger = logger;
    }

    public SymbolTable CreateFrom(Microsoft.Dafny.Program program, CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var declarations = CreateDeclarationDictionary(compilationUnit, cancellationToken);
      var designatorVisitor = new DesignatorVisitor(_logger, program, declarations, compilationUnit, cancellationToken);
      var declarationLocationVisitor = new SymbolDeclarationLocationVisitor(cancellationToken);
      var symbolsResolved = !HasErrors(program);
      if(symbolsResolved) {
        designatorVisitor.Visit(program);
        declarationLocationVisitor.Visit(compilationUnit);
      } else {
        // TODO This is an unfortunate situation. The syntax could be correct but contain some semantic errors.
        //      However, due to the contracts of the resolver we cannot pro-actively check if certain information could be resolved or not.
        //      Therefore, we only have "all or nothing" when re-using the semantic model. Check if there is really no possibility to
        //      check if information was set without actually retrieving it (i.e., it's not possible to access the Type attribute due to a contract
        //      prohibiting it to be null).
        _logger.LogDebug("cannot create symbol table from a program with errors");
      }
      return new SymbolTable(
        compilationUnit,
        declarations,
        declarationLocationVisitor.Locations,
        designatorVisitor.SymbolLookup,
        symbolsResolved
      );
    }

    private static bool HasErrors(Microsoft.Dafny.Program program) {
      // TODO create extension method
      return program.reporter.AllMessages[ErrorLevel.Error].Count > 0;
    }

    private static IDictionary<AstElement, ILocalizableSymbol> CreateDeclarationDictionary(CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var declarations = new Dictionary<AstElement, ILocalizableSymbol>();
      foreach(var symbol in compilationUnit.GetAllDescendantsAndSelf()) {
        cancellationToken.ThrowIfCancellationRequested();
        if(symbol is ILocalizableSymbol localizableSymbol) {
          // TODO we're using try-add since it appears that nodes of the System module are re-used accross several builtins.
          // TODO Maybe refine the mapping of the "declarations".
          declarations.TryAdd(localizableSymbol.Node, localizableSymbol);
        }
      }
      return declarations;
    }

    private class DesignatorVisitor : SyntaxTreeVisitor {
      private readonly ILogger _logger;
      private readonly Microsoft.Dafny.Program _program;
      private readonly IDictionary<AstElement, ILocalizableSymbol> _declarations;
      private readonly DafnyLangTypeResolver _typeResolver;
      private readonly IDictionary<AstElement, ISymbol> _designators =  new Dictionary<AstElement, ISymbol>();
      private readonly CancellationToken _cancellationToken;

      private ISymbol _currentScope;

      public IIntervalTree<Position, ILocalizableSymbol> SymbolLookup { get; } = new IntervalTree<Position, ILocalizableSymbol>(new PositionComparer());

      public DesignatorVisitor(
          ILogger logger, Microsoft.Dafny.Program program, IDictionary<AstElement, ILocalizableSymbol> declarations, ISymbol rootScope, CancellationToken cancellationToken
      ) {
        _logger = logger;
        _program = program;
        _declarations = declarations;
        _typeResolver = new DafnyLangTypeResolver(declarations);
        _currentScope = rootScope;
        _cancellationToken = cancellationToken;
      }

      public override void VisitUnknown(object node, Microsoft.Boogie.IToken token) {
        _logger.LogWarning("encountered unknown syntax node of type {} in {}@({},{})", node.GetType(), Path.GetFileName(token.filename), token.line, token.col);
      }

      public override void Visit(ModuleDefinition moduleDefinition) {
        _cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(moduleDefinition, moduleDefinition.tok, () => base.Visit(moduleDefinition));
      }

      public override void Visit(ClassDecl classDeclaration) {
        _cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(classDeclaration, classDeclaration.tok, () => base.Visit(classDeclaration));
      }

      public override void Visit(Method method) {
        _cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(method, method.tok, () => base.Visit(method));
      }

      public override void Visit(Function function) {
        _cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(function, function.tok, () => base.Visit(function));
      }

      public override void Visit(ExprDotName expressionDotName) {
        base.Visit(expressionDotName);
        if(_typeResolver.TryGetTypeSymbol(expressionDotName.Lhs, out var leftHandSideType)) {
          RegisterDesignator(leftHandSideType, expressionDotName, expressionDotName.tok, expressionDotName.SuffixName);
        }
      }

      public override void Visit(NameSegment nameSegment) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(_currentScope, nameSegment, nameSegment.tok, nameSegment.Name);
      }

      public override void Visit(TypeRhs typeRhs) {
        // TODO get the name of the type
        // TODO the token is pointing to the "new" keyword.
        //RegisterDesignator(_currentScope, typeRhs, typeRhs.Tok, typeRhs.Type.ToString());
        base.Visit(typeRhs);
      }

      private void RegisterDesignator(ISymbol scope, AstElement node, Microsoft.Boogie.IToken token, string identifier) {
        var symbol = GetDeclaration(scope, identifier);
        if(symbol != null) {
          var range = token.GetLspRange();
          SymbolLookup.Add(range.Start, range.End, symbol);
          _designators.Add(node, symbol);
        } else {
          _logger.LogWarning("could not resolve the symbol of designator named {} in {}@({},{})", identifier, Path.GetFileName(token.filename), token.line, token.col);
        }
      }

      private void ProcessNestedScope(AstElement node, Microsoft.Boogie.IToken token, System.Action visit) {
        if(!_program.IsPartOfEntryDocument(token)) {
          return;
        }
        var oldScope = _currentScope;
        _currentScope = _declarations[node];
        visit();
        _currentScope = oldScope;
      }

      private ILocalizableSymbol? GetDeclaration(ISymbol scope, string identifier) {
        var currentScope = scope;
        while(currentScope != null) {
          foreach(var child in currentScope.Children.OfType<ILocalizableSymbol>()) {
            _cancellationToken.ThrowIfCancellationRequested();
            if(child.Identifier == identifier) {
              return child;
            }
          }
          currentScope = currentScope.Scope;
        }
        return null;
      }
    }

    private class SymbolDeclarationLocationVisitor : ISymbolVisitor<Unit> {
      private readonly CancellationToken _cancellationToken;

      public IDictionary<ISymbol, SymbolLocation> Locations { get; } = new Dictionary<ISymbol, SymbolLocation>();

      public SymbolDeclarationLocationVisitor(CancellationToken cancellationToken) {
        _cancellationToken = cancellationToken;
      }

      public Unit Visit(ISymbol symbol) {
        symbol.Accept(this);
        return Unit.Value;
      }

      public Unit Visit(CompilationUnit compilationUnit) {
        VisitChildren(compilationUnit);
        return Unit.Value;
      }

      public Unit Visit(ModuleSymbol moduleSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          moduleSymbol,
          moduleSymbol.Declaration.tok,
          moduleSymbol.Declaration.tok.GetLspRange(),
          new Range(moduleSymbol.Declaration.tok.GetLspPosition(), moduleSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(moduleSymbol);
        return Unit.Value;
      }

      public Unit Visit(ClassSymbol classSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          classSymbol,
          classSymbol.Declaration.tok,
          classSymbol.Declaration.tok.GetLspRange(),
          new Range(classSymbol.Declaration.tok.GetLspPosition(), classSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(classSymbol);
        return Unit.Value;
      }

      public Unit Visit(FieldSymbol fieldSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          fieldSymbol,
          fieldSymbol.Declaration.tok,
          fieldSymbol.Declaration.tok.GetLspRange(),
          new Range(fieldSymbol.Declaration.tok.GetLspPosition(), fieldSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(fieldSymbol);
        return Unit.Value;
      }

      public Unit Visit(FunctionSymbol functionSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          functionSymbol,
          functionSymbol.Declaration.tok,
          functionSymbol.Declaration.tok.GetLspRange(),
          new Range(functionSymbol.Declaration.tok.GetLspPosition(), functionSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(functionSymbol);
        return Unit.Value;
      }

      public Unit Visit(MethodSymbol methodSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          methodSymbol,
          methodSymbol.Declaration.tok,
          methodSymbol.Declaration.tok.GetLspRange(),
          new Range(methodSymbol.Declaration.tok.GetLspPosition(), methodSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(methodSymbol);
        return Unit.Value;
      }

      public Unit Visit(VariableSymbol variableSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          variableSymbol,
          variableSymbol.Declaration.Tok,
          variableSymbol.Declaration.Tok.GetLspRange(),
          variableSymbol.Declaration.Tok.GetLspRange()
        );
        VisitChildren(variableSymbol);
        return Unit.Value;
      }

      private void VisitChildren(ISymbol symbol) {
        foreach(var child in symbol.Children) {
          child.Accept(this);
        }
      }

      private void RegisterLocation(ISymbol symbol, Microsoft.Boogie.IToken token, Range identifier, Range declaration) {
        if(token.filename != null) {
          // The filename is null if we have a default or System based symbol. This is also reflected by the ranges being usually -1.
          Locations.Add(symbol, new SymbolLocation(DocumentUri.FromFileSystemPath(token.filename), identifier, declaration));
        }
      }
    }
  }
}
