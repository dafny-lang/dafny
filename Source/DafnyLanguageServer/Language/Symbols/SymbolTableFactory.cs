using IntervalTree;
using MediatR;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using AstElement = System.Object;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class SymbolTableFactory : ISymbolTableFactory {
    private readonly ILogger _logger;

    public SymbolTableFactory(ILogger<SymbolTableFactory> logger) {
      _logger = logger;
    }

    public SymbolTable CreateFrom(Dafny.Program program, CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var declarations = CreateDeclarationDictionary(compilationUnit, cancellationToken);
      var designatorVisitor = new DesignatorVisitor(_logger, program, declarations, compilationUnit, cancellationToken);
      var declarationLocationVisitor = new SymbolDeclarationLocationVisitor(cancellationToken);
      var symbolsResolved = !program.reporter.HasErrors;
      if (symbolsResolved) {
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

    private static IDictionary<AstElement, ILocalizableSymbol> CreateDeclarationDictionary(CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var declarations = new Dictionary<AstElement, ILocalizableSymbol>();
      foreach (var symbol in compilationUnit.GetAllDescendantsAndSelf()) {
        cancellationToken.ThrowIfCancellationRequested();
        if (symbol is ILocalizableSymbol localizableSymbol) {
          // TODO we're using try-add since it appears that nodes of the System module are re-used accross several builtins.
          // TODO Maybe refine the mapping of the "declarations".
          declarations.TryAdd(localizableSymbol.Node, localizableSymbol);
        }
      }
      return declarations;
    }

    private class DesignatorVisitor : SyntaxTreeVisitor {
      private readonly ILogger _logger;
      private readonly Dafny.Program _program;
      private readonly IDictionary<AstElement, ILocalizableSymbol> _declarations;
      private readonly DafnyLangTypeResolver _typeResolver;
      private readonly IDictionary<AstElement, ISymbol> _designators = new Dictionary<AstElement, ISymbol>();
      private readonly CancellationToken _cancellationToken;

      private ISymbol _currentScope;

      public IIntervalTree<Position, ILocalizableSymbol> SymbolLookup { get; } = new IntervalTree<Position, ILocalizableSymbol>();

      public DesignatorVisitor(
          ILogger logger, Dafny.Program program, IDictionary<AstElement, ILocalizableSymbol> declarations, ISymbol rootScope, CancellationToken cancellationToken
      ) {
        _logger = logger;
        _program = program;
        _declarations = declarations;
        _typeResolver = new DafnyLangTypeResolver(declarations);
        _currentScope = rootScope;
        _cancellationToken = cancellationToken;
      }

      public override void VisitUnknown(object node, Boogie.IToken token) {
        _logger.LogDebug("encountered unknown syntax node of type {NodeType} in {Filename}@({Line},{Column})",
          node.GetType(), token.GetDocumentFileName(), token.line, token.col);
      }

      public override void Visit(ModuleDefinition moduleDefinition) {
        _cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(moduleDefinition, moduleDefinition.tok, () => base.Visit(moduleDefinition));
      }

      public override void Visit(ClassDecl classDeclaration) {
        VisitTopLevelDeclarationWithMembers(classDeclaration, () => base.Visit(classDeclaration));
      }

      public override void Visit(DatatypeDecl datatypeDeclaration) {
        VisitTopLevelDeclarationWithMembers(datatypeDeclaration, () => base.Visit(datatypeDeclaration));
      }

      private void VisitTopLevelDeclarationWithMembers(TopLevelDeclWithMembers declaration, System.Action visit) {
        _cancellationToken.ThrowIfCancellationRequested();
        foreach (var parentTrait in declaration.ParentTraits) {
          RegisterTypeDesignator(_currentScope, parentTrait);
        }
        ProcessNestedScope(declaration, declaration.tok, visit);
      }

      public override void Visit(Method method) {
        _cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(method, method.tok, () => base.Visit(method));
      }

      public override void Visit(Function function) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterTypeDesignator(_currentScope, function.ResultType);
        ProcessNestedScope(function, function.tok, () => base.Visit(function));
      }

      public override void Visit(Field field) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterTypeDesignator(_currentScope, field.Type);
        base.Visit(field);
      }

      public override void Visit(Formal formal) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterTypeDesignator(_currentScope, formal.Type);
        base.Visit(formal);
      }

      public override void Visit(BlockStmt blockStatement) {
        _cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(blockStatement, blockStatement.Tok, () => base.Visit(blockStatement));
      }

      public override void Visit(ExprDotName expressionDotName) {
        _cancellationToken.ThrowIfCancellationRequested();
        base.Visit(expressionDotName);
        if (_typeResolver.TryGetTypeSymbol(expressionDotName.Lhs, out var leftHandSideType)) {
          RegisterDesignator(leftHandSideType, expressionDotName, expressionDotName.tok, expressionDotName.SuffixName);
        }
      }

      public override void Visit(NameSegment nameSegment) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(_currentScope, nameSegment, nameSegment.tok, nameSegment.Name);
      }

      public override void Visit(TypeRhs typeRhs) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterTypeDesignator(_currentScope, typeRhs.EType);
        base.Visit(typeRhs);
      }

      public override void Visit(FrameExpression frameExpression) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(_currentScope, frameExpression, frameExpression.tok, frameExpression.FieldName);
      }

      public override void Visit(LocalVariable localVariable) {
        _cancellationToken.ThrowIfCancellationRequested();
        // TODO The type of a local variable may be visited twice when its initialized at declaration.
        //      It is visited first for the declaration itself and then for the update (initialization).
        // RegisterTypeDesignator(_currentScope, localVariable.Type);
        base.Visit(localVariable);
      }

      private void RegisterTypeDesignator(ISymbol scope, Type type) {
        // TODO We currently rely on the resolver to locate "NamePath" (i.e. the type designator).
        //      The "typeRhs" only points to the "new" keyword with its token.
        //      Find an alternative to get the type designator without requiring the resolver.
        if (type is UserDefinedType userDefinedType) {
          RegisterDesignator(scope, type, userDefinedType.NamePath.tok, userDefinedType.Name);
        }
      }

      private void RegisterDesignator(ISymbol scope, AstElement node, Boogie.IToken token, string identifier) {
        var symbol = GetSymbolDeclarationByName(scope, identifier);
        if (symbol != null) {
          // Many resolutions for automatically generated nodes (e.g. Decreases, Update when initializating a variable
          // at declaration) cause duplicated visits. These cannot be prevented at this time as it seems there's no way
          // to distinguish nodes from automatically created one (i.e. nodes of the original syntax tree vs. nodes of the
          // abstract syntax tree). We could just ignore such duplicates. However, we may miss programatic errors if we
          // do so.
          var range = token.GetLspRange();
          SymbolLookup.Add(range.Start, range.End, symbol);
          _designators.Add(node, symbol);
        } else {
          _logger.LogInformation("could not resolve the symbol of designator named {Identifier} in {Filename}@({Line},{Column})",
            identifier, token.GetDocumentFileName(), token.line, token.col);
        }
      }

      private void ProcessNestedScope(AstElement node, Boogie.IToken token, System.Action visit) {
        if (!_program.IsPartOfEntryDocument(token)) {
          return;
        }
        var oldScope = _currentScope;
        _currentScope = _declarations[node];
        visit();
        _currentScope = oldScope;
      }

      private ILocalizableSymbol? GetSymbolDeclarationByName(ISymbol scope, string name) {
        var currentScope = scope;
        while (currentScope != null) {
          foreach (var child in currentScope.Children.OfType<ILocalizableSymbol>()) {
            _cancellationToken.ThrowIfCancellationRequested();
            if (child.Name == name) {
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
        return VisitTypeSymbol(classSymbol);
      }

      public Unit Visit(DataTypeSymbol datatypeSymbol) {
        return VisitTypeSymbol(datatypeSymbol);
      }

      private Unit VisitTypeSymbol<TNode>(TypeWithMembersSymbolBase<TNode> typeSymbol) where TNode : TopLevelDeclWithMembers {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          typeSymbol,
          typeSymbol.Declaration.tok,
          typeSymbol.Declaration.tok.GetLspRange(),
          new Range(typeSymbol.Declaration.tok.GetLspPosition(), typeSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(typeSymbol);
        return Unit.Value;
      }

      public Unit Visit(ValueTypeSymbol valueTypeSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          valueTypeSymbol,
          valueTypeSymbol.Declaration.tok,
          valueTypeSymbol.Declaration.tok.GetLspRange(),
          new Range(valueTypeSymbol.Declaration.tok.GetLspPosition(), valueTypeSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(valueTypeSymbol);
        return Unit.Value;
      }

      public Unit Visit(FieldSymbol fieldSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          fieldSymbol,
          fieldSymbol.Declaration.tok,
          fieldSymbol.Declaration.tok.GetLspRange(),
          fieldSymbol.Declaration.tok.GetLspRange()
        // TODO BodyEndToken returns a token with location (0, 0)
        //new Range(fieldSymbol.Declaration.tok.GetLspPosition(), fieldSymbol.Declaration.BodyEndTok.GetLspPosition())
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

      public Unit Visit(ScopeSymbol scopeSymbol) {
        _cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          scopeSymbol,
          scopeSymbol.Declaration.Tok,
          scopeSymbol.Declaration.Tok.GetLspRange(),
          new Range(scopeSymbol.Declaration.Tok.GetLspPosition(), scopeSymbol.Declaration.EndTok.GetLspPosition())
        );
        VisitChildren(scopeSymbol);
        return Unit.Value;
      }

      private void VisitChildren(ISymbol symbol) {
        foreach (var child in symbol.Children) {
          child.Accept(this);
        }
      }

      private void RegisterLocation(ISymbol symbol, Boogie.IToken token, Range name, Range declaration) {
        if (token.filename != null) {
          // The filename is null if we have a default or System based symbol. This is also reflected by the ranges being usually -1.
          Locations.Add(symbol, new SymbolLocation(token.GetDocumentUri(), name, declaration));
        }
      }
    }
  }
}
