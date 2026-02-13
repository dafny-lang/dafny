using System;
using IntervalTree;
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace;
using AstElement = System.Object;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class SymbolTableFactory : ISymbolTableFactory {
    private readonly ILogger logger;

    public SymbolTableFactory(ILogger logger) {
      this.logger = logger;
    }


    public LegacySignatureAndCompletionTable CreateFrom(CompilationInput input,
      ResolutionResult resolutionResult,
      CancellationToken cancellationToken) {

      var compilationUnit = resolutionResult.HasErrors
        ? new CompilationUnit(input.Project.Uri, resolutionResult.ResolvedProgram)
        : new SymbolDeclarationResolver(logger, cancellationToken).ProcessProgram(input.Project.Uri, resolutionResult.ResolvedProgram);

      var program = resolutionResult.ResolvedProgram;
      var declarations = CreateDeclarationDictionary(compilationUnit, cancellationToken);
      var designatorVisitor = new DesignatorVisitor(logger, compilationUnit, declarations, compilationUnit, cancellationToken);
      var declarationLocationVisitor = new SymbolDeclarationLocationVisitor(cancellationToken);
      var symbolsResolved = !resolutionResult.HasErrors;
      if (symbolsResolved) {
        designatorVisitor.Visit(program);
        declarationLocationVisitor.Visit(compilationUnit);
      } else {
        // TODO This is an unfortunate situation. The syntax could be correct but contain some semantic errors.
        //      However, due to the contracts of the resolver we cannot pro-actively check if certain information could be resolved or not.
        //      Therefore, we only have "all or nothing" when re-using the semantic model. Check if there is really no possibility to
        //      check if information was set without actually retrieving it (i.e., it's not possible to access the Type attribute due to a contract
        //      prohibiting it to be null).
        logger.LogDebug("cannot create symbol table from a program with errors");
      }
      return new LegacySignatureAndCompletionTable(
        logger,
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
          // TODO we're using try-add since it appears that nodes of the System module are re-used across several builtins.
          // TODO Maybe refine the mapping of the "declarations".
          declarations.TryAdd(localizableSymbol.Node, localizableSymbol);
        }
      }
      return declarations;
    }

    private class DesignatorVisitor : SyntaxTreeVisitor {
      private readonly ILogger logger;
      private readonly IDictionary<AstElement, ILocalizableSymbol> declarations;
      private readonly DafnyLangTypeResolver typeResolver;
      private readonly IDictionary<AstElement, ILegacySymbol> designators = new Dictionary<AstElement, ILegacySymbol>();
      private readonly CancellationToken cancellationToken;
      private readonly CompilationUnit compilationUnit;

      private ILegacySymbol currentScope;

      public ImmutableDictionary<Uri, IIntervalTree<Position, ILocalizableSymbol>> SymbolLookup { get; private set; }
        = ImmutableDictionary<Uri, IIntervalTree<Position, ILocalizableSymbol>>.Empty;

      public DesignatorVisitor(
        ILogger logger, CompilationUnit compilationUnit, IDictionary<AstElement, ILocalizableSymbol> declarations, ILegacySymbol rootScope, CancellationToken cancellationToken) {
        this.logger = logger;
        this.compilationUnit = compilationUnit;
        this.declarations = declarations;
        typeResolver = new DafnyLangTypeResolver(declarations);
        currentScope = rootScope;
        this.cancellationToken = cancellationToken;
      }

      public override void VisitUnknown(object node, IOrigin token) {
        logger.LogDebug("encountered unknown syntax node of type {NodeType} in {Filename}@({Line},{Column})",
          node.GetType(), token.GetDocumentFileName(), token.line, token.col);
      }

      public override void Visit(ModuleDefinition moduleDefinition) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(moduleDefinition, moduleDefinition.Origin, () => base.Visit(moduleDefinition));
      }

      public override void Visit(TopLevelDeclWithMembers classDeclaration) {
        VisitTopLevelDeclarationWithMembers(classDeclaration, () => base.Visit(classDeclaration));
      }

      public override void Visit(DatatypeDecl datatypeDeclaration) {
        VisitTopLevelDeclarationWithMembers(datatypeDeclaration, () => base.Visit(datatypeDeclaration));
      }

      private void VisitTopLevelDeclarationWithMembers(TopLevelDeclWithMembers declaration, System.Action visit) {
        cancellationToken.ThrowIfCancellationRequested();
        foreach (var parentTrait in declaration.Traits) {
          RegisterTypeDesignator(currentScope, parentTrait);
        }
        ProcessNestedScope(declaration, declaration.Origin, visit);
      }

      public override void Visit(MethodOrConstructor method) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(method, method.Origin, () => base.Visit(method));
      }

      public override void Visit(Function function) {
        cancellationToken.ThrowIfCancellationRequested();
        if (function.Result == null) {
          RegisterTypeDesignator(currentScope, function.ResultType);
        }
        ProcessNestedScope(function, function.Origin, () => base.Visit(function));
      }

      public override void Visit(LambdaExpr lambdaExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(lambdaExpression, lambdaExpression.Origin, () => base.Visit(lambdaExpression));
      }
      public override void Visit(ForallExpr forallExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(forallExpression, forallExpression.Origin, () => base.Visit(forallExpression));
      }
      public override void Visit(ExistsExpr existsExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(existsExpression, existsExpression.Origin, () => base.Visit(existsExpression));
      }
      public override void Visit(SetComprehension setComprehension) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(setComprehension, setComprehension.Origin, () => base.Visit(setComprehension));
      }
      public override void Visit(MapComprehension mapComprehension) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(mapComprehension, mapComprehension.Origin, () => base.Visit(mapComprehension));
      }

      public override void Visit(LetExpr letExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(letExpression, letExpression.Origin, () => base.Visit(letExpression));
      }

      public override void Visit(Field field) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterTypeDesignator(currentScope, field.Type);
        base.Visit(field);
      }

      public override void Visit(Formal formal) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, formal, formal.Origin, formal.Name);
        RegisterTypeDesignator(currentScope, formal.Type);
        base.Visit(formal);
      }

      public override void Visit(NonglobalVariable variable) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, variable, variable.Origin, variable.Name);
        RegisterTypeDesignator(currentScope, variable.Type);
        base.Visit(variable);
      }

      public override void Visit(BlockLikeStmt blockStatement) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(blockStatement, blockStatement.Origin, () => base.Visit(blockStatement));
      }

      public override void Visit(ExprDotName expressionDotName) {
        cancellationToken.ThrowIfCancellationRequested();
        base.Visit(expressionDotName);
        if (typeResolver.TryGetTypeSymbol(expressionDotName.Lhs, out var leftHandSideType)) {
          RegisterDesignator(leftHandSideType, expressionDotName, expressionDotName.Center, expressionDotName.SuffixName);
        }
      }

      public override void Visit(NameSegment nameSegment) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, nameSegment, nameSegment.Origin, nameSegment.Name);
      }

      public override void Visit(TypeRhs typeRhs) {
        cancellationToken.ThrowIfCancellationRequested();
        if (typeRhs is AllocateArray allocateArray && allocateArray.ExplicitType != null) {
          RegisterTypeDesignator(currentScope, allocateArray.ExplicitType);
        }
        if (typeRhs is AllocateClass allocateClass) {
          RegisterTypeDesignator(currentScope, allocateClass.Type);
        }
        base.Visit(typeRhs);
      }

      public override void Visit(FrameExpression frameExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        if (frameExpression.FieldName != null) {
          RegisterDesignator(currentScope, frameExpression, frameExpression.Origin, frameExpression.FieldName);
        }
      }

      public override void Visit(IdentifierExpr identifierExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, identifierExpression, identifierExpression.Origin, identifierExpression.Name);
        base.Visit(identifierExpression);
      }

      public override void Visit(LocalVariable localVariable) {
        cancellationToken.ThrowIfCancellationRequested();
        // TODO The type of a local variable may be visited twice when its initialized at declaration.
        //      It is visited first for the declaration itself and then for the update (initialization).
        // RegisterTypeDesignator(_currentScope, localVariable.Type);
        base.Visit(localVariable);
      }

      private void RegisterTypeDesignator(ILegacySymbol scope, Type type) {
        // TODO We currently rely on the resolver to locate "NamePath" (i.e. the type designator).
        //      The "typeRhs" only points to the "new" keyword with its token.
        //      Find an alternative to get the type designator without requiring the resolver.
        if (type is UserDefinedType userDefinedType) {
          RegisterDesignator(scope, type, userDefinedType.NamePath.Origin, userDefinedType.Name);
        }
      }

      private void RegisterDesignator(ILegacySymbol scope, AstElement node, Boogie.IToken token, string identifier) {
        var symbol = GetSymbolDeclarationByName(scope, identifier);
        if (symbol != null) {
          if (ReferenceEquals(token, Token.NoToken)) {
            return;
          }
          // Many resolutions for automatically generated nodes (e.g. Decreases, Update when initializating a variable
          // at declaration) cause duplicated visits. These cannot be prevented at this time as it seems there's no way
          // to distinguish nodes from automatically created one (i.e. nodes of the original syntax tree vs. nodes of the
          // abstract syntax tree). We just ignore such duplicates until more information is availabe in the AST.
          var range = token.GetLspRange();

          var dafnyToken = (IOrigin)token;
          var symbolLookupForUri =
            SymbolLookup.GetValueOrDefault(dafnyToken.Uri) ?? new IntervalTree<Position, ILocalizableSymbol>();
          SymbolLookup = SymbolLookup.SetItem(dafnyToken.Uri, symbolLookupForUri);

          symbolLookupForUri.Add(range.Start, range.End, symbol);
          if (designators.TryGetValue(node, out var registeredSymbol)) {
            if (registeredSymbol != symbol) {
              logger.LogDebug("Conflicting symbol resolution of designator named {Identifier} in {Filename}@({Line},{Column})",
                identifier, token.GetDocumentFileName(), token.line, token.col);
            }
          } else {
            designators.Add(node, symbol);
          }
        } else {
          logger.LogDebug("could not resolve the symbol of designator named {Identifier} in {Filename}@({Line},{Column})",
            identifier, token.GetDocumentFileName(), token.line, token.col);
        }
      }

      private void ProcessNestedScope(AstElement node, Boogie.IToken token, System.Action visit) {
        if (!this.compilationUnit.IsPartOfEntryDocument(token)) {
          return;
        }
        var oldScope = currentScope;
        currentScope = declarations[node];
        visit();
        currentScope = oldScope;
      }

      private ILocalizableSymbol? GetSymbolDeclarationByName(ILegacySymbol scope, string name) {
        var currentScope = scope;
        while (currentScope != null) {
          foreach (var child in currentScope.Children.OfType<ILocalizableSymbol>()) {
            cancellationToken.ThrowIfCancellationRequested();
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
      private readonly CancellationToken cancellationToken;

      public ImmutableDictionary<Uri, IDictionary<ILegacySymbol, SymbolLocation>> Locations { get; private set; }
        = ImmutableDictionary<Uri, IDictionary<ILegacySymbol, SymbolLocation>>.Empty;

      public SymbolDeclarationLocationVisitor(CancellationToken cancellationToken) {
        this.cancellationToken = cancellationToken;
      }

      public Unit Visit(ILegacySymbol symbol) {
        symbol.Accept(this);
        return Unit.Value;
      }

      public Unit Visit(CompilationUnit compilationUnit) {
        VisitChildren(compilationUnit);
        return Unit.Value;
      }

      public Unit Visit(ModuleSymbol moduleSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          moduleSymbol,
          moduleSymbol.Declaration.Origin,
          moduleSymbol.Declaration.NavigationToken.GetLspRange(),
          moduleSymbol.Declaration.EntireRange.ToLspRange()
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
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          typeSymbol,
          typeSymbol.Declaration.Origin,
          typeSymbol.Declaration.NavigationRange.ToLspRange(),
          new Range(typeSymbol.Declaration.StartToken.GetLspPosition(), typeSymbol.Declaration.EndToken.GetLspPosition())
        );
        VisitChildren(typeSymbol);
        return Unit.Value;
      }

      public Unit Visit(ValueTypeSymbol valueTypeSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          valueTypeSymbol,
          valueTypeSymbol.Declaration.Origin,
          valueTypeSymbol.Declaration.NavigationRange.ToLspRange(),
          new Range(valueTypeSymbol.Declaration.StartToken.GetLspPosition(), valueTypeSymbol.Declaration.EndToken.GetLspPosition())
        );
        VisitChildren(valueTypeSymbol);
        return Unit.Value;
      }

      public Unit Visit(FieldSymbol fieldSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          fieldSymbol,
          fieldSymbol.Declaration.Origin,
          fieldSymbol.Declaration.NavigationRange.ToLspRange(),
          // BodyEndToken always returns Token.NoToken
          fieldSymbol.Declaration.EntireRange.ToLspRange()
        );
        VisitChildren(fieldSymbol);
        return Unit.Value;
      }

      public Unit Visit(FunctionSymbol functionSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          functionSymbol,
          functionSymbol.Declaration.Origin,
          functionSymbol.Declaration.NavigationRange.ToLspRange(),
          GetDeclarationRange(functionSymbol.Declaration)
        );
        VisitChildren(functionSymbol);
        return Unit.Value;
      }

      public Unit Visit(MethodSymbol methodSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          methodSymbol,
          methodSymbol.Declaration.Origin,
          methodSymbol.Declaration.NavigationRange.ToLspRange(),
          GetDeclarationRange(methodSymbol.Declaration)
        );
        VisitChildren(methodSymbol);
        return Unit.Value;
      }

      private static Range GetDeclarationRange(Declaration declaration) {
        return declaration.EntireRange.ToLspRange();
      }

      public Unit Visit(VariableSymbol variableSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          variableSymbol,
          variableSymbol.Declaration.Origin,
          variableSymbol.Declaration.NavigationRange.ToLspRange(),
          variableSymbol.Declaration.Origin.GetLspRange()
        );
        VisitChildren(variableSymbol);
        return Unit.Value;
      }

      public Unit Visit(ScopeSymbol scopeSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        var endToken = scopeSymbol.BodyEndToken;
        RegisterLocation(
          scopeSymbol,
          scopeSymbol.BodyStartToken,
          scopeSymbol.BodyStartToken.GetLspRange(),
          new Range(scopeSymbol.BodyStartToken.GetLspPosition(), endToken.GetLspPosition())
        );
        VisitChildren(scopeSymbol);
        return Unit.Value;
      }

      private void VisitChildren(ILegacySymbol symbol) {
        foreach (var child in symbol.Children) {
          child.Accept(this);
        }
      }

      private void RegisterLocation(ILegacySymbol symbol, IOrigin token, Range name, Range declaration) {
        if (token.Filepath != null) {
          // The filename is null if we have a default or System based symbol. This is also reflected by the ranges being usually -1.
          var locationsForUri =
            Locations.GetValueOrDefault(token.Uri) ?? new Dictionary<ILegacySymbol, SymbolLocation>();
          Locations = Locations.SetItem(token.Uri, locationsForUri);
          locationsForUri.Add(symbol, new SymbolLocation(token.Uri, name, declaration));
        }
      }
    }
  }
}