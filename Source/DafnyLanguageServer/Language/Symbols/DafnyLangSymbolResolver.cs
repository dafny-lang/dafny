using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Symbol resolver that utilizes dafny-lang to resolve the symbols.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this resolver serializes all invocations.
  /// </remarks>
  public class DafnyLangSymbolResolver : ISymbolResolver {
    private readonly ILogger logger;
    private readonly SemaphoreSlim resolverMutex = new(1);

    public DafnyLangSymbolResolver(ILogger<DafnyLangSymbolResolver> logger) {
      this.logger = logger;
    }

    public CompilationUnit ResolveSymbols(TextDocumentItem textDocument, Dafny.Program program, out bool canDoVerification, CancellationToken cancellationToken) {
      // TODO The resolution requires mutual exclusion since it sets static variables of classes like Microsoft.Dafny.Type.
      //      Although, the variables are marked "ThreadStatic" - thus it might not be necessary. But there might be
      //      other classes as well.
      resolverMutex.Wait(cancellationToken);
      try {
        if (!RunDafnyResolver(textDocument, program)) {
          // We cannot proceed without a successful resolution. Due to the contracts in dafny-lang, we cannot
          // access a property without potential contract violations. For example, a variable may have an
          // unresolved type represented by null. However, the contract prohibits the use of the type property
          // because it must not be null.
          canDoVerification = false;
          return new CompilationUnit(program);
        }
      }
      finally {
        resolverMutex.Release();
      }
      canDoVerification = true;
      return new SymbolDeclarationResolver(logger, cancellationToken).ProcessProgram(program);
    }

    private bool RunDafnyResolver(TextDocumentItem document, Dafny.Program program) {
      var resolver = new Resolver(program);
      resolver.ResolveProgram(program);
      int resolverErrors = resolver.Reporter.ErrorCountUntilResolver;
      if (resolverErrors > 0) {
        logger.LogDebug("encountered {ErrorCount} errors while resolving {DocumentUri}", resolverErrors, document.Uri);
        return false;
      }
      return true;
    }

    private class SymbolDeclarationResolver {
      private readonly ILogger logger;
      private readonly CancellationToken cancellationToken;

      public SymbolDeclarationResolver(ILogger logger, CancellationToken cancellationToken) {
        this.logger = logger;
        this.cancellationToken = cancellationToken;
      }

      public CompilationUnit ProcessProgram(Dafny.Program program) {
        var compilationUnit = new CompilationUnit(program);
        // program.CompileModules would probably more suitable here, since we want the symbols of the System module as well.
        // However, it appears that the AST of program.CompileModules does not hold the correct location of the nodes - at least of the declarations.
        foreach (var module in program.Modules()) {
          cancellationToken.ThrowIfCancellationRequested();
          compilationUnit.Modules.Add(ProcessModule(compilationUnit, module));
        }
        compilationUnit.Modules.Add(ProcessModule(compilationUnit, program.BuiltIns.SystemModule));
        return compilationUnit;
      }

      private ModuleSymbol ProcessModule(Symbol scope, ModuleDefinition moduleDefinition) {
        var moduleSymbol = new ModuleSymbol(scope, moduleDefinition);
        foreach (var declaration in moduleDefinition.TopLevelDecls) {
          cancellationToken.ThrowIfCancellationRequested();
          var topLevelSymbol = ProcessTopLevelDeclaration(moduleSymbol, declaration);
          if (topLevelSymbol != null) {
            moduleSymbol.Declarations.Add(topLevelSymbol);
          }
        }
        return moduleSymbol;
      }

      private Symbol? ProcessTopLevelDeclaration(ModuleSymbol moduleSymbol, TopLevelDecl topLevelDeclaration) {
        switch (topLevelDeclaration) {
          case ClassDecl classDeclaration:
            return ProcessClass(moduleSymbol, classDeclaration);
          case LiteralModuleDecl literalModuleDeclaration:
            return ProcessModule(moduleSymbol, literalModuleDeclaration.ModuleDef);
          case ValuetypeDecl valueTypeDeclaration:
            return ProcessValueType(moduleSymbol, valueTypeDeclaration);
          case DatatypeDecl dataTypeDeclaration:
            return ProcessDataType(moduleSymbol, dataTypeDeclaration);
          default:
            logger.LogTrace("encountered unknown top level declaration {Name} of type {Type}", topLevelDeclaration.Name, topLevelDeclaration.GetType());
            return null;
        }
      }

      private ClassSymbol ProcessClass(Symbol scope, ClassDecl classDeclaration) {
        var classSymbol = new ClassSymbol(scope, classDeclaration);
        ProcessAndAddAllMembers(classSymbol, classDeclaration);
        return classSymbol;
      }

      private static ValueTypeSymbol ProcessValueType(Symbol scope, ValuetypeDecl valueTypeDecarlation) {
        return new ValueTypeSymbol(scope, valueTypeDecarlation);
      }

      private DataTypeSymbol ProcessDataType(Symbol scope, DatatypeDecl dataTypeDeclaration) {
        var dataTypeSymbol = new DataTypeSymbol(scope, dataTypeDeclaration);
        ProcessAndAddAllMembers(dataTypeSymbol, dataTypeDeclaration);
        return dataTypeSymbol;
      }

      private void ProcessAndAddAllMembers(TypeWithMembersSymbolBase containingType, TopLevelDeclWithMembers declaration) {
        foreach (var member in declaration.Members) {
          cancellationToken.ThrowIfCancellationRequested();
          var memberSymbol = ProcessTypeMember(containingType, member);
          if (memberSymbol != null) {
            // TODO When respecting all possible class members, this should never be null.
            containingType.Members.Add(memberSymbol);
          }
        }
      }

      private Symbol? ProcessTypeMember(Symbol scope, MemberDecl memberDeclaration) {
        cancellationToken.ThrowIfCancellationRequested();
        switch (memberDeclaration) {
          case Function function:
            return ProcessFunction(scope, function);
          case Method method:
            // TODO handle the constructors explicitly? The constructor is a sub-class of Method.
            return ProcessMethod(scope, method);
          case Field field:
            return ProcessField(scope, field);
          default:
            // TODO The last missing member is AmbiguousMemberDecl which is created by the resolver.
            //      When is this class exactly used?
            logger.LogDebug("encountered unknown member declaration {DeclarationType}", memberDeclaration.GetType());
            return null;
        }
      }

      private FunctionSymbol ProcessFunction(Symbol scope, Function function) {
        var functionSymbol = new FunctionSymbol(scope, function);
        foreach (var parameter in function.Formals) {
          cancellationToken.ThrowIfCancellationRequested();
          functionSymbol.Parameters.Add(ProcessFormal(scope, parameter));
        }
        if (function.Result != null) {
          functionSymbol.Parameters.Add(ProcessFormal(scope, function.Result));
        }
        ScopeSymbol? ExpressionHandler(Expression? expression) =>
          expression == null
            ? null
            : ProcessExpression(new ScopeSymbol(functionSymbol, functionSymbol.Declaration), expression);
        functionSymbol.Body = ExpressionHandler(function.Body);
        functionSymbol.Ensures.AddRange(ProcessListAttributedExpressions(function.Ens, ExpressionHandler));
        functionSymbol.Requires.AddRange(ProcessListAttributedExpressions(function.Req, ExpressionHandler));
        functionSymbol.Reads.AddRange(ProcessListFramedExpressions(function.Reads, ExpressionHandler));
        functionSymbol.Decreases.AddRange(ProcessListExpressions(function.Decreases.Expressions, ExpressionHandler));
        functionSymbol.ByMethodBody = function.ByMethodBody == null ? null : ProcessFunctionByMethodBody(functionSymbol, function.ByMethodBody);
        return functionSymbol;
      }

      private IEnumerable<ScopeSymbol> ProcessListAttributedExpressions(
        IEnumerable<AttributedExpression> list, Func<Expression?, ScopeSymbol?> expressionHandler
        ) {
        return list
          .Select(attributedExpression => expressionHandler(attributedExpression.E))
          .Where(x => x != null)
          .Cast<ScopeSymbol>();
      }

      private IEnumerable<ScopeSymbol> ProcessListFramedExpressions(
        IEnumerable<FrameExpression> list, Func<Expression?, ScopeSymbol?> expressionHandler
        ) {
        return list
          .Select(frameExpression => expressionHandler(frameExpression.E))
          .Where(x => x != null)
          .Cast<ScopeSymbol>();
      }

      private IEnumerable<ScopeSymbol> ProcessListExpressions<T>(
        IEnumerable<T> list, Func<T, ScopeSymbol?> expressionHandler
        ) where T : class {
        return list
          .Select(expression => expressionHandler(expression))
          .Where(x => x != null)
          .Cast<ScopeSymbol>();
      }

      private MethodSymbol ProcessMethod(Symbol scope, Method method) {
        var methodSymbol = new MethodSymbol(scope, method);
        foreach (var parameter in method.Ins) {
          cancellationToken.ThrowIfCancellationRequested();
          methodSymbol.Parameters.Add(ProcessFormal(scope, parameter));
        }
        foreach (var result in method.Outs) {
          cancellationToken.ThrowIfCancellationRequested();
          methodSymbol.Returns.Add(ProcessFormal(scope, result));
        }
        methodSymbol.Block = method.Body == null ? null : ProcessMethodBody(methodSymbol, method.Body);
        ScopeSymbol? ExpressionHandler(Expression? expression) =>
          expression == null
            ? null
            : ProcessExpression(new ScopeSymbol(methodSymbol, methodSymbol.Declaration), expression);
        methodSymbol.Ensures.AddRange(ProcessListAttributedExpressions(method.Ens, ExpressionHandler));
        methodSymbol.Requires.AddRange(ProcessListAttributedExpressions(method.Req, ExpressionHandler));
        methodSymbol.Modifies.AddRange(ProcessListExpressions(
          method.Mod.Expressions.Select(frameExpression => frameExpression.E), ExpressionHandler));
        methodSymbol.Decreases.AddRange(ProcessListExpressions(method.Decreases.Expressions, ExpressionHandler));

        return methodSymbol;
      }

      private ScopeSymbol ProcessBlockStmt(ScopeSymbol rootBlock, BlockStmt blockStatement) {
        var localVisitor = new LocalVariableDeclarationVisitor(logger, rootBlock);
        localVisitor.Resolve(blockStatement);
        return rootBlock;
      }

      private ScopeSymbol ProcessFunctionByMethodBody(
        FunctionSymbol functionSymbol, BlockStmt blockStatement
      ) {
        return ProcessBlockStmt(new ScopeSymbol(functionSymbol, blockStatement), blockStatement);
      }

      private ScopeSymbol ProcessMethodBody(MethodSymbol methodSymbol, BlockStmt blockStatement) {
        return ProcessBlockStmt(new ScopeSymbol(methodSymbol, blockStatement), blockStatement);
      }

      private ScopeSymbol ProcessExpression(ScopeSymbol rootBlock, Expression expression) {
        // The outer function symbol takes ownership of the function already.
        var localVisitor = new LocalVariableDeclarationVisitor(logger, rootBlock);
        localVisitor.Resolve(expression);
        return rootBlock;
      }

      private static FieldSymbol ProcessField(Symbol scope, Field field) {
        return new FieldSymbol(scope, field);
      }

      private static VariableSymbol ProcessFormal(Symbol scope, Formal formal) {
        return new VariableSymbol(scope, formal);
      }
    }

    private class LocalVariableDeclarationVisitor : SyntaxTreeVisitor {
      private readonly ILogger logger;

      private ScopeSymbol block;

      public LocalVariableDeclarationVisitor(ILogger logger, ScopeSymbol rootBlock) {
        // TODO support cancellation
        this.logger = logger;
        block = rootBlock;
      }

      public void Resolve(BlockStmt blockStatement) {
        // The base is directly visited to avoid doubly nesting the root block of the method.
        base.Visit(blockStatement);
      }

      public void Resolve(Expression bodyExpression) {
        // The base is directly visited to avoid doubly nesting the root block of the method.
        base.Visit(bodyExpression);
      }

      public override void VisitUnknown(object node, IToken token) {
        logger.LogTrace("encountered unknown syntax node of type {NodeType} in {Filename}@({Line},{Column})",
          node.GetType(), token.GetDocumentFileName(), token.line, token.col);
      }

      public override void Visit(BlockStmt blockStatement) {
        var oldBlock = block;
        block = new ScopeSymbol(block, blockStatement);
        oldBlock.Symbols.Add(block);
        base.Visit(blockStatement);
        block = oldBlock;
      }

      public override void Visit(LocalVariable localVariable) {
        block.Symbols.Add(new VariableSymbol(block, localVariable));
      }

      public override void Visit(LambdaExpr lambdaExpression) {
        ProcessBoundVariableBearingExpression(lambdaExpression, () => base.Visit(lambdaExpression));
      }

      public override void Visit(ForallExpr forallExpression) {
        ProcessBoundVariableBearingExpression(forallExpression, () => base.Visit(forallExpression));
      }

      public override void Visit(ExistsExpr existExpression) {
        ProcessBoundVariableBearingExpression(existExpression, () => base.Visit(existExpression));
      }

      public override void Visit(SetComprehension setComprehension) {
        ProcessBoundVariableBearingExpression(setComprehension, () => base.Visit(setComprehension));
      }

      public override void Visit(MapComprehension mapComprehension) {
        ProcessBoundVariableBearingExpression(mapComprehension, () => base.Visit(mapComprehension));
      }

      public override void Visit(LetExpr letExpression) {
        ProcessBoundVariableBearingExpression(letExpression, () => base.Visit(letExpression));
      }

      private void ProcessBoundVariableBearingExpression<TExpr>(
        TExpr boundVarExpression, System.Action baseVisit
        ) where TExpr : Expression, IBoundVarsBearingExpression {
        var oldBlock = block;
        // To prevent two scope symbols from pointing to the same node,
        // (this crashes `declarations[nodes]` later on)
        // we reuse the existing scope symbol if it happens to be a top-level
        // bounded variable bearing expression that otherwise would create a new scope symbol
        if (block.Node != boundVarExpression) {
          block = new ScopeSymbol(block, boundVarExpression);
          oldBlock.Symbols.Add(block);
        }
        foreach (var parameter in boundVarExpression.AllBoundVars) {
          block.Symbols.Add(ProcessBoundVar(block, parameter));
        }
        baseVisit();
        block = oldBlock;
      }

      private static VariableSymbol ProcessBoundVar(Symbol scope, BoundVar formal) {
        return new VariableSymbol(scope, formal);
      }
    }
  }
}
