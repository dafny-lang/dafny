using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols;

internal class SymbolDeclarationResolver {
  private readonly ILogger logger;
  private readonly CancellationToken cancellationToken;

  public SymbolDeclarationResolver(ILogger logger, CancellationToken cancellationToken) {
    this.logger = logger;
    this.cancellationToken = cancellationToken;
  }

  public CompilationUnit ProcessProgram(Uri entryDocument, Dafny.Program program) {
    var compilationUnit = new CompilationUnit(entryDocument, program);
    // program.CompileModules would probably more suitable here, since we want the symbols of the System module as well.
    // However, it appears that the AST of program.CompileModules does not hold the correct location of the nodes - at least of the declarations.
    foreach (var module in compilationUnit.Program.Modules()) {
      cancellationToken.ThrowIfCancellationRequested();
      compilationUnit.Modules.Add(ProcessModule(compilationUnit, module));
    }
    compilationUnit.Modules.Add(ProcessModule(compilationUnit, compilationUnit.Program.SystemModuleManager.SystemModule));
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
      case ClassLikeDecl classDeclaration:
        return ProcessClass(moduleSymbol, classDeclaration);
      case DefaultClassDecl defaultClassDecl:
        return ProcessClass(moduleSymbol, defaultClassDecl);
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

  private ClassSymbol ProcessClass(Symbol scope, TopLevelDeclWithMembers classDeclaration) {
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
      case MethodOrConstructor method:
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
    foreach (var parameter in function.Ins) {
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
    functionSymbol.Reads.AddRange(ProcessListFramedExpressions(function.Reads.Expressions!, ExpressionHandler));
    functionSymbol.Decreases.AddRange(ProcessListExpressions(function.Decreases.Expressions!, ExpressionHandler));
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

  private MethodSymbol ProcessMethod(Symbol scope, MethodOrConstructor method) {
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
    methodSymbol.Reads.AddRange(ProcessListExpressions(
      method.Reads.Expressions!.Select(frameExpression => frameExpression.E), ExpressionHandler));
    methodSymbol.Modifies.AddRange(ProcessListExpressions(
      method.Mod.Expressions!.Select(frameExpression => frameExpression.E), ExpressionHandler));
    methodSymbol.Decreases.AddRange(ProcessListExpressions(method.Decreases.Expressions!, ExpressionHandler));

    return methodSymbol;
  }

  private ScopeSymbol ProcessBlockStmt(ScopeSymbol rootBlock, BlockLikeStmt blockStatement) {
    var localVisitor = new LocalVariableDeclarationVisitor(logger, rootBlock);
    localVisitor.Resolve(blockStatement);
    return rootBlock;
  }

  private ScopeSymbol ProcessFunctionByMethodBody(
    FunctionSymbol functionSymbol, BlockStmt blockStatement
  ) {
    return ProcessBlockStmt(new ScopeSymbol(functionSymbol, blockStatement), blockStatement);
  }

  private ScopeSymbol ProcessMethodBody(MethodSymbol methodSymbol, BlockLikeStmt blockStatement) {
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