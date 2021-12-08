using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using Microsoft.Boogie;

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

    public CompilationUnit ResolveSymbols(TextDocumentItem textDocument, Dafny.Program program, CancellationToken cancellationToken) {
      // TODO The resolution requires mutual exclusion since it sets static variables of classes like Microsoft.Dafny.Type.
      //      Although, the variables are marked "ThreadStatic" - thus it might not be necessary. But there might be
      //      other classes as well.
      resolverMutex.Wait(cancellationToken);
      try {
        if (!RunDafnyResolver(textDocument, program)) {
          // We cannot proceeed without a successful resolution. Due to the contracts in dafny-lang, we cannot
          // access a property without potential contract violations. For example, a variable may have an
          // unresolved type represented by null. However, the contract prohibits the use of the type property
          // because it must not be null.
          return new CompilationUnit(program);
        }
      }
      finally {
        resolverMutex.Release();
      }
      return new SymbolDeclarationResolver(logger, cancellationToken).ProcessProgram(program);
    }

    private bool RunDafnyResolver(TextDocumentItem document, Dafny.Program program) {
      var resolver = new Resolver(program);
      resolver.ResolveProgram(program);
      int resolverErrors = program.reporter.ErrorCount;
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
            logger.LogDebug("encountered unknown top level declaration {Name} of type {Type}", topLevelDeclaration.Name, topLevelDeclaration.GetType());
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

        Func<Expression, ScopeSymbol?> subP = (Expression e) => ProcessFunctionExpr(functionSymbol, e);
        functionSymbol.Body = ProcessFunctionExpr(functionSymbol, function.Body);
        functionSymbol.Ens = ProcessListAttributedExpressions(function.Ens, subP);
        functionSymbol.Req = ProcessListAttributedExpressions(function.Req, subP);
        functionSymbol.Reads = ProcessListFramedExpressions(function.Reads, subP);
        functionSymbol.Decreases = ProcessListExpressions(function.Decreases.Expressions, subP);
        functionSymbol.ByMethodBody = ProcessFunctionByMethodBody(functionSymbol, function.ByMethodBody);
        return functionSymbol;
      }

      private List<ScopeSymbol> ProcessListAttributedExpressions(
        IList<AttributedExpression> list, Func<Expression, ScopeSymbol?> subProcess) {
        return list.SelectMany(atExpr => Symbol.AsEnumerable<ScopeSymbol>(
          subProcess(atExpr.E))).ToList();
      }

      private List<ScopeSymbol> ProcessListFramedExpressions(
        IList<FrameExpression> list, Func<Expression, ScopeSymbol?> subProcess) {
        return list.SelectMany(frameExpr => Symbol.AsEnumerable<ScopeSymbol>(
          subProcess(frameExpr.E))).ToList();
      }

      private List<ScopeSymbol> ProcessListExpressions<T>(
        List<T> list, Func<T, ScopeSymbol?> subProcess) where T : class {
        return list.SelectMany(expr => Symbol.AsEnumerable<ScopeSymbol>(
          subProcess(expr))).ToList();
      }


      private ScopeSymbol? ProcessFunctionExpr(FunctionSymbol functionSymbol, Expression? expression) {
        if (expression == null) {
          return null;
        }
        // The outer function symbol takes ownership of the function already.
        var rootBlock = new ScopeSymbol(functionSymbol, functionSymbol.Declaration);
        var localVisitor = new LocalVariableDeclarationVisitor(logger, rootBlock);
        localVisitor.Resolve(expression);
        return rootBlock;
      }

      private ScopeSymbol? ProcessFunctionByMethodBody(FunctionSymbol functionSymbol, BlockStmt? blockStatement) {
        if (blockStatement == null) {
          return null;
        }
        var rootBlock = new ScopeSymbol(functionSymbol, blockStatement);
        var localVisitor = new LocalVariableDeclarationVisitor(logger, rootBlock);
        localVisitor.Resolve(blockStatement);
        return rootBlock;
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
        methodSymbol.Block = ProcessMethodBody(methodSymbol, method.Body);
        Func<Expression, ScopeSymbol?> subP = e => ProcessMethodExpr(methodSymbol, e);
        methodSymbol.Ens = ProcessListAttributedExpressions(method.Ens, subP);
        methodSymbol.Req = ProcessListAttributedExpressions(method.Req, subP);
        methodSymbol.Mod = ProcessListExpressions(method.Mod.Expressions.Select(e => e.E).ToList(), subP);
        methodSymbol.Decreases = ProcessListExpressions(method.Decreases.Expressions, subP);

        return methodSymbol;
      }

      private ScopeSymbol? ProcessMethodBody(MethodSymbol methodSymbol, BlockStmt? blockStatement) {
        if (blockStatement == null) {
          return null;
        }
        var rootBlock = new ScopeSymbol(methodSymbol, blockStatement);
        var localVisitor = new LocalVariableDeclarationVisitor(logger, rootBlock);
        localVisitor.Resolve(blockStatement);
        return rootBlock;
      }

      private ScopeSymbol? ProcessMethodExpr(MethodSymbol methodSymbol, Expression? expression) {
        if (expression == null) {
          return null;
        }
        // The outer function symbol takes ownership of the function already.
        var rootBlock = new ScopeSymbol(methodSymbol, methodSymbol.Declaration);
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

      public override void VisitUnknown(object node, Boogie.IToken token) {
        logger.LogDebug("encountered unknown syntax node of type {NodeType} in {Filename}@({Line},{Column})",
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

      public override void Visit(ComprehensionExpr compExpr) {
        var oldBlock = block;
        if (block.Node != compExpr) { // Else we reuse the current scopoe
          block = new ComprehensionSymbol(block, compExpr);
          oldBlock.Symbols.Add(block);
        }
        foreach (var parameter in compExpr.BoundVars) {
          block.Symbols.Add(ProcessBoundVar(block, parameter));
        }
        base.Visit(compExpr);
        block = oldBlock;
      }

      public override void Visit(LetExpr letExpr) {
        var oldBlock = block;
        // If this is the top-level expression, we have to replace the original scope
        if (block.Node != letExpr) { // Else we reuse the current scopoe
          block = new ScopeSymbol(block, letExpr);
          oldBlock.Symbols.Add(block);
        }
        foreach (var parameter in letExpr.BoundVars) {
          block.Symbols.Add(ProcessBoundVar(block, parameter));
        }
        base.Visit(letExpr);
        block = oldBlock;
      }

      private static VariableSymbol ProcessBoundVar(Symbol scope, BoundVar formal) {
        return new VariableSymbol(scope, formal);
      }
    }
  }
}
