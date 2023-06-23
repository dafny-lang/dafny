using System;
using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language.SemanticTokens;

/// <summary>
/// Visitor responsible for populating a table of document tokens.
/// </summary>
public class LspSemanticTokensGeneratingVisitor : SyntaxTreeVisitor {
  private readonly DafnySemanticTokensBuilder builder;

  public LspSemanticTokensGeneratingVisitor(DafnySemanticTokensBuilder builder) {
    this.builder = builder;
  }

  public override void VisitUnknown(object node, IToken token) {
    builder.Log("Unkown node to visit, please extract semantic tokens", node);
  }

  public override void Visit(ModuleDefinition moduleDefinition) {
    moduleDefinition.PrefixIds.ForEach(t => builder.Push("moduleDefinition.PrefixIds", t, SemanticTokenType.Namespace));
    builder.Push("moduleDefinition", moduleDefinition.tok, SemanticTokenType.Namespace);
    base.Visit(moduleDefinition);
  }

  public override void Visit(TopLevelDeclWithMembers classDeclaration) {
    builder.Push("classDeclaration", classDeclaration.tok, SemanticTokenType.Class, SemanticTokenModifier.Declaration);
    base.Visit(classDeclaration);
  }

  public override void Visit(DatatypeDecl dataTypeDeclaration) {
    builder.Push("dataTypeDeclaration", dataTypeDeclaration.tok, SemanticTokenType.Type, SemanticTokenModifier.Declaration);
    base.Visit(dataTypeDeclaration);
  }

  // TODO FieldDecl, ConstantFieldDecl for var kwd

  // FIXME the below are not declarations, they're references?  At least for Variable probably
  public override void Visit(Field field) {
    builder.Push("field", field.tok, SemanticTokenType.Property, SemanticTokenModifier.Declaration); //Property?
    base.Visit(field);
  }

  public override void Visit(Method method) {
    builder.Push("method", method.tok, SemanticTokenType.Method, SemanticTokenModifier.Declaration);
    base.Visit(method);
  }

  public override void Visit(Constructor constructor) {
    builder.Push("constructor", constructor.tok, SemanticTokenType.Function, SemanticTokenModifier.Definition);
    base.Visit(constructor);
  }

  public override void Visit(Function function) {
    builder.Push("function", function.tok, SemanticTokenType.Function, SemanticTokenModifier.Definition);
    base.Visit(function);
  }

  public override void Visit(NonglobalVariable nonGlobalVariable) { // Formals and bound vars
    builder.Push("nonGlobalVariable", nonGlobalVariable.tok, SemanticTokenType.Variable);
    base.Visit(nonGlobalVariable);
  }

  public override void Visit(Formal formal) {
    builder.Push("formal", formal.tok, SemanticTokenType.Parameter, SemanticTokenModifier.Declaration, SemanticTokenModifier.Readonly);
    base.Visit(formal);
  }

  public override void Visit(LocalVariable localVariable) {
    builder.Push("localVariable", localVariable.Tok, SemanticTokenType.Variable);
    base.Visit(localVariable);
  }

  public override void Visit(ForallStmt forAllStatement) {
    builder.Push("forAllStatement", forAllStatement.Tok, SemanticTokenType.Keyword); // Override the expression
    base.Visit(forAllStatement);
  }

  public override void Visit(AutoGhostIdentifierExpr autoGhostIdentifierExpression) {
    builder.Push("autoGhostIdentifierExpression", autoGhostIdentifierExpression.tok, SemanticTokenType.Variable, SemanticTokenModifier.Declaration); //TODO ghost
    // base.Visit(autoGhostIdentifierExpression); // No rec. into variable
  }

  public override void Visit(LiteralExpr literalExpression) {
    // base.Visit(literalExpression); // No rec. into literal
  }

  public override void Visit(IdentifierExpr identifierExpression) {
    builder.Push("identifierExpression", identifierExpression.tok, SemanticTokenType.Variable, SemanticTokenModifier.Declaration);
    // base.Visit(identifierExpression); // No rec. into variable
  }

  public override void Visit(AliasModuleDecl aliasModuleDecl) {
    builder.Push("aliasModuleDecl", aliasModuleDecl.tok, SemanticTokenType.Namespace);
    base.Visit(aliasModuleDecl);
  }

  public override void Visit(TypeParameter typeParameter) {
    builder.Push("typeParameter", typeParameter.tok, SemanticTokenType.TypeParameter);
    base.Visit(typeParameter);
  }
}
