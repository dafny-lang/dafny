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
    // FIXME change to logging a warning
  }

  public override void Visit(Dafny.Program program) {
    base.Visit(program);
  }

  public override void Visit(ModuleDefinition moduleDefinition) { // TODO Keyword token
    moduleDefinition.PrefixIds.ForEach(t => builder.Push("moduleDefinition.PrefixIds", t, SemanticTokenType.Namespace));
    builder.Push("moduleDefinition", moduleDefinition.tok, SemanticTokenType.Namespace);
    base.Visit(moduleDefinition);
  }

  public override void Visit(TopLevelDecl topLevelDeclaration) {
    base.Visit(topLevelDeclaration);
  }

  public override void Visit(ClassDecl classDeclaration) {
    builder.Push("classDeclaration", classDeclaration.tok, SemanticTokenType.Class, SemanticTokenModifier.Declaration);
    base.Visit(classDeclaration);
  }

  public override void Visit(DatatypeDecl dataTypeDeclaration) {
    builder.Push("dataTypeDeclaration", dataTypeDeclaration.tok, SemanticTokenType.Type, SemanticTokenModifier.Declaration);
    base.Visit(dataTypeDeclaration);
  }

  public override void Visit(MemberDecl memberDeclaration) {
    //# builder.Push("memberDeclaration", memberDeclaration.KeywordToken, SemanticTokenType.Keyword);
    //# Array.ForEach(memberDeclaration.ModifierTokens, t =>
    //#   builder.Push("memberDeclaration.modifierTokens", t, SemanticTokenType.Modifier));
    // Covered by specialized cases below builder.Push("memberDeclaration", memberDeclaration.tok, SemanticTokenType.Property, SemanticTokenModifier.Declaration); //Property?
    base.Visit(memberDeclaration);
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
    builder.Push("formal", formal.tok, SemanticTokenType.Parameter, SemanticTokenModifier.Declaration,  SemanticTokenModifier.Readonly);
    base.Visit(formal);
  }

  public override void Visit(LocalVariable localVariable) {
    builder.Push("localVariable", localVariable.Tok, SemanticTokenType.Variable);
    base.Visit(localVariable);
  }

  public override void Visit(Attributes attributes) {
    // TODO missing tokens
    base.Visit(attributes); // TODO: Visit attrs?
  }

  public override void Visit(Statement statement) {
    base.Visit(statement);
  }

  public override void Visit(ExprRhs expressionRhs) {
    base.Visit(expressionRhs);
  }

  public override void Visit(AssignmentRhs assignmentRhs) {
    base.Visit(assignmentRhs);
  }

  public override void Visit(TypeRhs typeRhs) { // FIXME highlight type name?
    base.Visit(typeRhs);
  }

  public override void Visit(BlockStmt blockStatement) {
    base.Visit(blockStatement);
  }

  public override void Visit(WhileStmt whileStatement) {
    //# builder.Push("whileStatement", whileStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(whileStatement);
  }

  public override void Visit(ForLoopStmt forStatement) {
    //# builder.Push("forStatement", forStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(forStatement);
  }

  public override void Visit(AlternativeLoopStmt alternativeLoopStatement) {
    //# builder.Push("alternativeLoopStatement", alternativeLoopStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(alternativeLoopStatement);
  }

  public override void Visit(IfStmt ifStatement) {
    //# builder.Push("ifStatement", ifStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(ifStatement);
  }

  public override void Visit(AlternativeStmt alternativeStatement) {
    //# builder.Push("alternativeStatement", alternativeStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(alternativeStatement);
  }

  public override void Visit(GuardedAlternative guardedAlternative) {
    //# builder.Push("guardedAlternative", guardedAlternative.Tok, SemanticTokenType.Keyword);
    base.Visit(guardedAlternative);
  }

  public override void Visit(VarDeclStmt variableDeclarationStatement) {
    //# builder.Push("variableDeclarationStatement", variableDeclarationStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(variableDeclarationStatement);
  }

  public override void Visit(UpdateStmt updateStatement) {
    //# builder.Push("updateStatement", updateStatement.Tok, SemanticTokenType.Operator);
    base.Visit(updateStatement);
  }

  public override void Visit(AssertStmt assertStatement) {
    //# builder.Push("assertStatement", assertStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(assertStatement);
  }

  public override void Visit(ReturnStmt returnStatement) {
    //# builder.Push("returnStatement", returnStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(returnStatement);
  }

  public override void Visit(MatchStmt matchStatement) {
    //# builder.Push("matchStatement", matchStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(matchStatement);
  }

  public override void Visit(MatchCaseStmt matchCaseStatement) {
    //# builder.Push("matchCaseStatement", matchCaseStatement.tok, SemanticTokenType.Keyword);
    base.Visit(matchCaseStatement);
  }

  public override void Visit(NestedMatchStmt nestedMatchStatement) { //?
    //# builder.Push("nestedMatchStatement", nestedMatchStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(nestedMatchStatement);
  }

  public override void Visit(NestedMatchCaseStmt nestedMatchCaseStatement) { //?
    //# builder.Push("nestedMatchCaseStatement", nestedMatchCaseStatement.Tok, SemanticTokenType.Keyword);
    base.Visit(nestedMatchCaseStatement);
  }

  public override void Visit(ForallStmt forAllStatement) {
    builder.Push("forAllStatement", forAllStatement.Tok, SemanticTokenType.Keyword); // Override the expression
    base.Visit(forAllStatement);
  }

  public override void Visit(PrintStmt printStatement) {
    //# builder.Push("printStatement", printStatement.Tok, SemanticTokenType.Function, SemanticTokenModifier.DefaultLibrary);
    base.Visit(printStatement);
  }

  public override void Visit(ActualBindings bindings) {
    base.Visit(bindings);
  }

  public override void Visit(ActualBinding binding) {
    base.Visit(binding);
  }

  public override void Visit(Expression expression) {
    base.Visit(expression);
  }

  public override void Visit(AutoGhostIdentifierExpr autoGhostIdentifierExpression) {
    builder.Push("autoGhostIdentifierExpression", autoGhostIdentifierExpression.tok, SemanticTokenType.Variable, SemanticTokenModifier.Declaration); //TODO ghost
    // base.Visit(autoGhostIdentifierExpression); // No rec. into variable
  }

  public override void Visit(LiteralExpr literalExpression) {
    //# builder.Push("literalExpression", literalExpression.tok, SemanticTokenType.Macro, SemanticTokenModifier.DefaultLibrary); //?Macro
    // base.Visit(literalExpression); // No rec. into literal
  }

  public override void Visit(IdentifierExpr identifierExpression) {
    builder.Push("identifierExpression", identifierExpression.tok, SemanticTokenType.Variable, SemanticTokenModifier.Declaration);
    // base.Visit(identifierExpression); // No rec. into variable
  }

  public override void Visit(ApplySuffix applySuffix) {
    base.Visit(applySuffix);
  }

  public override void Visit(NameSegment nameSegment) {
    base.Visit(nameSegment);
  }

  public override void Visit(AliasModuleDecl aliasModuleDecl) {
    builder.Push("aliasModuleDecl", aliasModuleDecl.tok, SemanticTokenType.Namespace);
    base.Visit(aliasModuleDecl);
  }

  public override void Visit(ExprDotName expressionDotName) {
    base.Visit(expressionDotName);
  }

  public override void Visit(ThisExpr thisExpression) { // TODO is this ever called?
    //# builder.Push("thisExpression", thisExpression.tok, SemanticTokenType.Variable, SemanticTokenModifier.Declaration);
    base.Visit(thisExpression);
  }

  public override void Visit(DisplayExpression displayExpression) { // set x | …
    //# builder.Push("displayExpression", displayExpression.tok, SemanticTokenType.Keyword);
    base.Visit(displayExpression);
  }

  public override void Visit(LambdaExpr lambdaExpression) {
    base.Visit(lambdaExpression);
  }

  public override void Visit(ForallExpr forallExpression) {
    //# builder.Push("forallExpression", forallExpression.tok, SemanticTokenType.Keyword);
    base.Visit(forallExpression);
  }

  public override void Visit(ExistsExpr existsExpression) {
    //# builder.Push("existsExpression", existsExpression.tok, SemanticTokenType.Keyword);
    base.Visit(existsExpression);
  }

  public override void Visit(SetComprehension setComprehensionExpression) {
    //# builder.Push("setComprehensionExpression", setComprehensionExpression.tok, SemanticTokenType.Keyword);
    base.Visit(setComprehensionExpression);
  }

  public override void Visit(MapComprehension mapComprehensionExpression) {
    //# builder.Push("mapComprehensionExpression", mapComprehensionExpression.tok, SemanticTokenType.Keyword);
    base.Visit(mapComprehensionExpression);
  }


  public override void Visit(AttributedExpression attributedExpression) {
    base.Visit(attributedExpression);
  }

  public override void Visit(SeqSelectExpr sequenceSelectExpression) {
    base.Visit(sequenceSelectExpression);
  }

  public override void Visit(TypeParameter typeParameter) {
    builder.Push("typeParameter", typeParameter.tok, SemanticTokenType.TypeParameter);
    base.Visit(typeParameter);
  }

  public override void Visit(ParensExpression parenthesesExpression) {
    base.Visit(parenthesesExpression);
  }

  public override void Visit(UnaryExpr unaryExpression) {
    //# builder.Push("unaryExpression", unaryExpression.tok, SemanticTokenType.Operator);
    base.Visit(unaryExpression);
  }

  public override void Visit(BinaryExpr binaryExpression) {
    //# builder.Push("binaryExpression", binaryExpression.tok, SemanticTokenType.Operator);
    base.Visit(binaryExpression);
  }

  public override void Visit(TernaryExpr ternaryExpression) {
    //# builder.Push("ternaryExpression", ternaryExpression.tok, SemanticTokenType.Operator);
    base.Visit(ternaryExpression);
  }

  public override void Visit(ChainingExpression chainingExpression) {
    base.Visit(chainingExpression);
  }

  public override void Visit(NegationExpression negationExpression) {
    //# builder.Push("negationExpression", negationExpression.tok, SemanticTokenType.Operator);
    base.Visit(negationExpression);
  }

  public override void Visit(OldExpr oldExpression) {
    //# builder.Push("oldExpression", oldExpression.tok, SemanticTokenType.Macro, SemanticTokenModifier.DefaultLibrary);
    base.Visit(oldExpression);
  }

  public override void Visit(ITEExpr ifThenElseExpression) { // FIME: missing then, else
    //# builder.Push("ifThenElseExpression", ifThenElseExpression.tok, SemanticTokenType.Keyword);
    base.Visit(ifThenElseExpression);
  }

  public override void Visit(NestedMatchExpr nestedMatchExpression) {
    //# builder.Push("nestedMatchExpression", nestedMatchExpression.tok, SemanticTokenType.Keyword);
    base.Visit(nestedMatchExpression);
  }

  public override void Visit(NestedMatchCaseExpr nestedMatchCaseExpression) {
    //# builder.Push("nestedMatchCaseExpression", nestedMatchCaseExpression.Tok, SemanticTokenType.Keyword);
    base.Visit(nestedMatchCaseExpression);
  }

  public override void Visit(SetDisplayExpr setDisplayExpression) {
    //# builder.Push("setDisplayExpression", setDisplayExpression.tok, SemanticTokenType.Keyword);
    base.Visit(setDisplayExpression);
  }

  public override void Visit(MultiSetDisplayExpr multiSetDisplayExpression) {
    //# builder.Push("multiSetDisplayExpression", multiSetDisplayExpression.tok, SemanticTokenType.Keyword);
    base.Visit(multiSetDisplayExpression);
  }

  public override void Visit(SeqDisplayExpr sequenceDisplayExpression) {
    //# builder.Push("sequenceDisplayExpression", sequenceDisplayExpression.tok, SemanticTokenType.Keyword);
    base.Visit(sequenceDisplayExpression);
  }

  public override void Visit(FrameExpression frameExpression) {
    //# builder.Push("frameExpression", frameExpression.tok, SemanticTokenType.Operator);
    base.Visit(frameExpression);
  }

  public override void Visit(ExtendedPattern extendedPattern) {
    base.Visit(extendedPattern);
  }

  public override void Visit(StmtExpr statementExpression) {
    base.Visit(statementExpression);
  }

  public override void Visit(LetExpr letExpression) {
    base.Visit(letExpression);
  }
}
