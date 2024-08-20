// See https://aka.ms/new-console-template for more information

#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using CompilerBuilder;
using CompilerBuilder.Grammars;
using static CompilerBuilder.GrammarBuilder;

namespace Microsoft.Dafny;

public class JavaGrammar {

  private readonly Grammar<Expression> expression;
  private readonly Grammar<Name> name;
  private readonly Uri uri;
  private readonly DafnyOptions options;
  private readonly Grammar<Type> type;
  private readonly Grammar<Statement> statement;
  private Grammar<BlockStmt> block;
  private Grammar<ApplySuffix> call;
  private readonly Grammar<AttributedExpression> attributedExpression;

  private readonly ISet<string> keywords = new HashSet<string>() { "return" };
  private readonly Grammar<string> identifier;

  public JavaGrammar(Uri uri, DafnyOptions options) {
    this.uri = uri;
    this.options = options;
    identifier = Identifier.Where(i => !keywords.Contains(i));
    name = GetNameGrammar();
    type = TypeGrammar();
    expression = Recursive<Expression>(self => {
      var t = GetExpressionGrammar(self);
      call = t.call;
      return t.expression;
    }, "expression");
    attributedExpression = expression.Map(
      e => new AttributedExpression(e),
      ae => ae.E);
    statement = Recursive<Statement>(self => {
      var r = StatementGrammar(self);
      block = r.Block;
      return r.Statement;
    }, "statement");
  }

  public Grammar<FileModuleDefinition> GetFinalGrammar()
  {
    var result = File();
    return Comments.AddTrivia(result, Comments.JavaTrivia());
  }


  public IToken ConvertValue(IPosition position, string value) {
    return new Token {
      col = position.Column + 1,
      line = position.Line + 1,
      pos = position.Offset,
      Uri = uri,
      val = value
    };
  }
  
  public IToken ConvertToken(ParseRange position) {
    return new Token {
      col = position.From.Column + 1,
      line = position.From.Line + 1,
      pos = position.From.Offset,
      Uri = uri,
      val = new string('f', position.Until.Offset - position.From.Offset)
    };
  }
  
  public IToken Convert(IPosition position) {
    return new Token {
      col = position.Column + 1,
      line = position.Line + 1,
      pos = position.Offset,
      Uri = uri,
    };
  }
  
  public RangeToken Convert(ParseRange parseRange) {
    return new RangeToken(Convert(parseRange.From), Convert(parseRange.Until));
  }

  public Grammar<FileModuleDefinition> File() {
    var package = Keyword("package").Then(identifier.CommaSeparated()).Then(";").Ignore();

    var include = Keyword("include").Then(StringInDoubleQuotes).Map((r, s) =>
        new Include(ConvertToken(r), uri, new Uri(Path.GetFullPath(s, Path.GetDirectoryName(uri.LocalPath)!)), options),
      i => i.IncludedFilename.LocalPath);
    var includes = include.Many(Separator.Linebreak);
    
    var qualifiedId = name.Map(n => new ModuleQualifiedId([n]), q => q.Path[0]);
    var import = Keyword("import").Then(qualifiedId).Then(";", Separator.Nothing).Map(
        (t, a) => new AliasModuleDecl(DafnyOptions.Default, 
          Convert(t), a, a.Path[^1], null, true, [], Guid.NewGuid()), 
        a => a.TargetQId);
    
    var classes = Class().Many(Separator.EmptyLine);
    var imports = import.Many(Separator.Linebreak);
    return Constructor<FileModuleDefinition>().Then(package).
      Then(includes, f => f.Includes).
      Then(imports, f => f.SourceDecls.OfType<AliasModuleDecl>().ToList(),
        (f, a) => f.SourceDecls.AddRange(a), Separator.EmptyLine).
      Then(classes,
      f => f.SourceDecls.OfType<ClassDecl>().ToList(),
      (f, c) => f.SourceDecls.AddRange(c), Separator.EmptyLine);
  }
  
  Grammar<ClassDecl> Class() {
    var header = Constructor<ClassDecl>().
      Then(Modifier("final").Ignore()). // TODO Bind to attribute 
      Then("class").
      Then(name, cl => cl.NameNode);
    
    var body = Member().Many(Separator.EmptyLine).InBraces();

    return header.
      Then(body, cl => cl.Members).
      FinishRangeNode(uri);
  }

  Grammar<MemberDecl> Member() {
    var (method, function) = MethodAndFunction();
    return method.UpCast<Method, MemberDecl>().OrCast(function);
  }
  
  (Grammar<Method> Method, Grammar<Function> Function) MethodAndFunction() {
    // Need something special for a unordered bag of keywords
    var staticc = Keyword("static").Then(Constant(true)).Default(false);

    var parameter = Constructor<Formal>().
      Then(type, f => f.Type).
      Then(name, f => new Name(f.Name), (f,v) => {
        f.Name = v.Value;
        f.tok = v.tok;
      }).
      SetRange((f, t) => {
        f.RangeToken = Convert(t);
        f.tok = ConvertToken(t);
        f.InParam = true;
      });
    
    var parameters = parameter.CommaSeparated().InParens();
    var require = Keyword("requires").Then(attributedExpression);
    var requires = require.Many(Separator.Linebreak);

    var ensure = Keyword("ensures").Then(attributedExpression);
    var ensures = ensure.Many(Separator.Linebreak);

    var returnParameter = type.Map(
      t => new Formal(t.Tok,"_returnName", t, false, false, null), 
      f=> f.Type);
    var voidReturnType = Keyword("void").Then(Constant<Formal?>(null));
    var outs = voidReturnType.OrCast(returnParameter).OptionToList();
    
    var frameField = Keyword("`").Then(identifier);
    
    var wildcardFrame = Constructor<FrameExpression>().Then(
      Keyword("*").Then(Constructor<WildcardExpr>()).UpCast<WildcardExpr, Expression>(), f => f.OriginalExpression);
    var receiverFrame = Constructor<FrameExpression>().Then(expression, f => f.OriginalExpression)
      .Then(frameField.Option(), f => f.FieldName);
    var implicitThisFrame = Constructor<FrameExpression>().Then(
      Constructor<ImplicitThisExpr>().UpCast<ImplicitThisExpr, Expression>(), f => f.OriginalExpression);
    
    var frameExpression = wildcardFrame.Or(receiverFrame.Or(implicitThisFrame));
    
    var modify = Keyword("modifies").Then(frameExpression);
    var modifies = modify.Many(Separator.Linebreak).Map(xs => new Specification<FrameExpression>(xs, null),
      s => s.Expressions);
    var method = Constructor<Method>().
      Then(staticc, m => m.IsStatic).
      Then(outs, m => m.Outs).
      Then(name, m => m.NameNode).
      Then(parameters, m => m.Ins, Separator.Nothing).
      // TODO optional: allow unordered required and modifies
      Then(requires.Indent(), m => m.Req, Separator.Linebreak).
      Then(modifies.Indent(), m => m.Mod, Separator.Linebreak).
      Then(ensures.Indent(), m => m.Ens, Separator.Linebreak).
      Then(block, m => m.Body, Separator.Linebreak).
      FinishRangeNode(uri);

    var expressionBody = Keyword("return").
      Then(expression).
      Then(";", Separator.Nothing).InBraces();
    var function = Constructor<Function>().
      Then(Keyword("@Function")).
      Then(staticc, m => m.IsStatic, Separator.Linebreak).
      Then(type, m => m.ResultType).
      Then(name, m => m.NameNode).
      Then(parameters, m => m.Ins, Separator.Nothing).
      Then(requires.Indent(), f => f.Req, Separator.Linebreak).
      Then(ensures.Indent(), f => f.Ens, Separator.Linebreak).
      Then(expressionBody, m => m.Body).
      FinishRangeNode(uri);

    return (method, function);
  }
  
  (Grammar<Statement> Statement, Grammar<BlockStmt> Block) StatementGrammar(Grammar<Statement> self) {
    var blockResult = self.Many(Separator.Linebreak).InBraces().
      Assign<BlockStmt, List<Statement>>(b => b.Body).FinishRangeNode(uri);
    
    var returnStatement = Keyword("return").Then(expression).Then(";", Separator.Nothing).
      Map((r, e) =>
      new ReturnStmt(Convert(r), [new ExprRhs(e)]), r => ((ExprRhs)r.Rhss.First()).Expr);
    var ifStatement = Constructor<IfStmt>().
      Then("if").Then(expression.InParens(), s => s.Guard).
      Then(blockResult, s => s.Thn).
      Then(Keyword("else").Then(self).Option(), s => s.Els);

    var expressionStatement = expression.DownCast<Expression, ApplySuffix>().
      Then(";", Separator.Nothing).Map(
      (t, a) => new UpdateStmt(Convert(t), new List<Expression>(), [new ExprRhs(a) {
        tok = Convert(t.From)
      }]),
      updateStmt => MapResult<ApplySuffix>.FromNullable((updateStmt.Rhss[0] as ExprRhs)?.Expr as ApplySuffix)
      );
    
    var oneLiteral = Expression.CreateIntLiteral(Token.NoToken, 1);

    var incrementStatement = expression.Then("++").Then(";").Map(
      (t, e) => new UpdateStmt(Convert(t), [e], [new ExprRhs(new BinaryExpr(ConvertToken(t),
        BinaryExpr.Opcode.Add, e, oneLiteral)) {
        tok = Convert(t.From)
      }]),
      updateStmt => updateStmt.Rhss.Count == 1 && ((updateStmt.Rhss[0] as ExprRhs)?.Expr 
        is BinaryExpr { Op: BinaryExpr.Opcode.Add } binaryExpr) && binaryExpr.E1 == oneLiteral
                    ? new MapSuccess<Expression>(updateStmt.Lhss[0]) : new MapFail<Expression>());

    var initializer = Keyword("=").Then(expression).Option();
    var ghostModifier = Modifier("ghost");
    var localStart = Constructor<LocalVariable>().
      Then(ghostModifier, s => s.IsGhost).
      Then(type, s => s.SyntacticType).
      Then(identifier, s => s.Name).
      FinishRangeNode(uri);
    var assert = Constructor<AssertStmt>().
      Then(Keyword("assert")).
      Then(expression, a => a.Expr).
      Then(";", Separator.Nothing);
    
    var varDecl = Constructor<VarDeclData>().
      Then(localStart, s => s.Local).
      Then(initializer, s => s.Initializer).Then(";", Separator.Nothing).
      Map((t, data) => {
        var locals = new List<LocalVariable> {
          data.Local
        };

        ConcreteUpdateStatement? update = null;
        if (data.Initializer != null) {
          var local = locals[0];
          update = CreateSingleUpdate(new Name(local.RangeToken, local.Name), data.Initializer);
        }
        return new VarDeclStmt(Convert(t), locals, update);
      }, varDeclStmt => new VarDeclData {
        Initializer = ((varDeclStmt.Update as UpdateStmt)?.Rhss[0] as ExprRhs)?.Expr,
        Local = varDeclStmt.Locals[0]
      });

    var autoGhostidentifier = Constructor<AutoGhostIdentifierExpr>().
      Then(identifier, g => g.Name).FinishTokenNode(uri);

    var assignmentRhs = expression.Map(e => new ExprRhs(e), e => e.Expr).FinishTokenNode(uri);
    var assignmentStatement = Constructor<UpdateStmt>().
      Then(autoGhostidentifier.UpCast<AutoGhostIdentifierExpr, Expression>().Singleton(), s => s.Lhss).
      Then(Keyword("=")).Then(assignmentRhs.UpCast<ExprRhs, AssignmentRhs>().Singleton(), s => s.Rhss).
      Then(";", Separator.Nothing).FinishRangeNode(uri);
    
    var invariant = Keyword("invariant").Then(attributedExpression);
    var invariants = invariant.Many(Separator.Linebreak).Indent();
    
    var decrease = Keyword("decreases").Then(expression);
    var decreases = decrease.Many(Separator.Linebreak).Map(
      (r, xs) => new Specification<Expression>(xs, null) {
        RangeToken = Convert(r),
        tok = ConvertToken(r)
      },
      s => s.Expressions).Indent();
    var whileStatement = Constructor<WhileStmt>().Then(Keyword("while")).
      Then(expression.InParens(), w => w.Guard).
      Then(invariants, w => w.Invariants, Separator.Linebreak).
      Then(decreases, w => w.Decreases, Separator.Linebreak).
      Then(blockResult, w => w.Body, Separator.Linebreak).FinishRangeNode(uri);
      
    var result = Fail<Statement>("a statement").OrCast(returnStatement).
      OrCast(ifStatement).OrCast(blockResult).OrCast(expressionStatement).OrCast(assert).OrCast(varDecl).
      OrCast(whileStatement).OrCast(assignmentStatement).OrCast(incrementStatement);
    return (result, blockResult);
  }

  private static ConcreteUpdateStatement CreateSingleUpdate(Name name, Expression value)
  {
    return new UpdateStmt(value.RangeToken, [
      new AutoGhostIdentifierExpr(name.Tok, name.Value) { RangeToken = name.RangeToken }], 
      [new ExprRhs(value)]);
  }

  (Grammar<Expression> expression, Grammar<ApplySuffix> call) GetExpressionGrammar(Grammar<Expression> self) {
    // Precedence of Java operators: https://introcs.cs.princeton.edu/java/11precedence/
    
    var variableRef = identifier.Map(
      (r, v) => new NameSegment(Convert(r), v, null), 
      ie => ie.Name);
    var number = Number.Map(
      (r, v) => new LiteralExpr(Convert(r), v), l => (int)(BigInteger)l.Value);
    var nonGhostBinding = self.Map((t, e) => new ActualBinding(null, e) {
      RangeToken = Convert(t),
      tok = ConvertToken(t)
    }, a => a.Actual);
    var nonGhostBindings = nonGhostBinding.CommaSeparated().
      Map((t, b) => new ActualBindings(b) {
        RangeToken = Convert(t)
      }, a => a.ArgumentBindings);
    
    var drop = self.Assign(() => new SeqSelectExpr(false), s => s.Seq).
      Then(".").Then("drop")
      .Then(self.InParens(), s => s.E0).
      FinishTokenNode(uri);
    var take = self.Assign(() => new SeqSelectExpr(false), s => s.Seq).
      Then(".").Then("take").
      Then(self.InParens(), s => s.E1).
      FinishTokenNode(uri);
    var get = self.Assign(() => new SeqSelectExpr(true), s => s.Seq).
      Then(".").Then("get").
      Then(self.InParens(), s => s.E0).
      FinishTokenNode(uri);
    var length = self.Assign(() => new UnaryOpExpr(UnaryOpExpr.Opcode.Cardinality), s => s.E).
      Then(".").Then("size").
      Then("(").Then(")").
      FinishTokenNode(uri);
    
    var callResult = self.Assign(() => new ApplySuffix(), s => s.Lhs)
      .Then(nonGhostBindings.InParens(), s => s.Bindings, Separator.Nothing).
      FinishTokenNode(uri);

    var exprDotName = self.Assign(() => new ExprDotName(), c => c.Lhs).
      Then(".").
      Then(identifier, c => c.SuffixName).
      FinishTokenNode(uri);
    
    var lambdaParameter = Constructor<BoundVar>().
      Then(type.Option(), f => f.Type).
      Then(name, f => new Name(f.Name), (f,v) => {
        f.Name = v.Value;
        f.tok = v.tok;
      }).
      FinishTokenNode(uri);
    var parameters = lambdaParameter.CommaSeparated();
    var lambda = Constructor<LambdaExpr>().
      Then(parameters, e => e.BoundVars).
      Then("->").
      Then(self, l => l.Term);

    var charLiteral = CharInSingleQuotes.Map<string, CharLiteralExpr>(
      (r, c) => new CharLiteralExpr(ConvertToken(r), c),
      e => (string)e.Value);

    var parenthesis = Keyword("(").Then(self).Then(")").Map(
      (t, e) => new ParensExpression(ConvertToken(t), e),
      p => p.E);

    // TODO fix position
    var truee = Keyword("true").Then(Constant(Expression.CreateBoolLiteral(Token.Parsing, true)));
    // TODO fix position
    var falsee = Keyword("false").Then(Constant(Expression.CreateBoolLiteral(Token.Parsing, false)));
    
    Grammar<Expression> code = Fail<Expression>("an expression").
      OrCast(variableRef).OrCast(number).OrCast(lambda).OrCast(charLiteral).OrCast(truee).OrCast(falsee).
      OrCast(drop).OrCast(take).OrCast(get).OrCast(parenthesis).OrCast(length).OrCast(exprDotName).OrCast(callResult);
    
    
    // postfix expr++ expr--

    // unary ++expr --expr +expr -expr ~ !
    var unary = Recursive<Expression>(unarySelf => {
      var unicodeOpcode =
        Keyword("!").Then(Constant(UnaryOpExpr.Opcode.Not));
      var prefixUnary = unicodeOpcode.Assign(() => new UnaryOpExpr(), b => b.Op).
        Then(unarySelf, u => u.E);

      return code.OrCast(prefixUnary);
    }, "unary");
    
    // cast
    var downcast = Recursive<Expression>(castSelf => {
      var cast = Constructor<ConversionExpr>().
        Then(type.InParens(), c => c.ToType).
        Then(castSelf, c => c.E);
      return unary.OrCast(cast);
    }, "cast");
    
    // multiplicative * / %
    var multiplicative = Recursive<Expression>(multiplicativeSelf => {
      var opCodes = Keyword("*").Then(Constant(BinaryExpr.Opcode.Mul)).Or(
        Keyword("/").Then(Constant(BinaryExpr.Opcode.Div))).Or(
        Keyword("%").Then(Constant(BinaryExpr.Opcode.Mod)));
      return downcast.OrCast(CreateBinary(multiplicativeSelf,  downcast, opCodes, true));
    }, "multiplicative");

    // additive + -
    var additive = Recursive<Expression>(additiveSelf => {
      var opCodes = Keyword("-").Then(Constant(BinaryExpr.Opcode.Sub)).Or(
        Keyword("+").Then(Constant(BinaryExpr.Opcode.Add)));
      return multiplicative.OrCast(CreateBinary(additiveSelf, multiplicative, opCodes, true));
    }, "additive");
      
    // shift	<< >> >>>
    var shift = additive;
    
    // relational	< > <= >= instanceof
    var relational = Recursive<Expression>(relationalSelf => {
      var opCodes = Keyword("<=").Then(Constant(BinaryExpr.Opcode.Le)).Or(
        Keyword("<").Then(Constant(BinaryExpr.Opcode.Lt)));
      return shift.OrCast(CreateBinary(relationalSelf, shift, opCodes, true));
    }, "relational");
    
    // equality	== !=
    var equality = Recursive<Expression>(equalitySelf => {
      var opCodes = Keyword("==").Then(Constant(BinaryExpr.Opcode.Eq)).Or(
        Keyword("!=").Then(Constant(BinaryExpr.Opcode.Neq)));
      return relational.OrCast(CreateBinary(equalitySelf, relational, opCodes, true));
    }, "equality");
    
    // bitwise AND	&
    var bitwiseAnd = equality;
    
    // bitwise exclusive OR	^
    var bitwiseExclusiveOr = bitwiseAnd;
    
    // bitwise inclusive OR	|
    var bitwiseInclusiveOr = bitwiseExclusiveOr;
    
    var logicalAnd = Recursive<Expression>(logicalAndSelf => {
      var opCodes = Keyword("&&").Then(Constant(BinaryExpr.Opcode.And));
      return bitwiseInclusiveOr.OrCast(CreateBinary(logicalAndSelf,  bitwiseInclusiveOr, opCodes));
    }, "logicalAnd");
    
    var logicalOr = Recursive<Expression>(logicalAndSelf => {
      var opCodes = Keyword("||").Then(Constant(BinaryExpr.Opcode.Or));
      return logicalAnd.OrCast(CreateBinary(logicalAndSelf, logicalAnd, opCodes));
    }, "logicalOr");
    
    // TODO consider not adding ==>
    var implies = Recursive<Expression>(impliesSelf => {
      var opCodes = Keyword("==>").Then(Constant(BinaryExpr.Opcode.Imp));
      return logicalOr.OrCast(CreateBinary(impliesSelf, logicalOr, opCodes));
    }, "implies");

    var ternary = Recursive<Expression>(ternarySelf => {
      var t = ternarySelf.Assign(() => new ITEExpr(), e => e.Test).
        Then("?").
        Then(ternarySelf, e => e.Thn).Then(":").
        Then(ternarySelf, e => e.Els);
      return implies.OrCast(t);
    }, "ternary");

    // assignment	= += -= *= /= %= &= ^= |= <<= >>= >>>=
    
    // var opCode = 
        //Keyword("<==>").Then(Constant(BinaryExpr.Opcode.Iff))).Or(
      // Keyword("==>").Then(Constant(BinaryExpr.Opcode.Imp))).Or(

    Grammar<BinaryExpr> CreateBinary(Grammar<Expression> withSelf, Grammar<Expression> withoutSelf, 
      Grammar<BinaryExpr.Opcode> opCode, bool leftToRight = true) {
      if (leftToRight) {
        return withSelf.Assign(() => new BinaryExpr(), b => b.E0).
          Then(Position, e => null, (e, p) => e.tok = Convert(p)).
          Then(opCode, b => b.Op).
          Then(withoutSelf, b => b.E1);
      } else {
        return withoutSelf.Assign(() => new BinaryExpr(), b => b.E0).
          Then(Position, e => null, (e, p) => e.tok = Convert(p)).
          Then(opCode, b => b.Op).
          Then(withSelf, b => b.E1);
      }
    }

    
    return (ternary, callResult);
  }

  private Grammar<Type> TypeGrammar()
  {
    var nameSegmentForTypeName = 
      identifier.Map((t, i) => new NameSegment(Convert(t), i, new List<Type>()),
      ns => ns.Name);
    // OptGenericInstantiation<out typeArgs, inExpressionContext>
    var intGrammar = Keyword("int").Then(Constant(Type.Int));
    var boolGrammar = Keyword("boolean").Then(Constant(Type.Bool)); 
    var userDefinedType = nameSegmentForTypeName.UpCast<NameSegment, Expression>().
      Map(n => new UserDefinedType(n.Tok, n), udt => udt.NamePath).UpCast<UserDefinedType, Type>();

    // { "."
    //   TypeNameOrCtorSuffix<out tok>       (. List<Type> typeArgs; .)
    //   OptGenericInstantiation<out typeArgs, inExpressionContext>
    //     (. e = new ExprDotName(tok, e, tok.val, typeArgs); .)
    // }
    return Fail<Type>("a type").OrCast(boolGrammar).OrCast(intGrammar).OrCast(userDefinedType);
  }


  private Grammar<Name> GetNameGrammar() => 
    identifier.Map((t, value) => new Name(ConvertValue(t.From, value)), n => n.Value);
}

public static class DafnyGrammarExtensions {
  public static Grammar<T> FinishRangeNode<T>(this Grammar<T> grammar, Uri uri) 
    where T : RangeNode {
    return grammar.SetRange((v, r) => v.RangeToken = Convert(r, uri));
  }
  
  public static Grammar<T> FinishTokenNode<T>(this Grammar<T> grammar, Uri uri) 
    where T : TokenNode {
    return grammar.SetRange((v, r) => {
      v.RangeToken = Convert(r, uri);
      v.tok = ConvertToken(r, uri);
    });
  }
  
  public static IToken ConvertValue(IPosition position, string value, Uri uri) {
    return new Token {
      col = position.Column + 1,
      line = position.Line + 1,
      pos = position.Offset,
      Uri = uri,
      val = value
    };
  }
  
  public static IToken ConvertToken(ParseRange position, Uri uri) {
    return new Token {
      col = position.From.Column + 1,
      line = position.From.Line + 1,
      pos = position.From.Offset,
      Uri = uri,
      val = new string('f', position.Until.Offset - position.From.Offset)
    };
  }
  
  public static IToken Convert(IPosition position, Uri uri) {
    return new Token {
      col = position.Column + 1,
      line = position.Line + 1,
      pos = position.Offset,
      Uri = uri,
    };
  }
  
  public static RangeToken Convert(ParseRange parseRange, Uri uri) {
    return new RangeToken(Convert(parseRange.From, uri), Convert(parseRange.Until, uri));
  }
}
  
public class VarDeclData {
  public LocalVariable Local { get; set; }
  public Expression? Initializer { get; set; }
}