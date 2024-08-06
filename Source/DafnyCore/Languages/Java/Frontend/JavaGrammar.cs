// See https://aka.ms/new-console-template for more information

#nullable enable
using System;
using System.Collections.Generic;
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
  private readonly Grammar<Type> type;
  private readonly Grammar<Statement> statement;
  private Grammar<BlockStmt> block;
  private Grammar<ApplySuffix> call;

  public JavaGrammar(Uri uri) {
    this.uri = uri;
    name = GetNameGrammar();
    type = TypeGrammar();
    expression = Recursive<Expression>(self => {
      var t = GetExpressionGrammar(self);
      call = t.call;
      return t.expression;
    });
    statement = Recursive<Statement>(self => {
      var r = StatementGrammar(self);
      block = r.Block;
      return r.Statement;
    });
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
    var qualifiedId = name.Map(n => new ModuleQualifiedId([n]), q => q.Path[0]);
    var import = Keyword("import").Then(qualifiedId).Then(";", Orientation.Adjacent).Map(
        (t, a) => new AliasModuleDecl(DafnyOptions.Default, 
          Convert(t), a, a.Path[^1], null, true, [], Guid.NewGuid()), 
        a => a.TargetQId);
    
    var classes = Class().Many(Orientation.LineBroken);
    return import.Many(Orientation.Vertical).Map(imports =>
      new FileModuleDefinition(Token.NoToken) {
        SourceDecls = imports.ToList<TopLevelDecl>()
      }, f => f.SourceDecls.OfType<AliasModuleDecl>().ToList()).Then(classes,
      f => f.SourceDecls.OfType<ClassDecl>().ToList(),
      (f, c) => f.SourceDecls.AddRange(c), Orientation.LineBroken);
  }
  
  Grammar<ClassDecl> Class() {
    var header = Constructor<ClassDecl>().
      Then("class").
      Then(name, cl => cl.NameNode);
    
    var body = Member().Many(Orientation.LineBroken).InBraces();

    return header.
      Then(body, cl => cl.Members).
      SetRange((cl, t) => cl.RangeToken = Convert(t));
  }

  Grammar<MemberDecl> Member() {
    return Method().UpCast<Method, MemberDecl>().OrCast(Function());
  }

  Grammar<Function> Function() {
    
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
        f.InParam = true;
      });
    var parameters = parameter.Many().InParens();
    var require = Keyword("requires").Then(expression).Map(
      e => new AttributedExpression(e), 
      ae => ae.E);
    var requires = require.Many();

    var expressionBody = Keyword("return").
      Then(expression).
      Then(";", Orientation.Adjacent).InBraces();
    return Constructor<Function>().
      Then(Keyword("@Function")).
      Then(staticc, m => m.IsStatic, Orientation.Vertical).
      Then(type, m => m.ResultType).
      Then(name, m => m.NameNode).
      Then(parameters, m => m.Ins, Orientation.Adjacent).
      Then(requires.Indent(), m => m.Req, Orientation.Vertical).
      Then(expressionBody, m => m.Body).
      SetRange((m, r) => m.RangeToken = Convert(r));
  }
  
  Grammar<Method> Method() {
    // Need something special for a unordered bag of keywords
    var staticc = Keyword("static").Then(Constant(true)).Default(false);
    var returnParameter = type.Map(
      t => new Formal(t.Tok,"_returnName", t, false, false, null), 
      f=> f.Type);
    var voidReturnType = Keyword("void").Then(Constant<Formal?>(null));
    var outs = voidReturnType.OrCast(returnParameter).OptionToList();

    var parameter = Constructor<Formal>().
      Then(type, f => f.Type).
      Then(name, f => new Name(f.Name), (f,v) => {
        f.Name = v.Value;
        f.tok = v.tok;
      }).
      SetRange((f, t) => {
        f.RangeToken = Convert(t);
        f.InParam = true;
      });
    // TODO replace .Many with .SeparatedBy
    var parameters = parameter.Many().InParens();
    var require = Keyword("requires").Then(expression).Map(
      e => new AttributedExpression(e), 
      ae => ae.E);
    var requires = require.Many(Orientation.Vertical);

    return Constructor<Method>().
      Then(staticc, m => m.IsStatic).
      Then(outs, m => m.Outs).
      Then(name, m => m.NameNode).
      Then(parameters, m => m.Ins, Orientation.Adjacent).
      Then(requires.Indent(), m => m.Req, Orientation.Vertical).
      Then(block, m => m.Body, Orientation.Vertical).
      SetRange((m, r) => m.RangeToken = Convert(r));
  }
  
  struct VarDeclData {
    public LocalVariable Local { get; set; }
    public Expression? Initializer { get; set; }
  }
  
  (Grammar<Statement> Statement, Grammar<BlockStmt> Block) StatementGrammar(Grammar<Statement> self) {
    var block = self.Many(Orientation.Vertical).InBraces().Map(
      (r, ss) => new BlockStmt(Convert(r), ss), 
      b => b.Body);
    var returnExpression = Keyword("return").Then(expression).Then(";", Orientation.Adjacent).
      Map((r, e) =>
      new ReturnStmt(Convert(r), [new ExprRhs(e)]), r => ((ExprRhs)r.Rhss.First()).Expr);
    var ifStatement = Constructor<IfStmt>().
      Then("if").Then(expression.InParens(), s => s.Guard).
      Then(block, s => s.Thn);

    var expressionStatement = expression.DownCast<Expression, ApplySuffix>().
      Then(";", Orientation.Adjacent).Map(
      (t, a) => new UpdateStmt(Convert(t), new List<Expression>(), [new ExprRhs(a) {
        tok = Convert(t.From)
      }]),
      updateStmt => MapResult<ApplySuffix>.FromNullable((updateStmt.Rhss[0] as ExprRhs)?.Expr as ApplySuffix)
      );

    var initializer = Keyword("=").Then(expression).Option();
    var localStart = Constructor<LocalVariable>().
      Then(type, s => s.Type).
      Then(Identifier, s => s.Name).
      SetRange((v, r) => v.RangeToken = Convert(r));
    var varDecl = Constructor<VarDeclData>().
      Then(localStart, s => s.Local).
      Then(initializer, s => s.Initializer).Then(";", Orientation.Adjacent).
      Map((t, data) => {
        var locals = new List<LocalVariable> {
          data.Local
        };

        ConcreteUpdateStatement? update = null;
        if (data.Initializer != null) {
          var lhs = locals.Select(l =>
            new AutoGhostIdentifierExpr(l.Tok, l.Name) { RangeToken = new RangeToken(l.Tok, l.Tok) } ).ToList<Expression>();
          update = new UpdateStmt(data.Initializer.RangeToken, lhs,
            new List<AssignmentRhs>() { new ExprRhs(data.Initializer) });
        }
        return new VarDeclStmt(Convert(t), locals, update);
      }, varDeclStmt => new VarDeclData {
        Initializer = ((varDeclStmt.Update as UpdateStmt)?.Rhss[0] as ExprRhs)?.Expr,
        Local = varDeclStmt.Locals[0]
      });
    // if statement
    // assignment statement
    // variable declaration [initializer]
    var result = Fail<Statement>("a statement").OrCast(returnExpression).
      OrCast(ifStatement).OrCast(block).OrCast(expressionStatement);
    return (result, block);
  }

  (Grammar<Expression> expression, Grammar<ApplySuffix> call) GetExpressionGrammar(Grammar<Expression> self) {
    var ternary = 
      self.Assign(() => new ITEExpr(), e => e.Test).
      Then("?").Then(self, e => e.Thn).
      Then(":").Then(self, e => e.Els);

    var opCode = 
      Keyword("!=").Then(Constant(BinaryExpr.Opcode.Neq)).Or(
      Keyword("-").Then(Constant(BinaryExpr.Opcode.Sub))).Or(
      Keyword("+").Then(Constant(BinaryExpr.Opcode.Add))).Or(
      Keyword("<").Then(Constant(BinaryExpr.Opcode.Le))).Or(
      Keyword("/").Then(Constant(BinaryExpr.Opcode.Div)));
    var binary = self.Assign(() => new BinaryExpr(), b => b.E0).
      Then(Position, e => null, (e, p) => e.tok = Convert(p)).
      Then(opCode, b => b.Op).
      Then(self, b => b.E1);

    var variableRef = Identifier.Map(
      (r, v) => new NameSegment(Convert(r), v, null), 
      ie => ie.Name);
    var number = Number.Map(
      (r, v) => new LiteralExpr(Convert(r), v), l => (int)(BigInteger)l.Value);
    var nonGhostBinding = self.Map((t, e) => new ActualBinding(null, e) {
      RangeToken = Convert(t)
    }, a => a.Actual);
    var nonGhostBindings = nonGhostBinding.Many().
      Map((t, b) => new ActualBindings(b) {
        RangeToken = Convert(t)
      }, a => a.ArgumentBindings);
    var callResult = self.Assign(() => new ApplySuffix(), s => s.Lhs)
      .Then(nonGhostBindings.InParens(), s => s.Bindings, Orientation.Adjacent).
      SetRange((s, t) => s.RangeToken = Convert(t));

    var exprDotName = self.Assign(() => new ExprDotName(), c => c.Lhs).
      Then(".").
      Then(Identifier, c => c.SuffixName).
      SetRange((c,r) => c.RangeToken = Convert(r));
    
    var expressionResult = Fail<Expression>("an expression").OrCast(ternary).OrCast(binary).
      OrCast(variableRef).OrCast(number).OrCast(callResult).OrCast(exprDotName);
    return (expressionResult, callResult);
  }

  private Grammar<Type> TypeGrammar()
  {
    var nameSegmentForTypeName = 
      Identifier.Map((t, i) => new NameSegment(Convert(t), i, new List<Type>()),
      ns => ns.Name);
    // OptGenericInstantiation<out typeArgs, inExpressionContext>
    var intGrammar = Keyword("int").Then(Constant(Type.Int));
    var userDefinedType = nameSegmentForTypeName.UpCast<NameSegment, Expression>().
      Map(n => new UserDefinedType(n.Tok, n), udt => udt.NamePath).UpCast<UserDefinedType, Type>();

    // { "."
    //   TypeNameOrCtorSuffix<out tok>       (. List<Type> typeArgs; .)
    //   OptGenericInstantiation<out typeArgs, inExpressionContext>
    //     (. e = new ExprDotName(tok, e, tok.val, typeArgs); .)
    // }
    return Fail<Type>("a type").OrCast(intGrammar).OrCast(userDefinedType);
  }


  private Grammar<Name> GetNameGrammar() => 
    Identifier.Map((t, value) => new Name(ConvertValue(t.From, value)), n => n.Value);
}