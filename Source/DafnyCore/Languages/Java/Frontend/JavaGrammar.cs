// See https://aka.ms/new-console-template for more information

using System;
using System.Collections.Generic;
using System.Linq;
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

  public JavaGrammar(Uri uri) {
    this.uri = uri;
    name = GetNameGrammar();
    type = TypeGrammar();
    expression = Recursive<Expression>(GetExpressionGrammar);
    statement = Recursive<Statement>(self => {
      var r = Statement(self);
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
    return Class().Many().Map(c => {
      var result = new FileModuleDefinition(Token.NoToken);
      result.SourceDecls.AddRange(c);
      return result;
    }, m => m.SourceDecls.OfType<ClassDecl>().ToList());
  }
  
  Grammar<ClassDecl> Class() {
    var header = Value(() => new ClassDecl()).
      Then("class").
      Then(name, cl => cl.NameNode);
    
    var body = Member().Many().InBraces();

    return header.
      Then(body, cl => cl.Members, Orientation.Vertical).
      SetRange((cl, t) => cl.RangeToken = Convert(t));
  }

  Grammar<MemberDecl> Member() {
    return Method().UpCast<Method, MemberDecl>();
  }

  Grammar<Method> Method() {
    // Need something special for a unordered bag of keywords
    var staticc = Keyword("static").Then(Constant(true)).Default(() => false);
    var returnParameter = type.Map(
      t => new Formal(t.Tok,"_returnName", t, false, false, null), 
      f=> f.Type);
    var outs = returnParameter.Option(Keyword("void")).OptionToList();

    var parameter = Value(() => new Formal()).
      Then(type, f => f.Type).
      Then(name, f => new Name(f.Name), (f,v) => {
        f.Name = v.Value;
        f.tok = v.tok;
      }).
      SetRange((f, t) => f.RangeToken = Convert(t));
    var parameters = parameter.Many().InParens();

    return Value(() => new Method()).
      Then(staticc, m => m.IsStatic).
      Then(outs, m => m.Outs).
      Then(name, m => m.NameNode).
      Then(parameters, m => m.Ins).
      Then(block, m => m.Body, Orientation.Vertical).
      SetRange((m, r) => m.RangeToken = Convert(r));
  }
  
  struct VarDeclData {
    public LocalVariable Local { get; set; }
    public Expression? Initializer { get; set; }
  }
  
  (Grammar<Statement> Statement, Grammar<BlockStmt> Block) Statement(Grammar<Statement> self) {
    var block = self.Many().InBraces().Map(
      (r, ss) => new BlockStmt(Convert(r), ss), 
      b => b.Body);
    var returnExpression = Keyword("return").Then(expression).Then(";").
      Map((r, e) =>
      new ReturnStmt(Convert(r), [new ExprRhs(e)]), r => ((ExprRhs)r.Rhss.First()).Expr);
    var ifStatement = Value(() => new IfStmt()).
      Then("if").Then(expression.InParens(), s => s.Guard).
      Then(block, s => s.Thn);

    var initializer = Keyword("=").Then(expression).Option();
    var localStart = Value(() => new LocalVariable()).
      Then(type, s => s.Type).
      Then(Identifier, s => s.Name).
      SetRange((v, r) => v.RangeToken = Convert(r));
    var varDecl = Value(() => new VarDeclData()).
      Then(localStart, s => s.Local).
      Then(initializer, s => s.Initializer).Then(";").
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
    var statement = returnExpression.UpCast<ReturnStmt, Statement>().OrCast(ifStatement).OrCast(block);
    return (statement, block);
  }

  Grammar<Expression> GetExpressionGrammar(Grammar<Expression> self) {
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
      Then(opCode, b => b.Op).
      Then(self, b => b.E1);

    var variableRef = Identifier.Map((r, v) => new IdentifierExpr(Convert(r), v), ie => ie.Name);
    var number = Number.Map((r, v) => new LiteralExpr(Convert(r), v), l => throw new NotImplementedException());
    var nonGhostBinding = self.Map(e => new ActualBinding(null, e), a => a.Actual);
    var nonGhostBindings = nonGhostBinding.Many().
      Map(b => new ActualBindings(b), a => a.ArgumentBindings);
    var call = self.Assign(() => new ApplySuffix(), s => s.Lhs)
      .Then(nonGhostBindings.InParens(), s => s.Bindings);
    
    return ternary.UpCast<ITEExpr, Expression>().OrCast(binary).OrCast(variableRef).OrCast(number).OrCast(call);
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
    return intGrammar.UpCast<IntType, Type>().OrCast(userDefinedType);
  }


  private Grammar<Name> GetNameGrammar() => 
    Identifier.Map((t, value) => new Name(ConvertValue(t.From, value)), n => n.Value);
}

// class Div {
//   int Foo(int x) {
//     return 3 / x;
//   }
// }
// class Fib {
//   static int FibonacciSpec(int n) {
//     return n < 2 ? n : FibonacciSpec(n - 1) + FibonacciSpec(n - 2);
//   }
//
//   static int Fibonacci(int n)
//     // ensures result == FibonacciSpec(n)
//   {
//     if (n == 0) {
//       return 0;
//     }
//
//     int iMinMinResult = 0;
//     int iResult = 1;
//     int i = 1;
//     while(i < n)
//       // invariant iResult == FibonacciSpec(i)
//       // invariant iMinMinResult == FibonacciSpec(i - 1)
//       // invariant i <= n
//     {
//       i = i + 1;
//       int temp = iResult + iMinMinResult;
//       iMinMinResult = iResult;
//       iResult = temp;
//     }
//     return iResult;
//   }
// }