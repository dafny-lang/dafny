// See https://aka.ms/new-console-template for more information

using System.Numerics;
using System.Reflection.Emit;
using CompilerBuilder;
using Microsoft.Dafny;
using static CompilerBuilder.GrammarBuilder;
using Name = Microsoft.Dafny.Name;
using Type = Microsoft.Dafny.Type;

namespace JavaSupport;

class JavaGrammar {
  Grammar<ClassDecl> Class() {
    var header = Value(new ClassDecl()).
      Then("class").
      Then(Name, cl => cl.NameNode);
    
    var body = Member().Many().InBraces();

    return header.
      Then(body, cl => cl.Members, Orientation.Vertical).
      SetRange((cl, t) => cl.RangeToken = t);
  }

  Grammar<MemberDecl> Member() {
    return Method().UpCast<Method, MemberDecl>();
  }

  Grammar<Method> Method() {
    // Need something special for a unordered bag of keywords
    var staticc = Keyword("static").Then(Value(true)).Default(false);
    var type = Type();
    var returnParameter = type.Map(
      t => new Formal(Token.NoToken,"_returnName", t, false, false, null), 
      f=> f.Type);
    var outs = returnParameter.Option(Keyword("void")).OptionToList();

    var parameter = Value(new Formal()).
      Then(type, f => f.Type).
      Then(Identifier, f => f.Name);
    var parameters = parameter.Many().InParens();

    return Value(new Method()).
      Then(staticc, m => m.IsStatic).
      Then(outs, m => m.Outs).
      Then(Name, m => m.NameNode).
      Then(parameters, m => m.Ins).
      Then(Block(), m => m.Body, Orientation.Vertical);
  }

  Grammar<BlockStmt> Block() {
    return Statement().Many().InBraces().Map((r, ss) => new BlockStmt(r, ss), b => b.Body);
  }
  
  Grammar<Statement> Statement() {
    var returnExpression = Keyword("return").Then(Expression()).Map((r, e) =>
      new ReturnStmt(r, [new ExprRhs(e)]), r => ((ExprRhs)r.Rhss.First()).Expr);

    return Fail<Statement>().Or(returnExpression);
  }

  private static Grammar<Expression> expression = Expression();
  private static Grammar<Expression> expressionRef = new Recursive<Expression>(() => expression);

  static Grammar<Expression> Expression() {
    var ternary = Value(new ITEExpr()).
      Then(expressionRef, e => e.Test).
      Then("?").Then(expressionRef, e => e.Thn).
      Then(":").Then(expressionRef, e => e.Els);

    var opCode = 
      Keyword("<").Then(Value(BinaryExpr.Opcode.Le)).Or(
      Keyword("/").Then(Value(BinaryExpr.Opcode.Div)));
    var less = Value(new BinaryExpr()).Then(expressionRef, b => b.E0).
      Then(opCode, b => b.Op).
      Then(expressionRef, b => b.E1);

    var variableRef = Identifier.Map((r, v) => new IdentifierExpr(r, v), ie => ie.Name);
    var number = Number.Map((r, v) => new LiteralExpr(r, v), l => throw new NotImplementedException());
    var nonGhostBinding = expressionRef.Map(e => new ActualBinding(null, e), a => a.Actual);
    var nonGhostBindings = nonGhostBinding.Many().Map(b => new ActualBindings(b), a => a.ArgumentBindings);
    var call = Value(new ApplySuffix()).Then(expressionRef, s => s.Lhs)
      .Then(nonGhostBindings.InParens(), s => s.Bindings);
    
    return Fail<Expression>().Or(ternary).Or(less).Or(variableRef).Or(number).Or(call);
  }

  private static Grammar<Type> Type()
  {
    Grammar<NameSegment> nameSegmentForTypeName = Identifier.Map((t, i) => new NameSegment(t, i, new List<Type>()),
      ns => ns.Name);
    // OptGenericInstantiation<out typeArgs, inExpressionContext>
    Grammar<Type> type = nameSegmentForTypeName.UpCast<NameSegment, Expression>().
      Map(n => new UserDefinedType(n.Tok, n), udt => udt.NamePath).UpCast<UserDefinedType, Type>();

    // { "."
    //   TypeNameOrCtorSuffix<out tok>       (. List<Type> typeArgs; .)
    //   OptGenericInstantiation<out typeArgs, inExpressionContext>
    //     (. e = new ExprDotName(tok, e, tok.val, typeArgs); .)
    // }
    return type;
  }


  private static readonly Grammar<Name> Name = 
    Identifier.Map((t, value) => new Name(t, value), n => n.Value);
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