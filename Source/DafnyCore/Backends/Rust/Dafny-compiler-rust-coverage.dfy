/*This module exists to increase code coverage of the generated code
  All modules ending with "Coverage" will be compiled to DafnyCore.Test */
module DafnyToRustCompilerCoverage {
  module RASTCoverage {
    import opened RAST
    import opened Std.Wrappers
    import opened DAST.Format
    import Strings = Std.Strings

    method TestExpr() {
      TestOptimizeToString();
      TestPrintingInfo();
      TestNoExtraSemicolonAfter();
    }

    method TestNoOptimize(e: Expr)
      //requires e.Optimize() == e // Too expensive
    {
    }

    function ConversionNum(t: Type, x: Expr): Expr {
      Call(
        ExprFromPath(
          PMemberSelect(
            PMemberSelect(
              Global(),
              "dafny_runtime"),
            "truncate!")),
        [x, ExprFromType(t)])
    }

    function DafnyIntLiteral(s: string): Expr {
      Call(ExprFromPath(PMemberSelect(dafny_runtime, "int!")), [LiteralInt("1")])
    }

    method TestOptimizeToString() {
      var x := Identifier("x");
      var y := Identifier("y");
      AssertCoverage(UnaryOp("&", Call(Select(x, "clone"), []), UnaryOpFormat.NoFormat).Optimize()
                     == UnaryOp("&", x, UnaryOpFormat.NoFormat));
      TestNoOptimize(UnaryOp("&", Call(Select(x, "clone"), [y]), UnaryOpFormat.NoFormat));
      AssertCoverage(UnaryOp("!", BinaryOp("==", x, y, BinaryOpFormat.NoFormat),
                             CombineFormat()).Optimize() == BinaryOp("!=", x, y, BinaryOpFormat.NoFormat));
      AssertCoverage(UnaryOp("!", BinaryOp("<", x, y, BinaryOpFormat.NoFormat),
                             CombineFormat()).Optimize() == BinaryOp(">=", x, y, BinaryOpFormat.NoFormat()));
      AssertCoverage(UnaryOp("!", BinaryOp("<", x, y, ReverseFormat()),
                             CombineFormat()).Optimize() == BinaryOp("<=", y, x, BinaryOpFormat.NoFormat()));
      AssertCoverage(ConversionNum(I128, DafnyIntLiteral("1")).Optimize() == LiteralInt("1"));
      TestNoOptimize(ConversionNum(I128, x));
      AssertCoverage(StmtExpr(DeclareVar(MUT, "z", Some(I128), None), StmtExpr(AssignVar("z", y), RawExpr("return"))).Optimize()
                     == StmtExpr(DeclareVar(MUT, "z", Some(I128), Some(y)), RawExpr("return")));
      TestNoOptimize(StmtExpr(DeclareVar(MUT, "z", Some(I128), None), StmtExpr(AssignVar("w", y), RawExpr("return"))));

      TestNoOptimize(x);
      TestNoOptimize(StmtExpr(x, x));
      TestNoOptimize(StmtExpr(Match(x, []), x));
      TestNoOptimize(StmtExpr(StructBuild(x, []), x));
      TestNoOptimize(StmtExpr(Tuple([]), x));
      TestNoOptimize(StmtExpr(UnaryOp("&", x, UnaryOpFormat.NoFormat), x));
      TestNoOptimize(StmtExpr(BinaryOp("&&", x, x, BinaryOpFormat.NoFormat), x));
      TestNoOptimize(StmtExpr(TypeAscription(x, I128), x));
      TestNoOptimize(StmtExpr(LiteralInt("1"), x));
      TestNoOptimize(StmtExpr(LiteralString("2", true, false), x));
      TestNoOptimize(StmtExpr(LiteralString("3", false, true), x));
      AssertCoverage(StmtExpr(DeclareVar(MUT, "z", Some(I128), None), StmtExpr(AssignVar("z", y), RawExpr("return"))).Optimize()
                     == StmtExpr(DeclareVar(MUT, "z", Some(I128), Some(y)), RawExpr("return")));

      var coverageExpression := [
        RawExpr("abc"),
        Identifier("x"),
        Match(Identifier("x"), [MatchCase(RawPattern("abc"), Identifier("x"))]),
        StmtExpr(RawExpr("panic!()"), Identifier("a")),
        Block(RawExpr("abc")),
        StructBuild(Identifier("dummy"), [AssignIdentifier("foo", Identifier("bar"))]),
        StructBuild(Identifier("dummy"), [AssignIdentifier("foo", Identifier("bar")), AssignIdentifier("foo2", Identifier("bar"))]),
        Tuple([Identifier("x")]),
        UnaryOp("-", Identifier("x"), UnaryOpFormat.NoFormat),
        BinaryOp("+", Identifier("x"), Identifier("y"), BinaryOpFormat.NoFormat),
        TypeAscription(Identifier("x"), I128),
        LiteralInt("322"),
        LiteralString("abc", true, false),
        LiteralString("abc", false, true),
        DeclareVar(MUT, "abc", Some(I128), None),
        DeclareVar(CONST, "abc", None, Some(Identifier("x"))),
        AssignVar("abc", Identifier("x")),
        IfExpr(Identifier("x"), Identifier("x"), Identifier("x")),
        Loop(Some(Identifier("x")), Identifier("x")),
        For("abc", Identifier("x"), Identifier("x")),
        Labelled("abc", Identifier("x")),
        Break(None),
        Break(Some("l")),
        Continue(None),
        Continue(Some("l")),
        Return(None),
        Return(Some(Identifier("x"))),
        Call(Identifier("x"), []),
        Call(Identifier("x"), [Identifier("x"), Identifier("y")]),
        CallType(Identifier("x"), [I128, U32]),
        Select(Identifier("x"), "abc"),
        ExprFromPath(PMemberSelect(Crate(), "abc")),
        ExprFromPath(PMemberSelect(Global(), "abc"))
      ];
      for i := 0 to |coverageExpression| {
        var c := coverageExpression[i];
        var _ := c.printingInfo;
        var _ := c.Optimize();
        var _ := map[c := c.ToString("")];
        var _ := StmtExpr(DeclareVar(MUT, "abc", Some(I128), None), c).Optimize();
        var _ := StmtExpr(DeclareVar(MUT, "abc", Some(I128), None), StmtExpr(AssignVar("abc", c), RawExpr(""))).Optimize();
        var _ := UnaryOp("&", c, UnaryOpFormat.NoFormat()).Optimize();
        var _ := UnaryOp("!", c, UnaryOpFormat.NoFormat()).Optimize();
        var _ := ConversionNum(U8, c).Optimize();
        var _ := ConversionNum(U8, Call(c, [])).Optimize();
        var _ := c.RightMostIdentifier();

      }
    }

    method TestPrintingInfo() {
      var x := Identifier("x");
      var y := Identifier("y");
      var bnf := BinaryOpFormat.NoFormat;
      AssertCoverage(RawExpr("x").printingInfo.UnknownPrecedence?);
      AssertCoverage(x.printingInfo == Precedence(1));
      AssertCoverage(LiteralInt("3").printingInfo == Precedence(1));
      AssertCoverage(LiteralString("abc", true, false).printingInfo == Precedence(1));
      AssertCoverage(UnaryOp("?", x, UnaryOpFormat.NoFormat).printingInfo == SuffixPrecedence(5));
      AssertCoverage(UnaryOp("-", x, UnaryOpFormat.NoFormat).printingInfo == Precedence(6));
      AssertCoverage(UnaryOp("*", x, UnaryOpFormat.NoFormat).printingInfo == Precedence(6));
      AssertCoverage(UnaryOp("!", x, UnaryOpFormat.NoFormat).printingInfo == Precedence(6));
      AssertCoverage(UnaryOp("&", x, UnaryOpFormat.NoFormat).printingInfo == Precedence(6));
      AssertCoverage(UnaryOp("&mut", x, UnaryOpFormat.NoFormat).printingInfo == Precedence(6));
      AssertCoverage(UnaryOp("!!", x, UnaryOpFormat.NoFormat).printingInfo == UnknownPrecedence());
      AssertCoverage(Select(x, "name").printingInfo == PrecedenceAssociativity(2, LeftToRight));
      AssertCoverage(ExprFromPath(PMemberSelect(Global(), "name")).printingInfo == Precedence(2));
      AssertCoverage(Call(x, []).printingInfo == PrecedenceAssociativity(2, LeftToRight));
      AssertCoverage(TypeAscription(x, I128).printingInfo == PrecedenceAssociativity(10, LeftToRight));
      AssertCoverage(BinaryOp("*", x, y, bnf).printingInfo == PrecedenceAssociativity(20, LeftToRight));
      AssertCoverage(BinaryOp("/", x, y, bnf).printingInfo == PrecedenceAssociativity(20, LeftToRight));
      AssertCoverage(BinaryOp("%", x, y, bnf).printingInfo == PrecedenceAssociativity(20, LeftToRight));
      AssertCoverage(BinaryOp("+", x, y, bnf).printingInfo == PrecedenceAssociativity(30, LeftToRight));
      AssertCoverage(BinaryOp("-", x, y, bnf).printingInfo == PrecedenceAssociativity(30, LeftToRight));
      AssertCoverage(BinaryOp("<<", x, y, bnf).printingInfo == PrecedenceAssociativity(40, LeftToRight));
      AssertCoverage(BinaryOp(">>", x, y, bnf).printingInfo == PrecedenceAssociativity(40, LeftToRight));
      AssertCoverage(BinaryOp("&", x, y, bnf).printingInfo == PrecedenceAssociativity(50, LeftToRight));
      AssertCoverage(BinaryOp("^", x, y, bnf).printingInfo == PrecedenceAssociativity(60, LeftToRight));
      AssertCoverage(BinaryOp("|", x, y, bnf).printingInfo == PrecedenceAssociativity(70, LeftToRight));
      AssertCoverage(BinaryOp("==", x, y, bnf).printingInfo == PrecedenceAssociativity(80, RequiresParentheses));
      AssertCoverage(BinaryOp("!=", x, y, bnf).printingInfo == PrecedenceAssociativity(80, RequiresParentheses));
      AssertCoverage(BinaryOp("<", x, y, bnf).printingInfo == PrecedenceAssociativity(80, RequiresParentheses));
      AssertCoverage(BinaryOp(">", x, y, bnf).printingInfo == PrecedenceAssociativity(80, RequiresParentheses));
      AssertCoverage(BinaryOp("<=", x, y, bnf).printingInfo == PrecedenceAssociativity(80, RequiresParentheses));
      AssertCoverage(BinaryOp(">=", x, y, bnf).printingInfo == PrecedenceAssociativity(80, RequiresParentheses));
      AssertCoverage(BinaryOp("&&", x, y, bnf).printingInfo == PrecedenceAssociativity(90, LeftToRight));
      AssertCoverage(BinaryOp("||", x, y, bnf).printingInfo == PrecedenceAssociativity(100, LeftToRight));
      AssertCoverage(BinaryOp("..", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RequiresParentheses));
      AssertCoverage(BinaryOp("..=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RequiresParentheses));
      AssertCoverage(BinaryOp("=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("+=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("-=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("*=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("/=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("%=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("&=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("|=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("^=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("<<=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp(">>=", x, y, bnf).printingInfo == PrecedenceAssociativity(110, RightToLeft));
      AssertCoverage(BinaryOp("?!?", x, y, bnf).printingInfo == PrecedenceAssociativity(0, RequiresParentheses));
      AssertCoverage(Break(None).printingInfo == UnknownPrecedence());
    }

    method AssertCoverage(x: bool)
      //requires x // Too expensive
    {
    }

    method TestNoExtraSemicolonAfter() {
      AssertCoverage(RawExpr(";").NoExtraSemicolonAfter());
      AssertCoverage(!RawExpr("a").NoExtraSemicolonAfter());
      AssertCoverage(Return(None).NoExtraSemicolonAfter());
      AssertCoverage(Continue(None).NoExtraSemicolonAfter());
      AssertCoverage(Break(None).NoExtraSemicolonAfter());
      AssertCoverage(AssignVar("x", Identifier("y")).NoExtraSemicolonAfter());
      AssertCoverage(DeclareVar(MUT, "x", None, None).NoExtraSemicolonAfter());
      AssertCoverage(!Identifier("x").NoExtraSemicolonAfter());
    }
  }
}
