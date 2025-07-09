// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace RASTCoverage {

  public partial class __default {
    public static void AssertCoverage(bool x)
    {
      if (!(x)) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(26,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
    }
    public static void AssertEq<__T>(__T x, __T y)
    {
      if (!(object.Equals(x, y))) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(30,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
    }
    public static void TestExpr()
    {
      RASTCoverage.__default.TestOptimizeToString();
      RASTCoverage.__default.TestPrintingInfo();
      RASTCoverage.__default.TestNoExtraSemicolonAfter();
      RASTCoverage.__default.TestDocstring();
    }
    public static Dafny.ISequence<Dafny.Rune> CanonicalNewlines(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune('\r'))) {
        if (((new BigInteger((s).Count)) > (BigInteger.One)) && (((s).Select(BigInteger.One)) == (new Dafny.Rune('\n')))) {
          _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
          Dafny.ISequence<Dafny.Rune> _in0 = (s).Drop(new BigInteger(2));
          s = _in0;
          goto TAIL_CALL_START;
        } else {
          _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
          Dafny.ISequence<Dafny.Rune> _in1 = (s).Drop(BigInteger.One);
          s = _in1;
          goto TAIL_CALL_START;
        }
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, (s).Take(BigInteger.One));
        Dafny.ISequence<Dafny.Rune> _in2 = (s).Drop(BigInteger.One);
        s = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static void TestOneDocstring(Dafny.ISequence<Dafny.Rune> dafnyDocstring, Dafny.ISequence<Dafny.Rune> rustDocstring, Dafny.ISequence<Dafny.Rune> indent)
    {
      RASTCoverage.__default.AssertEq<Dafny.ISequence<Dafny.Rune>>(RAST.__default.ConvertDocstring(RASTCoverage.__default.CanonicalNewlines(dafnyDocstring), indent, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()), RASTCoverage.__default.CanonicalNewlines(rustDocstring));
    }
    public static void TestDocstring()
    {
      RASTCoverage.__default.TestOneDocstring(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
Hello
World"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  /// Hello
  /// World"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  "));
      RASTCoverage.__default.TestOneDocstring(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
Title
```rs
let mut x = 1;
```
End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  /// Title
  /// ```
  /// let mut x = 1;
  /// ```
  /// End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  "));
      RASTCoverage.__default.TestOneDocstring(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
Title
`````rs
let mut x = 1;
`````
End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  /// Title
  /// `````
  /// let mut x = 1;
  /// `````
  /// End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  "));
      RASTCoverage.__default.TestOneDocstring(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
Title
```
var x := 1;
```
End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  /// Title
  /// ```dafny
  /// var x := 1;
  /// ```
  /// End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  "));
      RASTCoverage.__default.TestOneDocstring(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
Title
`````
var x := 1;
`````
End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  /// Title
  /// `````dafny
  /// var x := 1;
  /// `````
  /// End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  "));
      RASTCoverage.__default.TestOneDocstring(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
Title
`````md
# title
```
code
```
Outside of code
`````
```
dafnycode
```
End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  /// Title
  /// `````md
  /// # title
  /// ```
  /// code
  /// ```
  /// Outside of code
  /// `````
  /// ```dafny
  /// dafnycode
  /// ```
  /// End comment"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  "));
      RASTCoverage.__default.TestOneDocstring(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
Title
    Indented code
    More indented code
Back to normal
   Normal as well
  Also normal
    But this one indented"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  /// Title
  /// |   Indented code
  /// |   More indented code
  /// Back to normal
  ///    Normal as well
  ///   Also normal
  /// |   But this one indented"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  "));
    }
    public static void TestNoOptimize(RAST._IExpr e)
    {
      if (!(object.Equals((RASTCoverage.__default.ExprSimp).ReplaceExpr(e), e))) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-coverage.dfy(157,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
    }
    public static RAST._IExpr ConversionNum(RAST._IType t, RAST._IExpr x)
    {
      return RAST.Expr.create_Call(RAST.Expr.create_ExprFromPath(RAST.Path.create_PMemberSelect(RAST.Path.create_PMemberSelect(RAST.Path.create_Global(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))), Dafny.Sequence<RAST._IExpr>.FromElements(x, RAST.Expr.create_ExprFromType(t)));
    }
    public static RAST._IExpr DafnyIntLiteral(Dafny.ISequence<Dafny.Rune> s) {
      return RAST.Expr.create_Call(RAST.Expr.create_ExprFromPath(RAST.Path.create_PMemberSelect(RAST.__default.dafny__runtime, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))), Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1"))));
    }
    public static RAST._IExpr Optimize(RAST._IExpr e) {
      return (ExpressionOptimization.__default.ExprSimplifier()).ReplaceExpr(e);
    }
    public static void TestOptimizeToString()
    {
      RAST._IExpr _0_x;
      _0_x = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"));
      RAST._IExpr _1_y;
      _1_y = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("y"));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), RAST.Expr.create_Call(RAST.Expr.create_Select(_0_x, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone")), Dafny.Sequence<RAST._IExpr>.FromElements(_1_y)), DAST.Format.UnaryOpFormat.create_NoFormat()));
      RASTCoverage.__default.AssertCoverage(object.Equals(RASTCoverage.__default.Optimize(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _0_x, _1_y, DAST.Format.BinaryOpFormat.create_NoFormat()), DAST.Format.UnaryOpFormat.create_CombineFormat())), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="), _0_x, _1_y, DAST.Format.BinaryOpFormat.create_NoFormat())));
      RASTCoverage.__default.AssertCoverage(object.Equals(RASTCoverage.__default.Optimize(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _0_x, _1_y, DAST.Format.BinaryOpFormat.create_NoFormat()), DAST.Format.UnaryOpFormat.create_CombineFormat())), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="), _0_x, _1_y, DAST.Format.BinaryOpFormat.create_NoFormat())));
      RASTCoverage.__default.AssertCoverage(object.Equals(RASTCoverage.__default.Optimize(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _0_x, _1_y, DAST.Format.BinaryOpFormat.create_ReverseFormat()), DAST.Format.UnaryOpFormat.create_CombineFormat())), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1_y, _0_x, DAST.Format.BinaryOpFormat.create_NoFormat())));
      RASTCoverage.__default.AssertCoverage(object.Equals(RASTCoverage.__default.Optimize(RASTCoverage.__default.ConversionNum(RAST.Type.create_I128(), RASTCoverage.__default.DafnyIntLiteral(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1")))), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1"))));
      RASTCoverage.__default.TestNoOptimize(RASTCoverage.__default.ConversionNum(RAST.Type.create_I128(), _0_x));
      RASTCoverage.__default.AssertCoverage(object.Equals(RASTCoverage.__default.Optimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_None()), RAST.Expr.create_StmtExpr(RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"), _1_y), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"))))), RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1_y)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return")))));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_None()), RAST.Expr.create_StmtExpr(RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("w"), _1_y), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return")))));
      RASTCoverage.__default.TestNoOptimize(_0_x);
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(_0_x, _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_Match(_0_x, Dafny.Sequence<RAST._IMatchCase>.FromElements()), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_StructBuild(_0_x, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements()), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements()), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat()), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&"), _0_x, _0_x, DAST.Format.BinaryOpFormat.create_NoFormat()), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_TypeAscription(_0_x, RAST.Type.create_I128()), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1")), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("2"), true, false), _0_x));
      RASTCoverage.__default.TestNoOptimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("3"), false, true), _0_x));
      RASTCoverage.__default.AssertCoverage(object.Equals(RASTCoverage.__default.Optimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_None()), RAST.Expr.create_StmtExpr(RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"), _1_y), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"))))), RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1_y)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return")))));
      Dafny.ISequence<RAST._IExpr> _2_coverageExpression;
      _2_coverageExpression = Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))))), RAST.Expr.create_StmtExpr(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a"))), RAST.Expr.create_Block(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"))), RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dummy")), Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("foo"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bar"))))), RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dummy")), Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("foo"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bar"))), RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("foo2"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bar"))))), RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")))), RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), DAST.Format.UnaryOpFormat.create_NoFormat()), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("y")), DAST.Format.BinaryOpFormat.create_NoFormat()), RAST.Expr.create_TypeAscription(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), RAST.Type.create_I128()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("322")), RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), true, false), RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), false, true), RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_None()), RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")))), RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))), RAST.Expr.create_IfExpr(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))), RAST.Expr.create_For(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))), RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))), RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()), RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("l"))), RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()), RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("l"))), RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None()), RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")))), RAST.Expr.create_Call(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_Call(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("y")))), RAST.Expr.create_CallType(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_I128(), RAST.Type.create_U32())), RAST.Expr.create_Select(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc")), RAST.Expr.create_ExprFromPath(RAST.Path.create_PMemberSelect(RAST.Path.create_Crate(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"))), RAST.Expr.create_ExprFromPath(RAST.Path.create_PMemberSelect(RAST.Path.create_Global(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"))));
      BigInteger _hi0 = new BigInteger((_2_coverageExpression).Count);
      for (BigInteger _3_i = BigInteger.Zero; _3_i < _hi0; _3_i++) {
        RAST._IExpr _4_c;
        _4_c = (_2_coverageExpression).Select(_3_i);
        RAST._IPrintingInfo _5___v0;
        _5___v0 = (_4_c).printingInfo;
        RAST._IExpr _6___v1;
        _6___v1 = RASTCoverage.__default.Optimize(_4_c);
        Dafny.IMap<RAST._IExpr,Dafny.ISequence<Dafny.Rune>> _7___v2;
        _7___v2 = Dafny.Map<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>(_4_c, (_4_c)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
        RAST._IExpr _8___v3;
        _8___v3 = RASTCoverage.__default.Optimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_None()), _4_c));
        RAST._IExpr _9___v4;
        _9___v4 = RASTCoverage.__default.Optimize(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128()), Std.Wrappers.Option<RAST._IExpr>.create_None()), RAST.Expr.create_StmtExpr(RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), _4_c), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
        RAST._IExpr _10___v5;
        _10___v5 = RASTCoverage.__default.Optimize(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _4_c, DAST.Format.UnaryOpFormat.create_NoFormat()));
        RAST._IExpr _11___v6;
        _11___v6 = RASTCoverage.__default.Optimize(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _4_c, DAST.Format.UnaryOpFormat.create_NoFormat()));
        RAST._IExpr _12___v7;
        _12___v7 = RASTCoverage.__default.Optimize(RASTCoverage.__default.ConversionNum(RAST.Type.create_U8(), _4_c));
        RAST._IExpr _13___v8;
        _13___v8 = RASTCoverage.__default.Optimize(RASTCoverage.__default.ConversionNum(RAST.Type.create_U8(), RAST.Expr.create_Call(_4_c, Dafny.Sequence<RAST._IExpr>.FromElements())));
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _14___v9;
        _14___v9 = (_4_c).RightMostIdentifier();
      }
    }
    public static void TestPrintingInfo()
    {
      RAST._IExpr _0_x;
      _0_x = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"));
      RAST._IExpr _1_y;
      _1_y = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("y"));
      DAST.Format._IBinaryOpFormat _2_bnf;
      _2_bnf = DAST.Format.BinaryOpFormat.create_NoFormat();
      RASTCoverage.__default.AssertCoverage(((RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))).printingInfo).is_UnknownPrecedence);
      RASTCoverage.__default.AssertCoverage(object.Equals((_0_x).printingInfo, RAST.PrintingInfo.create_Precedence(BigInteger.One)));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("3"))).printingInfo, RAST.PrintingInfo.create_Precedence(BigInteger.One)));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abc"), true, false)).printingInfo, RAST.PrintingInfo.create_Precedence(BigInteger.One)));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat())).printingInfo, RAST.PrintingInfo.create_SuffixPrecedence(new BigInteger(5))));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat())).printingInfo, RAST.PrintingInfo.create_Precedence(new BigInteger(6))));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat())).printingInfo, RAST.PrintingInfo.create_Precedence(new BigInteger(6))));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat())).printingInfo, RAST.PrintingInfo.create_Precedence(new BigInteger(6))));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat())).printingInfo, RAST.PrintingInfo.create_Precedence(new BigInteger(6))));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat())).printingInfo, RAST.PrintingInfo.create_Precedence(new BigInteger(6))));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!!"), _0_x, DAST.Format.UnaryOpFormat.create_NoFormat())).printingInfo, RAST.PrintingInfo.create_UnknownPrecedence()));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_Select(_0_x, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("name"))).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_ExprFromPath(RAST.Path.create_PMemberSelect(RAST.Path.create_Global(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("name")))).printingInfo, RAST.PrintingInfo.create_Precedence(new BigInteger(2))));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_Call(_0_x, Dafny.Sequence<RAST._IExpr>.FromElements())).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_TypeAscription(_0_x, RAST.Type.create_I128())).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(10), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(30), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(30), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(40), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(40), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(50), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(60), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(70), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(90), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(100), RAST.Associativity.create_LeftToRight())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".."), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>="), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?!?"), _0_x, _1_y, _2_bnf)).printingInfo, RAST.PrintingInfo.create_PrecedenceAssociativity(BigInteger.Zero, RAST.Associativity.create_RequiresParentheses())));
      RASTCoverage.__default.AssertCoverage(object.Equals((RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())).printingInfo, RAST.PrintingInfo.create_UnknownPrecedence()));
    }
    public static void TestNoExtraSemicolonAfter()
    {
      RASTCoverage.__default.AssertCoverage((RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))).NoExtraSemicolonAfter());
      RASTCoverage.__default.AssertCoverage(!((RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a"))).NoExtraSemicolonAfter()));
      RASTCoverage.__default.AssertCoverage((RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None())).NoExtraSemicolonAfter());
      RASTCoverage.__default.AssertCoverage((RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())).NoExtraSemicolonAfter());
      RASTCoverage.__default.AssertCoverage((RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())).NoExtraSemicolonAfter());
      RASTCoverage.__default.AssertCoverage((RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("y")))).NoExtraSemicolonAfter());
      RASTCoverage.__default.AssertCoverage((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_None())).NoExtraSemicolonAfter());
      RASTCoverage.__default.AssertCoverage(!((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"))).NoExtraSemicolonAfter()));
    }
    public static RAST._IRASTBottomUpReplacer ExprSimp { get {
      return ExpressionOptimization.__default.ExprSimplifier();
    } }
  }
} // end of namespace RASTCoverage