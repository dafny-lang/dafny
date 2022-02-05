include "../CSharpDafnyASTModel.dfy"
include "../CSharpInterop.dfy"
include "../CSharpDafnyInterop.dfy"
include "../Library.dfy"

module {:extern "DafnyInDafny.CSharp"} CSharpDafnyCompiler {
  import System
  import CSharpDafnyASTModel
  import opened CSharpInterop
  import opened CSharpDafnyInterop
  import opened Microsoft.Dafny

  module AST {
    import opened Microsoft
    import C = CSharpDafnyASTModel

    datatype Tokd<T> =
      Tokd(tok: Boogie.IToken, val: T)

    module BinaryOp {
      datatype Logical =
        Iff | Imp | And | Or
      datatype Eq =
        EqCommon | NeqCommon
      datatype Numeric =
        Lt | Le | Ge | Gt | Add | Sub | Mul | Div | Mod
      datatype BV =
        LeftShift | RightShift | BitwiseAnd | BitwiseOr | BitwiseXor
      datatype Char =
        LtChar | LeChar | GeChar | GtChar
      datatype Sets =
        SetEq | SetNeq | ProperSubset | Subset | Superset | ProperSuperset |
        Disjoint | InSet | NotInSet | Union | Intersection | SetDifference
      datatype MultiSets =
        MultiSetEq | MultiSetNeq | MultiSubset | MultiSuperset |
        ProperMultiSubset | ProperMultiSuperset | MultiSetDisjoint | InMultiSet |
        NotInMultiSet | MultiSetUnion | MultiSetIntersection | MultiSetDifference
      datatype Sequences =
        SeqEq | SeqNeq | ProperPrefix | Prefix | Concat | InSeq | NotInSeq
      datatype Maps =
        MapEq | MapNeq | InMap | NotInMap | MapMerge | MapSubtraction
      datatype Datatypes =
        RankLt | RankGt
      datatype Op =
        | Logical(oLogical: Logical)
        | Eq(oEq: Eq)
        | Numeric(oNumeric: Numeric)
        | BV(oBV: BV)
        | Char(oChar: Char)
        | Sets(oSets: Sets)
        | MultiSets(oMultiSets: MultiSets)
        | Sequences(oSequences: Sequences)
        | Maps(oMaps: Maps)
        | Datatypes(oDatatypes: Datatypes)
    }

    // public class LiteralExpr : Expression
    datatype LiteralExpr =
      | LitBool(b: bool)
      | LitInt(i: int)
      | LitReal(r: real)
      | LitChar(c: string) // FIXME should this use a char?
      | LitString(s: string, verbatim: bool)

    datatype Expr =
      | BinaryExpr(op: BinaryOp.Op, e0: Expr, e1: Expr)
      | LiteralExpr(lit: LiteralExpr)
      | InvalidExpr(msg: string)
      | UnsupportedExpr(expr: C.Expression)

    datatype Stmt =
      | PrintStmt(exprs: seq<Expr>)
      | UnsupportedStmt

    type BlockStmt = seq<Stmt>

    datatype Method = Method(CompileName: string, methodBody: BlockStmt)

    datatype Program = Program(mainMethod: Method)
  }

  module Translator {
    import opened Lib
    import opened CSharpInterop
    import opened CSharpInterop.System
    import opened CSharpDafnyInterop
    import opened CSharpDafnyInterop.Microsoft
    import C = CSharpDafnyASTModel
    import D = AST

    const BinaryOpCodeMap: map<C.BinaryExpr__ResolvedOpcode, D.BinaryOp.Op> :=
      map[C.BinaryExpr__ResolvedOpcode.Iff := D.BinaryOp.Logical(D.BinaryOp.Iff)]
         [C.BinaryExpr__ResolvedOpcode.Imp := D.BinaryOp.Logical(D.BinaryOp.Imp)]
         [C.BinaryExpr__ResolvedOpcode.And := D.BinaryOp.Logical(D.BinaryOp.And)]
         [C.BinaryExpr__ResolvedOpcode.Or := D.BinaryOp.Logical(D.BinaryOp.Or)]
         [C.BinaryExpr__ResolvedOpcode.EqCommon := D.BinaryOp.Eq(D.BinaryOp.EqCommon)]
         [C.BinaryExpr__ResolvedOpcode.NeqCommon := D.BinaryOp.Eq(D.BinaryOp.NeqCommon)]
         [C.BinaryExpr__ResolvedOpcode.Lt := D.BinaryOp.Numeric(D.BinaryOp.Lt)]
         [C.BinaryExpr__ResolvedOpcode.Le := D.BinaryOp.Numeric(D.BinaryOp.Le)]
         [C.BinaryExpr__ResolvedOpcode.Ge := D.BinaryOp.Numeric(D.BinaryOp.Ge)]
         [C.BinaryExpr__ResolvedOpcode.Gt := D.BinaryOp.Numeric(D.BinaryOp.Gt)]
         [C.BinaryExpr__ResolvedOpcode.Add := D.BinaryOp.Numeric(D.BinaryOp.Add)]
         [C.BinaryExpr__ResolvedOpcode.Sub := D.BinaryOp.Numeric(D.BinaryOp.Sub)]
         [C.BinaryExpr__ResolvedOpcode.Mul := D.BinaryOp.Numeric(D.BinaryOp.Mul)]
         [C.BinaryExpr__ResolvedOpcode.Div := D.BinaryOp.Numeric(D.BinaryOp.Div)]
         [C.BinaryExpr__ResolvedOpcode.Mod := D.BinaryOp.Numeric(D.BinaryOp.Mod)]
         [C.BinaryExpr__ResolvedOpcode.LeftShift := D.BinaryOp.BV(D.BinaryOp.LeftShift)]
         [C.BinaryExpr__ResolvedOpcode.RightShift := D.BinaryOp.BV(D.BinaryOp.RightShift)]
         [C.BinaryExpr__ResolvedOpcode.BitwiseAnd := D.BinaryOp.BV(D.BinaryOp.BitwiseAnd)]
         [C.BinaryExpr__ResolvedOpcode.BitwiseOr := D.BinaryOp.BV(D.BinaryOp.BitwiseOr)]
         [C.BinaryExpr__ResolvedOpcode.BitwiseXor := D.BinaryOp.BV(D.BinaryOp.BitwiseXor)]
         [C.BinaryExpr__ResolvedOpcode.LtChar := D.BinaryOp.Char(D.BinaryOp.LtChar)]
         [C.BinaryExpr__ResolvedOpcode.LeChar := D.BinaryOp.Char(D.BinaryOp.LeChar)]
         [C.BinaryExpr__ResolvedOpcode.GeChar := D.BinaryOp.Char(D.BinaryOp.GeChar)]
         [C.BinaryExpr__ResolvedOpcode.GtChar := D.BinaryOp.Char(D.BinaryOp.GtChar)]
         [C.BinaryExpr__ResolvedOpcode.SetEq := D.BinaryOp.Sets(D.BinaryOp.SetEq)]
         [C.BinaryExpr__ResolvedOpcode.SetNeq := D.BinaryOp.Sets(D.BinaryOp.SetNeq)]
         [C.BinaryExpr__ResolvedOpcode.ProperSubset := D.BinaryOp.Sets(D.BinaryOp.ProperSubset)]
         [C.BinaryExpr__ResolvedOpcode.Subset := D.BinaryOp.Sets(D.BinaryOp.Subset)]
         [C.BinaryExpr__ResolvedOpcode.Superset := D.BinaryOp.Sets(D.BinaryOp.Superset)]
         [C.BinaryExpr__ResolvedOpcode.ProperSuperset := D.BinaryOp.Sets(D.BinaryOp.ProperSuperset)]
         [C.BinaryExpr__ResolvedOpcode.Disjoint := D.BinaryOp.Sets(D.BinaryOp.Disjoint)]
         [C.BinaryExpr__ResolvedOpcode.InSet := D.BinaryOp.Sets(D.BinaryOp.InSet)]
         [C.BinaryExpr__ResolvedOpcode.NotInSet := D.BinaryOp.Sets(D.BinaryOp.NotInSet)]
         [C.BinaryExpr__ResolvedOpcode.Union := D.BinaryOp.Sets(D.BinaryOp.Union)]
         [C.BinaryExpr__ResolvedOpcode.Intersection := D.BinaryOp.Sets(D.BinaryOp.Intersection)]
         [C.BinaryExpr__ResolvedOpcode.SetDifference := D.BinaryOp.Sets(D.BinaryOp.SetDifference)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetEq := D.BinaryOp.MultiSets(D.BinaryOp.MultiSetEq)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetNeq := D.BinaryOp.MultiSets(D.BinaryOp.MultiSetNeq)]
         [C.BinaryExpr__ResolvedOpcode.MultiSubset := D.BinaryOp.MultiSets(D.BinaryOp.MultiSubset)]
         [C.BinaryExpr__ResolvedOpcode.MultiSuperset := D.BinaryOp.MultiSets(D.BinaryOp.MultiSuperset)]
         [C.BinaryExpr__ResolvedOpcode.ProperMultiSubset := D.BinaryOp.MultiSets(D.BinaryOp.ProperMultiSubset)]
         [C.BinaryExpr__ResolvedOpcode.ProperMultiSuperset := D.BinaryOp.MultiSets(D.BinaryOp.ProperMultiSuperset)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetDisjoint := D.BinaryOp.MultiSets(D.BinaryOp.MultiSetDisjoint)]
         [C.BinaryExpr__ResolvedOpcode.InMultiSet := D.BinaryOp.MultiSets(D.BinaryOp.InMultiSet)]
         [C.BinaryExpr__ResolvedOpcode.NotInMultiSet := D.BinaryOp.MultiSets(D.BinaryOp.NotInMultiSet)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetUnion := D.BinaryOp.MultiSets(D.BinaryOp.MultiSetUnion)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetIntersection := D.BinaryOp.MultiSets(D.BinaryOp.MultiSetIntersection)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetDifference := D.BinaryOp.MultiSets(D.BinaryOp.MultiSetDifference)]
         [C.BinaryExpr__ResolvedOpcode.SeqEq := D.BinaryOp.Sequences(D.BinaryOp.SeqEq)]
         [C.BinaryExpr__ResolvedOpcode.SeqNeq := D.BinaryOp.Sequences(D.BinaryOp.SeqNeq)]
         [C.BinaryExpr__ResolvedOpcode.ProperPrefix := D.BinaryOp.Sequences(D.BinaryOp.ProperPrefix)]
         [C.BinaryExpr__ResolvedOpcode.Prefix := D.BinaryOp.Sequences(D.BinaryOp.Prefix)]
         [C.BinaryExpr__ResolvedOpcode.Concat := D.BinaryOp.Sequences(D.BinaryOp.Concat)]
         [C.BinaryExpr__ResolvedOpcode.InSeq := D.BinaryOp.Sequences(D.BinaryOp.InSeq)]
         [C.BinaryExpr__ResolvedOpcode.NotInSeq := D.BinaryOp.Sequences(D.BinaryOp.NotInSeq)]
         [C.BinaryExpr__ResolvedOpcode.MapEq := D.BinaryOp.Maps(D.BinaryOp.MapEq)]
         [C.BinaryExpr__ResolvedOpcode.MapNeq := D.BinaryOp.Maps(D.BinaryOp.MapNeq)]
         [C.BinaryExpr__ResolvedOpcode.InMap := D.BinaryOp.Maps(D.BinaryOp.InMap)]
         [C.BinaryExpr__ResolvedOpcode.NotInMap := D.BinaryOp.Maps(D.BinaryOp.NotInMap)]
         [C.BinaryExpr__ResolvedOpcode.MapMerge := D.BinaryOp.Maps(D.BinaryOp.MapMerge)]
         [C.BinaryExpr__ResolvedOpcode.MapSubtraction := D.BinaryOp.Maps(D.BinaryOp.MapSubtraction)]
         [C.BinaryExpr__ResolvedOpcode.RankLt := D.BinaryOp.Datatypes(D.BinaryOp.RankLt)]
         [C.BinaryExpr__ResolvedOpcode.RankGt := D.BinaryOp.Datatypes(D.BinaryOp.RankGt)];

    function method {:verify false} TranslateBinary(b: C.BinaryExpr) : D.Expr {
      var op, e0, e1 := b.ResolvedOp, b.E0, b.E1;
      // LATER b.AccumulatesForTailRecursion
      assume op in BinaryOpCodeMap.Keys; // FIXME expect
      D.BinaryExpr(BinaryOpCodeMap[op], TranslateExpression(e0), TranslateExpression(e1))
    }

    function method TranslateLiteral(l: C.LiteralExpr): D.Expr reads * {
        if l.Value is Boolean then
          D.LiteralExpr(D.LitBool(TypeConv.AsBool(l.Value)))
        else if l.Value is Numerics.BigInteger then
          D.LiteralExpr(D.LitInt(TypeConv.AsInt(l.Value)))
        else if l.Value is BaseTypes.BigDec then
          D.LiteralExpr(D.LitReal(TypeConv.AsReal(l.Value))) // TODO test
        else if l.Value is String then
          var str := TypeConv.AsString(l.Value);
          if l is C.CharLiteralExpr then
            D.LiteralExpr(D.LitChar(str))
          else if l is C.StringLiteralExpr then
            var sl := l as C.StringLiteralExpr;
            D.LiteralExpr(D.LitString(str, sl.IsVerbatim))
          else
            D.InvalidExpr("LiteralExpr with .Value of type string must be a char or a string.")
        else D.UnsupportedExpr(l)
    }

    function method {:verify false} TranslateExpression(c: C.Expression) : D.Expr reads * {
      if c is C.BinaryExpr then
        TranslateBinary(c as C.BinaryExpr)
      else if c is C.LiteralExpr then
        TranslateLiteral(c as C.LiteralExpr)
      else D.UnsupportedExpr(c)
    }

    function method TranslateStatement(s: C.Statement) : D.Stmt reads * {
      if s is C.PrintStmt then
        var p := s as C.PrintStmt;
        D.PrintStmt(Seq.Map(TranslateExpression, ListUtils.ToSeq(p.Args)))
      else D.UnsupportedStmt
    }

    function method TranslateBlock(b: C.BlockStmt) : D.BlockStmt reads * {
      Seq.Map(TranslateStatement, ListUtils.ToSeq(b.Body))
    }

    function method TranslateMethod(m: C.Method) : D.Method reads * {
      // var compileName := m.CompileName;
      D.Method("Main", TranslateBlock(m.Body)) // FIXME “Main”
    }

    function method TranslateProgram(p: C.Program) : D.Program reads * {
      D.Program(TranslateMethod(p.MainMethod))
    }
  }

  module Target {
    import opened Lib.Datatypes

    datatype StrTree =
      | Str(s: string)
      | SepSeq(sep: Option<string>, asts: seq<StrTree>)
      | Unsupported

    function method Seq(asts: seq<StrTree>) : StrTree {
      SepSeq(None, asts)
    }

    function method Concat(sep: string, asts: seq<StrTree>) : StrTree {
      SepSeq(Some(sep), asts)
    }

    function method Call(fn: string, args: seq<StrTree>) : StrTree {
      Seq([Str(fn), Str("("), Concat(", ", args), Str(")")])
    }

    function method SingleQuote(s: StrTree): StrTree {
      Seq([Str("'"), s, Str("'")])
    }

    function method DoubleQuote(s: StrTree): StrTree {
      Seq([Str("\""), s, Str("\"")])
    }

    function method interleave<T>(t0: seq<T>, t1: seq<T>, pos: int) : seq<T>
      requires 0 <= pos
      requires pos <= |t0| && pos <= |t1|
      decreases |t0| - pos
    {
      if pos >= |t1| then t0[pos..]
      else if pos >= |t0| then t1[pos..]
      else [t0[pos], t1[pos]] + interleave(t0, t1, pos + 1)
    }


    function method splitFormat'(formatString: string, prev: int, pos: int) : (parts: seq<StrTree>)
      requires 0 <= prev <= pos <= |formatString|
      ensures |parts| > 0
      decreases |formatString| - pos
    {
      if pos >= |formatString| - 1 then
        [Str(formatString[prev..])]
      else if formatString[pos] == '{' && formatString[pos + 1] == '}' then
        [Str(formatString[prev..pos])] + splitFormat'(formatString, pos + 2, pos + 2)
      else
        splitFormat'(formatString, prev, pos + 1)
    }

    function method splitFormat(formatString: string) : seq<StrTree> {
      splitFormat'(formatString, 0, 0)
    }

    function method Format(s: string, values: seq<StrTree>): StrTree
      requires |splitFormat(s)| == |values| + 1
    {
      Seq(interleave(splitFormat(s), values, 0))
    }
  }

  module Rewriter {
    import Lib
    import opened AST
    import opened Target
    import opened Lib.Datatypes
    import opened CSharpInterop

    module MapExprs {
      import opened Lib
      import opened AST

      function method MapExprs_Stmt(s: Stmt, f: Expr -> Expr) : Stmt {
        match s {
          case PrintStmt(exprs) =>
            PrintStmt(Seq.Map(f, exprs))
          case UnsupportedStmt => s
        }
      }

      function method MapExprs_BlockStmt(b: BlockStmt, f: Expr -> Expr) : BlockStmt {
        Seq.Map((s => MapExprs_Stmt(s, f)), b)
      }

      function method MapExprs_Method(m: Method, f: Expr -> Expr) : Method {
        match m {
          case Method(CompileName, methodBody) =>
            Method(CompileName, MapExprs_BlockStmt(methodBody, f))
        }
      }

      function method MapExprs_Program(p: Program, f: Expr -> Expr) : Program {
        match p {
          case Program(mainMethod) => Program(MapExprs_Method(mainMethod, f))
        }
      }

      function method MapExprs(p: Program, f: Expr -> Expr) : Program {
        MapExprs_Program(p, f)
      }
    }
  }

  module Compiler {
    import Lib
    import opened AST
    import opened Target
    import opened Lib.Datatypes
    import opened CSharpInterop
    import opened CSharpDafnyInterop

    function method CompileInt(i: int) : StrTree {
      var istr := Lib.Str.of_int(i, 10);
      Call("new BigInteger", [Str(istr)])
    }

    function method CompileLiteralExpr(l: LiteralExpr) : StrTree {
      match l {
        case LitBool(b: bool) => Str(if b then "true" else "false")
        case LitInt(i: int) => CompileInt(i)
        case LitReal(r: real) =>
          var n := TypeConv.Numerator(r);
          var d := TypeConv.Denominator(r);
          Call("new BigRational", [CompileInt(n), CompileInt(d)])
        case LitChar(c: string) => SingleQuote(Str(c))
        case LitString(s: string, verbatim: bool) => DoubleQuote(Str(s)) // FIXME verbatim
      }
    }

    // NEXT: Write a transformation that translates negations into unary op + unnegated binary op, apply it using the expr mapper, then write a predicate on the AST that rules out negated exprs, and finally omit the relevant cases from CompileBinaryExpr below.

    function method CompileBinaryExpr(op: BinaryOp.Op, c0: StrTree, c1: StrTree) : StrTree {
      var fmt := str requires |splitFormat(str)| == 3 =>
        Format(str, [c0, c1]); // Cute use of function precondition
      var bin := str =>
        Format("{} {} {}", [c0, Str(str), c1]);
      var rbin := str =>
        Format("{} {} {}", [c1, Str(str), c0]);
      match op {
        case Logical(Iff) => bin("==")
        case Logical(Imp) => fmt("!{} || {}")
        case Logical(And) => bin("&&")
        case Logical(Or) => bin("||")

        case Eq(EqCommon) => Unsupported
        case Eq(NeqCommon) => Unsupported

        case Numeric(Lt) => bin("<")
        case Numeric(Le) => bin("<=")
        case Numeric(Ge) => bin(">=")
        case Numeric(Gt) => bin(">")
        case Numeric(Add) => Unsupported
        case Numeric(Sub) => Unsupported
        case Numeric(Mul) => Unsupported
        case Numeric(Div) => Unsupported
        case Numeric(Mod) => Unsupported

        case BV(LeftShift) => Unsupported
        case BV(RightShift) => Unsupported
        case BV(BitwiseAnd) => bin("&")
        case BV(BitwiseOr) => bin("|")
        case BV(BitwiseXor) => bin("^")

        case Char(LtChar) => bin("<")
        case Char(LeChar) => bin("<=")
        case Char(GeChar) => bin(">=")
        case Char(GtChar) => bin(">")
        // FIXME: Why is there lt/le/gt/ge for chars but not binops?

        case Sets(SetEq) => fmt("{}.Equals({})")
        case Sets(SetNeq) => Unsupported
        case Sets(ProperSubset) => Unsupported
        case Sets(Subset) => Unsupported
        case Sets(Superset) => Unsupported
        case Sets(ProperSuperset) => Unsupported
        case Sets(Disjoint) => Unsupported
        case Sets(InSet) => rbin("{}.Contains({})")
        case Sets(NotInSet) => Unsupported
        case Sets(Union) => Unsupported
        case Sets(Intersection) => Unsupported
        case Sets(SetDifference) => Unsupported

        case MultiSets(MultiSetEq) => fmt("{}.Equals({})")
        case MultiSets(MultiSetNeq) => Unsupported
        case MultiSets(MultiSubset) => Unsupported
        case MultiSets(MultiSuperset) => Unsupported
        case MultiSets(ProperMultiSubset) => Unsupported
        case MultiSets(ProperMultiSuperset) => Unsupported
        case MultiSets(MultiSetDisjoint) => Unsupported
        case MultiSets(InMultiSet) => rbin("{}.Contains({})")
        case MultiSets(NotInMultiSet) => Unsupported
        case MultiSets(MultiSetUnion) => Unsupported
        case MultiSets(MultiSetIntersection) => Unsupported
        case MultiSets(MultiSetDifference) => Unsupported

        case Sequences(SeqEq) => fmt("{}.Equals({})")
        case Sequences(SeqNeq) => Unsupported
        case Sequences(ProperPrefix) => Unsupported
        case Sequences(Prefix) => Unsupported
        case Sequences(Concat) => Unsupported
        case Sequences(InSeq) => Unsupported
        case Sequences(NotInSeq) => Unsupported

        case Maps(MapEq) => fmt("{}.Equals({})")
        case Maps(MapNeq) => Unsupported
        case Maps(InMap) => rbin("{}.Contains({})")
        case Maps(NotInMap) => Unsupported
        case Maps(MapMerge) => Unsupported
        case Maps(MapSubtraction) => Unsupported

        case Datatypes(RankLt) => Unsupported
        case Datatypes(RankGt) => Unsupported
      }
    }

    function method CompileExpr(s: Expr) : StrTree {
      match s {
        case LiteralExpr(l) =>
          CompileLiteralExpr(l)
        case BinaryExpr(op, e0, e1) =>
          var c0, c1 := CompileExpr(e0), CompileExpr(e1);
          CompileBinaryExpr(op, c0, c1)
        case InvalidExpr(_) => Unsupported
        case UnsupportedExpr(_) => Unsupported
      }
    }

    function method CompilePrint(e: Expr) : StrTree {
      Seq([Call("DafnyRuntime.Helpers.Print", [CompileExpr(e)]), Str(";")])
    }

    function method CompileStmt(s: Stmt) : StrTree {
      match s {
        case PrintStmt(exprs) =>
          Concat("\n", Lib.Seq.Map(CompilePrint, exprs))
        case UnsupportedStmt => Unsupported
      }
    }

    function method CompileMethod(m: Method) : StrTree {
      match m {
        case Method(nm, methodBody) => Concat("\n", Lib.Seq.Map(CompileStmt, methodBody))
      }
    }

    function method CompileProgram(p: Program) : StrTree {
      match p {
        case Program(mainMethod) => CompileMethod(mainMethod)
      }
    }
  }

  method WriteAST(wr: CSharpDafnyInterop.SyntaxTreeAdapter, ast: Target.StrTree) {
    match ast {
      case Str(s) =>
        wr.Write(s);
      case SepSeq(sep, asts) =>
        for i := 0 to |asts| {
          if i != 0 && sep.Some? {
            wr.Write(sep.t);
          }
          WriteAST(wr, asts[i]);
        }
      case Unsupported =>
    }
  }

  class {:extern} DafnyCSharpCompiler {
    constructor() {
    }

    method Compile(dafnyProgram: CSharpDafnyASTModel.Program,
                   wr: ConcreteSyntaxTree) {
      var st := new CSharpDafnyInterop.SyntaxTreeAdapter(wr);
      var translated := Translator.TranslateProgram(dafnyProgram);
      var compiled := Compiler.CompileProgram(translated);
      WriteAST(st, compiled);
    }

    method EmitCallToMain(mainMethod: CSharpDafnyASTModel.Method,
                          baseName: System.String,
                          wr: ConcreteSyntaxTree) {
      // var st := new SyntaxTreeAdapter(wr);
      // var sClass := st.NewBlock("class __CallToMain");
      // var sBody := sClass.NewBlock("public static void Main(string[] args)");
      // sBody.WriteLine("DafnyRuntime.Helpers.WithHaltHandling(_module.Main);");
    }
  }
}
