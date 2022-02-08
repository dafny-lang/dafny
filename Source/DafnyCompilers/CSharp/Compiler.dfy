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

    module UnaryOp { // FIXME should be resolved ResolvedUnaryOp (see SinglePassCompiler.cs)
      datatype Op =
        | Not
        | Cardinality
        | Fresh
        | Allocated
        | Lit
    }

    // public class LiteralExpr : Expression
    datatype LiteralExpr =
      | LitBool(b: bool)
      | LitInt(i: int)
      | LitReal(r: real)
      | LitChar(c: string) // FIXME should this use a char?
      | LitString(s: string, verbatim: bool)

    datatype Expr =
      | UnaryOpExpr(uop: UnaryOp.Op, e: Expr) // LATER UnaryExpr
      | BinaryExpr(bop: BinaryOp.Op, e0: Expr, e1: Expr)
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

    const UnaryOpCodeMap: map<C.UnaryOpExpr__Opcode, D.UnaryOp.Op> :=
      map[C.UnaryOpExpr__Opcode.Not := D.UnaryOp.Not]
         [C.UnaryOpExpr__Opcode.Cardinality := D.UnaryOp.Cardinality]
         [C.UnaryOpExpr__Opcode.Fresh := D.UnaryOp.Fresh]
         [C.UnaryOpExpr__Opcode.Allocated := D.UnaryOp.Allocated]
         [C.UnaryOpExpr__Opcode.Lit := D.UnaryOp.Lit]

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

    function method {:verify false} TranslateUnary(u: C.UnaryExpr) : D.Expr {
      if u is C.UnaryOpExpr then
        var u := u as C.UnaryOpExpr;
        var op, e := u.Op, u.E;
        assume op in UnaryOpCodeMap.Keys; // FIXME expect
        D.UnaryOpExpr(UnaryOpCodeMap[op], TranslateExpression(e))
      else
        D.UnsupportedExpr(u)
    }

    function ASTHeight(c: C.Expression) : nat

    function method TranslateBinary(b: C.BinaryExpr) : D.Expr
      decreases ASTHeight(b), 0
      reads *
    {
      var op, e0, e1 := b.ResolvedOp, b.E0, b.E1;
      // LATER b.AccumulatesForTailRecursion
      assume op in BinaryOpCodeMap.Keys; // FIXME expect
      assume ASTHeight(e0) < ASTHeight(b);
      assume ASTHeight(e1) < ASTHeight(b);
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

    function method TranslateExpression(c: C.Expression) : D.Expr
      reads *
      decreases ASTHeight(c), 1
    {
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


  module Predicates {
    module TopExprs {
      import opened Lib
      import opened AST

      function method TopExprs_Stmt(s: Stmt, P: Expr -> bool) : bool {
        match s {
          case PrintStmt(exprs) =>
            Seq.All(P, exprs)
          case UnsupportedStmt => true
        }
      }

      function method TopExprs_BlockStmt(b: BlockStmt, P: Expr -> bool) : bool {
        Seq.All((s => TopExprs_Stmt(s, P)), b)
      }

      function method TopExprs_Method(m: Method, P: Expr -> bool) : bool {
        match m {
          case Method(CompileName_, methodBody) => TopExprs_BlockStmt(methodBody, P)
        }
      }

      function method TopExprs_Program(p: Program, P: Expr -> bool) : bool {
        match p {
          case Program(mainMethod) => TopExprs_Method(mainMethod, P)
        }
      }

      function method TopExprs(p: Program, P: Expr -> bool) : bool {
        TopExprs_Program(p, P)
      }
    }

    module AllExprs {
      import opened Lib
      import opened AST

      // FIXME rewrite in terms of a generic iterator on expressions
      function method AllExprs_Expr(e: Expr, P: Expr -> bool) : bool {
        && P(e)
        && match e {
            case UnaryOpExpr(uop: UnaryOp.Op, e: Expr) =>
              AllExprs_Expr(e, P)
            case BinaryExpr(bop: BinaryOp.Op, e0: Expr, e1: Expr) =>
              AllExprs_Expr(e0, P) && AllExprs_Expr(e1, P)
            case LiteralExpr(lit: LiteralExpr) => true
            case InvalidExpr(msg: string) => true
            case UnsupportedExpr(expr: C.Expression) => true
          }
      }

      function method AllExprs_Stmt(s: Stmt, P: Expr -> bool) : bool {
        match s {
          case PrintStmt(exprs) =>
            Seq.All((e => AllExprs_Expr(e, P)), exprs)
          case UnsupportedStmt => true
        }
      }

      function method AllExprs_BlockStmt(b: BlockStmt, P: Expr -> bool) : bool {
        Seq.All((s => AllExprs_Stmt(s, P)), b)
      }

      function method AllExprs_Method(m: Method, P: Expr -> bool) : bool {
        match m {
          case Method(CompileName_, methodBody) => AllExprs_BlockStmt(methodBody, P)
        }
      }

      function method AllExprs_Program(p: Program, P: Expr -> bool) : bool {
        match p {
          case Program(mainMethod) => AllExprs_Method(mainMethod, P)
        }
      }

      function method AllExprs(p: Program, P: Expr -> bool) : bool {
        AllExprs_Program(p, P)
      }
    }

    import opened AST

    lemma TopExprs_AllExprs(p: Program, P: Expr -> bool)
      requires TopExprs.TopExprs_Program(p, (e => AllExprs.AllExprs_Expr(e, P)))
      ensures AllExprs.AllExprs_Program(p, P)
    {}
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
      import opened Predicates.TopExprs

      function IsMap<T(!new), T'>(f: T -> T') : T' -> bool {
        y => exists x :: y == f(x)
      }

      // LATER: Explain why this can't be defined: putting `f` on the outside risks breaking the invariant for subterms, and putting f on the inside breaks termination.
      // function method MapExprs_Expr(e: Expr, f: Expr -> Expr) : (e': Expr)
      //   ensures AllExprs_Expr(e', IsMap(f))
      // {
      //   var e := f(e);
      //   match e {
      //       case UnaryOpExpr(uop, e) =>
      //         // Not using datatype update to ensure that I get a warning if a type gets new arguments
      //         UnaryOpExpr(uop, MapExprs_Expr(e, f))
      //       case BinaryExpr(bop, e0, e1) =>
      //         BinaryExpr(bop, MapExprs_Expr(e0, f), MapExprs_Expr(e1, f))
      //       case LiteralExpr(lit_) => e
      //       case InvalidExpr(msg_) => e
      //       case UnsupportedExpr(cexpr_) => e
      //   }
      // }

      function method {:opaque} {:verify false} MapExprs_Stmt(s: Stmt, f: Expr -> Expr) : (s': Stmt)
        ensures TopExprs_Stmt(s', IsMap(f))
      {
        match s {
          case PrintStmt(exprs) =>
            PrintStmt(Seq.Map(f, exprs))
          case UnsupportedStmt => s
        }
      }

      function method {:opaque} {:verify false} MapExprs_BlockStmt(b: BlockStmt, f: Expr -> Expr) : (b': BlockStmt)
        ensures TopExprs_BlockStmt(b', IsMap(f))
      {
        Seq.Map((s => MapExprs_Stmt(s, f)), b)
      }

      function method {:opaque} {:verify false} MapExprs_Method(m: Method, f: Expr -> Expr) : (m': Method)
        ensures TopExprs_Method(m', IsMap(f))
      {
        match m {
          case Method(CompileName, methodBody) =>
            Method(CompileName, MapExprs_BlockStmt(methodBody, f))
        }
      }

      function method {:opaque} {:verify false} MapExprs_Program(p: Program, f: Expr -> Expr) : (p': Program)
        ensures TopExprs_Program(p', IsMap(f))
      {
        match p {
          case Program(mainMethod) => Program(MapExprs_Method(mainMethod, f))
        }
      }
    }
  }

  module Simplifier {
    import Lib
    import opened AST
    import opened Lib.Datatypes
    import opened Rewriter.MapExprs

    import Predicates
    import opened Predicates.AllExprs
    import opened Predicates.TopExprs

    function method FlipNegatedBinop1(op: BinaryOp.Op) : (op': BinaryOp.Op)
    {
      match op {
        case Eq(NeqCommon) => BinaryOp.Eq(BinaryOp.EqCommon)
        case Maps(MapNeq) => BinaryOp.Maps(BinaryOp.MapEq)
        case Maps(NotInMap) => BinaryOp.Maps(BinaryOp.InMap)
        case MultiSets(MultiSetNeq) => BinaryOp.MultiSets(BinaryOp.MultiSetEq)
        case MultiSets(NotInMultiSet) => BinaryOp.MultiSets(BinaryOp.InMultiSet)
        case Sequences(SeqNeq) => BinaryOp.Sequences(BinaryOp.SeqEq)
        case Sets(SetNeq) => BinaryOp.Sets(BinaryOp.SetEq)
        case Sets(NotInSet) => BinaryOp.Sets(BinaryOp.InSet)
        case Sequences(NotInSeq) => BinaryOp.Sequences(BinaryOp.InSeq)
        case _ => op
      }
    }

    function method FlipNegatedBinop(op: BinaryOp.Op) : (op': BinaryOp.Op)
      ensures !IsNegatedBinop(op')
    {
      FlipNegatedBinop1(op)
    }

    predicate method IsNegatedBinop(op: BinaryOp.Op) {
      FlipNegatedBinop1(op) != op
    }

    predicate method IsNegatedBinopExpr(e: Expr) {
      e.BinaryExpr? && IsNegatedBinop(e.bop)
    }

    predicate NotANegatedBinopExpr(e: Expr) {
      !IsNegatedBinopExpr(e)
    }

    function method EliminateNegatedBinops_Expr(e: Expr) : (e': Expr)
      ensures AllExprs_Expr(e', NotANegatedBinopExpr)
    {
      match e {
        case UnaryOpExpr(uop, e) =>
          // Not using datatype update to ensure that I get a warning if a type gets new arguments
          UnaryOpExpr(uop, EliminateNegatedBinops_Expr(e))
        case BinaryExpr(bop, e0, e1) =>
          var e0', e1' := EliminateNegatedBinops_Expr(e0), EliminateNegatedBinops_Expr(e1);
          if IsNegatedBinop(bop) then
            UnaryOpExpr(UnaryOp.Not, BinaryExpr(FlipNegatedBinop(bop), e0', e1'))
          else
            BinaryExpr(bop, e0', e1')
        case LiteralExpr(lit_) => e
        case InvalidExpr(msg_) => e
        case UnsupportedExpr(cexpr_) => e
      }
    }

    function method EliminateNegatedBinops(p: Program) : (p': Program)
      ensures AllExprs_Program(p', NotANegatedBinopExpr)
    {
      var p' := MapExprs_Program(p, EliminateNegatedBinops_Expr);
      // LATER: it actually works even without this call; make more things opaque?
      Predicates.TopExprs_AllExprs(p', NotANegatedBinopExpr);
      p'
    }
  }

  module Compiler {
    import Lib
    import Simplifier
    import opened AST
    import opened Target
    import opened Lib.Datatypes
    import opened CSharpInterop
    import opened CSharpDafnyInterop
    import Predicates
    import opened Predicates.AllExprs

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

    function method CompileUnaryOpExpr(op: UnaryOp.Op, c: StrTree) : StrTree {
      match op {
        case Not => Format("!{}", [c]) // LATER use resolved op, which distinguishes between BV and boolean
        case Cardinality => Unsupported
        case Fresh => Unsupported
        case Allocated => Unsupported
        case Lit => Unsupported
      }
    }

    function method CompileBinaryExpr(op: BinaryOp.Op, c0: StrTree, c1: StrTree) : StrTree
      requires !Simplifier.IsNegatedBinop(op)
    {
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
        case MultiSets(MultiSetUnion) => Unsupported
        case MultiSets(MultiSetIntersection) => Unsupported
        case MultiSets(MultiSetDifference) => Unsupported

        case Sequences(SeqEq) => fmt("{}.Equals({})")
        case Sequences(ProperPrefix) => Unsupported
        case Sequences(Prefix) => Unsupported
        case Sequences(Concat) => Unsupported
        case Sequences(InSeq) => Unsupported

        case Maps(MapEq) => fmt("{}.Equals({})")
        case Maps(MapNeq) => Unsupported
        case Maps(InMap) => rbin("{}.Contains({})")
        case Maps(MapMerge) => Unsupported
        case Maps(MapSubtraction) => Unsupported

        case Datatypes(RankLt) => Unsupported
        case Datatypes(RankGt) => Unsupported
      }
    }

    function method CompileExpr(e: Expr) : StrTree
      requires AllExprs_Expr(e, Simplifier.NotANegatedBinopExpr)
    {
      match e {
        case LiteralExpr(l) =>
          CompileLiteralExpr(l)
        case UnaryOpExpr(op, e) =>
          var c := CompileExpr(e);
          CompileUnaryOpExpr(op, c)
        case BinaryExpr(op, e0, e1) =>
          var c0, c1 := CompileExpr(e0), CompileExpr(e1);
          CompileBinaryExpr(op, c0, c1)
        case InvalidExpr(_) => Unsupported
        case UnsupportedExpr(_) => Unsupported
      }
    }

    function method CompilePrint(e: Expr) : StrTree
      requires AllExprs_Expr(e, Simplifier.NotANegatedBinopExpr)
    {
      Seq([Call("DafnyRuntime.Helpers.Print", [CompileExpr(e)]), Str(";")])
    }

    function method CompileStmt(s: Stmt) : StrTree
      requires AllExprs_Stmt(s, Simplifier.NotANegatedBinopExpr)
    {
      match s {
        case PrintStmt(exprs) =>
          Concat("\n", Lib.Seq.Map(CompilePrint, exprs))
        case UnsupportedStmt => Unsupported
      }
    }

    function method CompileMethod(m: Method) : StrTree
      requires AllExprs_Method(m, Simplifier.NotANegatedBinopExpr)
    {
      match m {
        case Method(nm, methodBody) => Concat("\n", Lib.Seq.Map(CompileStmt, methodBody))
      }
    }

    function method CompileProgram(p: Program) : StrTree
      requires AllExprs_Program(p, Simplifier.NotANegatedBinopExpr)
    {
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
      var lowered := Simplifier.EliminateNegatedBinops(translated);
      var compiled := Compiler.CompileProgram(lowered);
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
