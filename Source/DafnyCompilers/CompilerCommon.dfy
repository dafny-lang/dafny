include "CSharpDafnyASTModel.dfy"
include "CSharpInterop.dfy"
include "CSharpDafnyInterop.dfy"
include "Library.dfy"
include "StrTree.dfy"

module {:extern "DafnyInDafny.Common"} DafnyCompilerCommon {
  import System
  import CSharpDafnyASTModel
  import opened CSharpInterop
  import opened CSharpDafnyInterop
  import opened Microsoft.Dafny
  import StrTree

  module AST {
    import Lib.Math
    import Lib.Seq
    import opened Microsoft
    import C = CSharpDafnyASTModel

    module Type {
      import C = CSharpDafnyASTModel

      type Path = seq<string>

      datatype ClassType = ClassType(className: Path, typeArgs: seq<Type>)

      datatype Type =
        | Unit
        | Bool
        | Char
        | Int
        | Nat
        | Real
        | BigOrdinal
        | BitVector(width: int)
        | Collection(finite: bool, kind: CollectionKind, eltType: Type)
        | Unsupported(ty: C.Type)
        | Class(classType: ClassType)

      datatype CollectionKind =
        | Map(keyType: Type)
        | Multiset
        | Seq
        | Set
    }

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

    module Expr {
      import Lib.Math
      import Lib.Seq

      import Type
      import UnaryOp
      import BinaryOp
      import C = CSharpDafnyASTModel

      // public class LiteralExpr : Expression
      datatype Literal =
        | LitBool(b: bool)
        | LitInt(i: int)
        | LitReal(r: real)
        | LitChar(c: string) // FIXME should this use a char?
        | LitString(s: string, verbatim: bool)
      {
        function method Depth() : nat { 1 }
      }

      datatype Receiver =
        | StaticReceiver(classType: Type.ClassType)
        | InstanceReceiver(obj: Expr) // TODO: also include ClassType?

      datatype MethodId =
        | Constructor
        | StaticMethod(name: string)
        | InstanceMethod(name: string) // First argument is target object

      datatype BuiltinFunction =
        | Display(ty: Type.Type)
        | Print

      datatype ApplyOp =
        | UnaryOp(uop: UnaryOp.Op)
        | BinaryOp(bop: BinaryOp.Op)
        | DataConstructor(name: Type.Path, typeArgs: seq<Type.Type>)
        | MethodCall(classType: Type.ClassType, receiver: MethodId, typeArgs: seq<Type.Type>)
        | FunctionCall // First argument is function
        | Builtin(fn: BuiltinFunction)

      datatype Expr =
        // Expressions
        | Literal(lit: Literal)
        | Apply(aop: ApplyOp, args: seq<Expr>)
        | Invalid(msg: string)
        | UnsupportedExpr(expr: C.Expression)
        // Statements
        | Block(stmts: seq<Expr>)
        | If(cond: Expr, thn: Expr, els: Expr)
        | UnsupportedStmt(stmt: C.Statement)
      {
        function method Depth() : nat {
          1 + match this { // FIXME IDE rejects this, command line accepts it
            // Expressions
            case Literal(lit: Literal) =>
              0
            case Apply(_, args) =>
              Seq.MaxF(var f := (e: Expr) requires e in args => e.Depth(); f, args, 0)
            case UnsupportedExpr(expr: C.Expression) =>
              0
            case Invalid(msg: string) =>
              0
            // Statements
            case Block(stmts) =>
              Seq.MaxF(var f := (e: Expr) requires e in stmts => e.Depth(); f, stmts, 0)
            case If(cond, thn, els) =>
              Math.Max(cond.Depth(), Math.Max(thn.Depth(), els.Depth()))
            case UnsupportedStmt(expr: C.Statement) =>
              0
          }
        }

      }

      function method WellFormed(e: Expr): bool {
        match e {
          case Apply(UnaryOp(_), es) => |es| == 1
          case Apply(BinaryOp(_), es) => |es| == 2
          case _ => true
        }
      }

      type t = Expr
    }

    datatype Method = Method(CompileName: string, methodBody: Expr.t) {
      function method Depth() : nat {
        1 + match this {
          case Method(CompileName, methodBody) => methodBody.Depth()
        }
      }
    }

    datatype Program = Program(mainMethod: Method) {
      function method Depth() : nat {
        1 + match this {
          case Program(mainMethod) =>
            mainMethod.Depth()
        }
      }
    }
  }

  module Translator {
    import opened Lib
    import opened CSharpInterop
    import opened CSharpInterop.System
    import opened CSharpDafnyInterop
    import opened CSharpDafnyInterop.Microsoft
    import C = CSharpDafnyASTModel
    import D = AST
    import P = Predicates.Deep

    function method TranslateType(ty: C.Type): D.Type.Type
      reads *
      decreases TypeHeight(ty)
    {
      if ty is C.BoolType then
        D.Type.Bool
      else if ty is C.CharType then
        D.Type.Char
      else if ty is C.IntType then
        D.Type.Int
      else if ty is C.RealType then
        D.Type.Real
      else if ty is C.BigOrdinalType then
        D.Type.BigOrdinal
      else if ty is C.BitvectorType then
        var bvTy := ty as C.BitvectorType;
        D.Type.BitVector(bvTy.Width as int)
      // TODO: the following could be simplified
      else if ty is C.MapType then
        var mTy := ty as C.MapType;
        assume TypeHeight(mTy.Domain) < TypeHeight(mTy);
        assume TypeHeight(mTy.Range) < TypeHeight(mTy);
        var domainTy := TranslateType(mTy.Domain);
        var rangeTy := TranslateType(mTy.Range);
        D.Type.Collection(mTy.Finite, D.Type.CollectionKind.Map(domainTy), rangeTy)
      else if ty is C.SetType then
        var mTy := ty as C.SetType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        D.Type.Collection(mTy.Finite, D.Type.CollectionKind.Set, eltTy)
      else if ty is C.MultiSetType then
        var mTy := ty as C.MultiSetType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        D.Type.Collection(true, D.Type.CollectionKind.Multiset, eltTy)
      else if ty is C.SeqType then
        var mTy := ty as C.SeqType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        D.Type.Collection(true, D.Type.CollectionKind.Seq, eltTy)
      else D.Type.Unsupported(ty)
    }

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

    function method TranslateUnary(u: C.UnaryExpr) : (e: D.Expr.t)
      decreases ASTHeight(u), 0
      reads *
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      if u is C.UnaryOpExpr then
        var u := u as C.UnaryOpExpr;
        var op, e := u.Op, u.E;
        assume op in UnaryOpCodeMap.Keys; // FIXME expect
        D.Expr.t.Apply(D.Expr.ApplyOp.UnaryOp(UnaryOpCodeMap[op]), [TranslateExpression(e)])
      else
        D.Expr.UnsupportedExpr(u)
    }

    function {:axiom} ASTHeight(c: C.Expression) : nat
    function {:axiom} StmtHeight(t: C.Statement) : nat
    function {:axiom} TypeHeight(t: C.Type) : nat

    function method TranslateBinary(b: C.BinaryExpr) : (e: D.Expr.t)
      decreases ASTHeight(b), 0
      reads *
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      var op, e0, e1 := b.ResolvedOp, b.E0, b.E1;
      // LATER b.AccumulatesForTailRecursion
      assume op in BinaryOpCodeMap.Keys; // FIXME expect
      assume ASTHeight(e0) < ASTHeight(b);
      assume ASTHeight(e1) < ASTHeight(b);
      D.Expr.Apply(D.Expr.ApplyOp.BinaryOp(BinaryOpCodeMap[op]), [TranslateExpression(e0), TranslateExpression(e1)])
    }

    function method TranslateLiteral(l: C.LiteralExpr): (e: D.Expr.t)
      reads *
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      if l.Value is Boolean then
        D.Expr.Literal(D.Expr.LitBool(TypeConv.AsBool(l.Value)))
      else if l.Value is Numerics.BigInteger then
        D.Expr.Literal(D.Expr.LitInt(TypeConv.AsInt(l.Value)))
      else if l.Value is BaseTypes.BigDec then
        D.Expr.Literal(D.Expr.LitReal(TypeConv.AsReal(l.Value))) // TODO test
      else if l.Value is String then
        var str := TypeConv.AsString(l.Value);
        if l is C.CharLiteralExpr then
          D.Expr.Literal(D.Expr.LitChar(str))
        else if l is C.StringLiteralExpr then
          var sl := l as C.StringLiteralExpr;
          D.Expr.Literal(D.Expr.LitString(str, sl.IsVerbatim))
        else
          D.Expr.Invalid("LiteralExpr with .Value of type string must be a char or a string.")
      else D.Expr.UnsupportedExpr(l)
    }

    function method TranslateFunctionCall(fce: C.FunctionCallExpr): (e: D.Expr.t)
      reads *
      decreases ASTHeight(fce), 0
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      assume ASTHeight(fce.Receiver) < ASTHeight(fce);
      var fnExpr := TranslateExpression(fce.Receiver);
      var argsC := ListUtils.ToSeq(fce.Args);
      var argExprs := Seq.Map((e requires e in argsC reads * =>
        assume ASTHeight(e) < ASTHeight(fce); TranslateExpression(e)), argsC);
      D.Expr.Apply(D.Expr.ApplyOp.FunctionCall, [fnExpr] + argExprs)
    }

    function method TranslateDatatypeValue(dtv: C.DatatypeValue): (e: D.Expr.t)
      reads *
      decreases ASTHeight(dtv), 0
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      var ctor := dtv.Ctor;
      var n := TypeConv.AsString(ctor.Name);
      var typeArgsC := ListUtils.ToSeq(dtv.InferredTypeArgs);
      var typeArgs := Seq.Map((t requires t in typeArgsC reads * =>
        TranslateType(t)), typeArgsC);
      // TODO: also include formals in the following, and filter out ghost arguments
      var argsC := ListUtils.ToSeq(dtv.Arguments);
      var argExprs := Seq.Map((e requires e in argsC reads * =>
        assume ASTHeight(e) < ASTHeight(dtv); TranslateExpression(e)), argsC);
      D.Expr.Apply(D.Expr.DataConstructor([n], typeArgs), argExprs) // TODO: proper path
    }

    function method TranslateDisplayExpr(de: C.DisplayExpression): (e: D.Expr.t)
      reads *
      decreases ASTHeight(de), 0
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      var elSeq := ListUtils.ToSeq(de.Elements);
      var exprs := Seq.Map((e requires e in elSeq reads * =>
        assume ASTHeight(e) < ASTHeight(de); TranslateExpression(e)), elSeq);
      var ty := TranslateType(de.Type);
      D.Expr.Apply(D.Expr.ApplyOp.Builtin(D.Expr.Display(ty)), exprs)
    }

    function method TranslateExpressionPair(mde: C.MapDisplayExpr, ep: C.ExpressionPair): (e: D.Expr.t)
      reads *
      requires Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde)
      decreases ASTHeight(mde), 0
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      var tyA := TranslateType(ep.A.Type);
      // TODO: This isn't really a sequence of type tyA! It should really construct pairs
      var ty := D.Type.Collection(true, D.Type.CollectionKind.Seq, tyA);
      D.Expr.Apply(D.Expr.ApplyOp.Builtin(D.Expr.Display(ty)), [TranslateExpression(ep.A), TranslateExpression(ep.B)])
    }

    function method TranslateMapDisplayExpr(mde: C.MapDisplayExpr): (e: D.Expr.t)
      reads *
      decreases ASTHeight(mde), 1
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      var elSeq := ListUtils.ToSeq(mde.Elements);
      var exprs := Seq.Map((ep: C.ExpressionPair) reads * =>
        assume Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde);
        TranslateExpressionPair(mde, ep), elSeq);
      var ty := TranslateType(mde.Type);
      D.Expr.Apply(D.Expr.ApplyOp.Builtin(D.Expr.Display(ty)), exprs)
    }

    function method TranslateExpression(c: C.Expression) : (e: D.Expr.t)
      reads *
      decreases ASTHeight(c), 2
      ensures P.All_Expr(e, D.Expr.WellFormed)
    {
      if c is C.BinaryExpr then
        TranslateBinary(c as C.BinaryExpr)
      else if c is C.LiteralExpr then
        TranslateLiteral(c as C.LiteralExpr)
      else if c is C.FunctionCallExpr then
        TranslateFunctionCall(c as C.FunctionCallExpr)
      else if c is C.DatatypeValue then
        TranslateDatatypeValue(c as C.DatatypeValue)
      else if c is C.MapDisplayExpr then
        TranslateMapDisplayExpr(c as C.MapDisplayExpr)
      else if c is C.DisplayExpression then
        TranslateDisplayExpr(c as C.DisplayExpression)
      else D.Expr.UnsupportedExpr(c)
    }

    function method TranslateStatement(s: C.Statement) : D.Expr.t
      reads *
      decreases StmtHeight(s)
    {
      if s is C.PrintStmt then
        var p := s as C.PrintStmt;
        D.Expr.Apply(D.Expr.ApplyOp.Builtin(D.Expr.Print), Seq.Map(TranslateExpression, ListUtils.ToSeq(p.Args)))
      else if s is C.BlockStmt then
        var b := s as C.BlockStmt;
        var stmts := ListUtils.ToSeq(b.Body);
        var stmts' := Seq.Map(s' requires s' in stmts reads * =>
          assume StmtHeight(s') < StmtHeight(s); TranslateStatement(s'), stmts);
        D.Expr.Block(stmts')
      else if s is C.IfStmt then
        var i := s as C.IfStmt;
        // TODO: look at i.IsBindingGuard
        assume ASTHeight(i.Guard) < StmtHeight(i);
        assume StmtHeight(i.Thn) < StmtHeight(i);
        assume StmtHeight(i.Els) < StmtHeight(i);
        var cond := TranslateExpression(i.Guard);
        var thn := TranslateStatement(i.Thn);
        var els := TranslateStatement(i.Els);
        D.Expr.If(cond, thn, els)
      else D.Expr.UnsupportedStmt(s)
    }

    function method TranslateMethod(m: C.Method) : D.Method reads * {
      // var compileName := m.CompileName;
      // FIXME “Main”
      D.Method("Main", D.Expr.Block(Seq.Map(TranslateStatement, ListUtils.ToSeq(m.Body.Body))))
    }

    function method TranslateProgram(p: C.Program) : D.Program reads * {
      D.Program(TranslateMethod(p.MainMethod))
    }
  }

  module Predicates {
    function IsMap<T(!new), T'>(f: T --> T') : T' -> bool {
      y => exists x | f.requires(x) :: y == f(x)
    }

    lemma Map_All_IsMap<A, B>(f: A --> B, xs: seq<A>)
      requires forall a | a in xs :: f.requires(a)
      ensures Seq.All(IsMap(f), Seq.Map(f, xs))
    {}

    lemma Map_All_PC<A, B>(f: A --> B, P: B -> bool, xs: seq<A>)
      requires forall a | a in xs :: f.requires(a)
      requires forall a | a in xs :: P(f(a))
      ensures Seq.All(P, Seq.Map(f, xs))
    {}

    function method {:opaque} MapWithPC<T, Q>(f: T ~> Q, ghost PC: Q -> bool, ts: seq<T>) : (qs: seq<Q>)
      reads f.reads // FIXME: what does this mean?
      requires forall t | t in ts :: f.requires(t)
      requires forall t | t in ts :: PC(f(t))
      ensures |qs| == |ts|
      ensures forall i | 0 <= i < |ts| :: qs[i] == f(ts[i])
      ensures forall q | q in qs :: PC(q)
      ensures Seq.All(PC, qs)
    {
      Seq.Map(f, ts)
    }

    datatype Transformer'<!A, !B> =
      TR(f: A -> B, ghost PC: B -> bool)

    predicate HasValidPC<A(!new), B>(tr: Transformer'<A, B>) {
      forall a: A :: tr.PC(tr.f(a))
    }

    type Transformer<!A(!new), !B(0)> = tr: Transformer'<A, B> | HasValidPC(tr)
      witness *

    type ExprTransformer = Transformer<Expr.t, Expr.t>

    lemma Map_All_TR<A(!new), B(00)>(tr: Transformer<A, B>, ts: seq<A>)
      ensures Seq.All(tr.PC, Seq.Map(tr.f, ts))
    {}

    module Shallow {
      import opened Lib
      import opened AST

      function method All_Method(m: Method, P: Expr.t -> bool) : bool {
        match m {
          case Method(CompileName_, methodBody) => P(methodBody)
        }
      }

      function method All_Program(p: Program, P: Expr.t -> bool) : bool {
        match p {
          case Program(mainMethod) => All_Method(mainMethod, P)
        }
      }

      function method All(p: Program, P: Expr.t -> bool) : bool {
        All_Program(p, P)
      }
    }

    module Deep {
      import opened Lib
      import opened AST
      import Shallow

      function method AllChildren_Expr(e: Expr.t, P: Expr.t -> bool) : bool
        decreases e, 0
      {
        match e {
          // Exprs
          case Literal(lit: Expr.Literal) => true
          case Apply(_, exprs) =>
            Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
          case Invalid(msg: string) => true
          case UnsupportedExpr(expr: C.Expression) => true

          // Statements
          case Block(exprs) => Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
          case If(cond, thn, els) =>
            All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
          case UnsupportedStmt(_) => true
        }
      }

      // FIXME rewrite in terms Expr_Children below
      function method All_Expr(e: Expr.t, P: Expr.t -> bool) : bool {
        && P(e)
        && AllChildren_Expr(e, P)
      }

      function method All_Method(m: Method, P: Expr.t -> bool) : bool {
        Shallow.All_Method(m, e => All_Expr(e, P))
      }

      function method All_Program(p: Program, P: Expr.t -> bool) : bool {
        Shallow.All_Program(p, e => All_Expr(e, P))
      }
    }

    import opened AST

    lemma Shallow_Deep(p: Program, P: Expr.t -> bool)
      requires Shallow.All_Program(p, (e => Deep.All_Expr(e, P)))
      ensures Deep.All_Program(p, P)
    {}

    lemma AllImpliesChildren(e: Expr.t, p: Expr.t -> bool)
      requires Deep.All_Expr(e, p)
      ensures Deep.AllChildren_Expr(e, p)
    {}

  }

  module Rewriter {
    import Lib
    import opened AST
    import opened StrTree
    import opened Lib.Datatypes
    import opened CSharpInterop

    module Shallow {
      import opened Lib
      import opened AST
      import opened Predicates

      // LATER: Explain why this can't be defined: putting `f` on the outside risks breaking the invariant for subterms, and putting f on the inside breaks termination.
      // function method Map_Expr(e: Expr.t, f: Expr.t -> Expr.t) : (e': Expr.t)
      //   ensures Deep.All_Expr(e', tr.PC)
      // {
      //   var e := f(e);
      //   f(match e {
      //       case UnaryOp(uop, e) =>
      //         // Not using datatype update to ensure that I get a warning if a type gets new arguments
      //         Expr.UnaryOp(uop, Map_Expr(e, f))
      //       case Binary(bop, e0, e1) =>
      //         Expr.Binary(bop, Map_Expr(e0, f), Map_Expr(e1, f))
      //       case Literal(lit_) => e
      //       case Invalid(msg_) => e
      //       case UnsupportedExpr(cexpr_) => e
      //   })
      // }

      function method {:opaque} Map_Method(m: Method, tr: ExprTransformer) : (m': Method)
        ensures Shallow.All_Method(m', tr.PC) // FIXME Deep
      {
        match m {
          case Method(CompileName, methodBody) =>
            Method(CompileName, tr.f(methodBody))
        }
      }

      function method {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
        ensures Shallow.All_Program(p', tr.PC)
      {
        match p {
          case Program(mainMethod) => Program(Map_Method(mainMethod, tr))
        }
      }
    }

    module BottomUp {
      import opened AST
      import opened Lib
      import opened Predicates
      import Shallow

      predicate IsBottomUpTransformer(f: Expr.t -> Expr.t, PC: Expr.t -> bool) {
        forall e | Deep.AllChildren_Expr(e, PC) :: Deep.All_Expr(f(e), PC)
      }

      type BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.PC)
        witness TR(d => d, _ => true)

      function method MapChildren_Expr(e: Expr.t, tr: BottomUpTransformer) : (e': Expr.t)
        decreases e, 0
        ensures Deep.AllChildren_Expr(e', tr.PC)
      {
        // Introducing `Deep.AllChildren_Expr(e, tr.PC)` as a term to unblock
        // the proof in the `⇒ e` case.
        ghost var children := Deep.AllChildren_Expr(e, tr.PC);
        // Not using datatype updates below to ensure that we get a warning if a
        // type gets new arguments
        match e {
          // Expressions
          case Literal(lit_) => e
          case Apply(aop, exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Predicates.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            Expr.Apply(aop, exprs')
          case Invalid(msg_) => e
          case UnsupportedExpr(cexpr_) => e

          // Statements
          case Block(exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Predicates.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            Expr.Block(exprs')
          case If(cond, thn, els) =>
            Expr.If(Map_Expr(cond, tr), Map_Expr(thn, tr), Map_Expr(els, tr))
          case UnsupportedStmt(_) =>
            e
        }
      }

      function method Map_Expr(e: Expr.t, tr: BottomUpTransformer) : (e': Expr.t)
        decreases e, 1
        ensures Deep.All_Expr(e', tr.PC)
      {
        tr.f(MapChildren_Expr(e, tr))
      }

      function method Map_Expr_Transformer(tr: BottomUpTransformer) : (tr': ExprTransformer)
      {
        TR(e => Map_Expr(e, tr), e' => Deep.All_Expr(e', tr.PC))
      }

      function method {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) : (m': Method)
        ensures Deep.All_Method(m', tr.PC)
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      function method {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) : (p': Program)
        ensures Deep.All_Program(p', tr.PC)
      {
        Shallow.Map_Program(p, Map_Expr_Transformer(tr))
      }
    }
  }

  module Simplifier {
    import Lib
    import opened AST
    import opened Lib.Datatypes
    import opened Rewriter.BottomUp

    import opened Predicates

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

    predicate method IsNegatedBinopExpr(e: Expr.t) {
      match e {
        case Apply(BinaryOp(op), _) => IsNegatedBinop(op)
        case _ => false
      }
    }

    predicate NotANegatedBinopExpr(e: Expr.t) {
      !IsNegatedBinopExpr(e)
    }

    // function method EliminateNegatedBinops_Expr1(e: Expr.t) : (e': Expr.t)
    //   ensures NotANegatedBinopExpr(e')
    // {
    //   match e {
    //     case Binary(bop, e0, e1) =>
    //       if IsNegatedBinop(bop) then
    //         Expr.UnaryOp(UnaryOp.Not, Expr.Binary(FlipNegatedBinop(bop), e0, e1))
    //       else
    //         Expr.Binary(bop, e0, e1)
    //     case _ => e
    //   }
    // }

    // FIXME Add `require Deep.AllChildren_Expr(e, NotANegatedBinopExpr)`
    function method EliminateNegatedBinops_Expr1(e: Expr.t) : (e': Expr.t)
      ensures NotANegatedBinopExpr(e')
    {
      match e {
        case Apply(BinaryOp(op), es) =>
          if IsNegatedBinop(op) then
            Expr.t.Apply(Expr.ApplyOp.UnaryOp(UnaryOp.Not), [Expr.Apply(Expr.ApplyOp.BinaryOp(FlipNegatedBinop(op)), es)])
          else
            e
        case _ => e
      }
    }

    lemma EliminateNegatedBinops_Expr'_BU()
      ensures IsBottomUpTransformer(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr)
    {
      var (f, PC) := (EliminateNegatedBinops_Expr1, NotANegatedBinopExpr);
      forall e | Deep.AllChildren_Expr(e, PC) ensures Deep.AllChildren_Expr(f(e), PC) {
        if IsNegatedBinopExpr(e) {
          var e'' := match e {
            case Apply(BinaryOp(op), es) =>
              Expr.Apply(Expr.ApplyOp.BinaryOp(FlipNegatedBinop(op)), es)
          };
          var e' := Expr.t.Apply(Expr.ApplyOp.UnaryOp(UnaryOp.Not), [e'']);
          calc { // FIXME Automate
            Deep.All_Expr(f(e), PC);
            Deep.All_Expr(e', PC);
            PC(e') && Deep.AllChildren_Expr(e', PC);
            true && Deep.AllChildren_Expr(e', PC);
            true && Deep.All_Expr(e'', PC);
            true && PC(e'') && Deep.AllChildren_Expr(e'', PC);
          }
        } else {}
      }
    }

    const EliminateNegatedBinops_Expr : BottomUpTransformer :=
      (EliminateNegatedBinops_Expr'_BU();
       TR(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr))

    function method EliminateNegatedBinops_Expr_direct(e: Expr.t) : (e': Expr.t)
      requires Deep.All_Expr(e, Expr.WellFormed)
      ensures Deep.All_Expr(e', NotANegatedBinopExpr)
      ensures Deep.All_Expr(e', Expr.WellFormed)
    {
      AllImpliesChildren(e, Expr.WellFormed);
      match e {
        // Exprs
        case Apply(BinaryOp(bop), exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          if IsNegatedBinop(bop) then
            var e'' := Expr.Apply(Expr.ApplyOp.BinaryOp(FlipNegatedBinop(bop)), exprs');
            assert Deep.All_Expr(e'', NotANegatedBinopExpr);
            assert Deep.All_Expr(e'', Expr.WellFormed);
            var e' := Expr.t.Apply(Expr.ApplyOp.UnaryOp(UnaryOp.Not), [e'']);
            e'
          else
            Expr.Apply(Expr.ApplyOp.BinaryOp(bop), exprs')
        case Apply(aop, exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Expr.Apply(aop, exprs')
        case Literal(lit_) => e
        case Invalid(msg_) => e
        case UnsupportedExpr(cexpr_) => e

        // Statements
        case Block(exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Expr.Block(exprs')
        case If(cond, thn, els) =>
          Expr.If(EliminateNegatedBinops_Expr_direct(cond),
                  EliminateNegatedBinops_Expr_direct(thn),
                  EliminateNegatedBinops_Expr_direct(els))
        case UnsupportedStmt(_) =>
          e
      }
    }

    function method EliminateNegatedBinops(p: Program) : (p': Program)
      ensures Deep.All_Program(p', NotANegatedBinopExpr)
    {
      var p' := Map_Program(p, EliminateNegatedBinops_Expr);
      // LATER: it actually works even without this call; make more things opaque?
      Predicates.Shallow_Deep(p', NotANegatedBinopExpr);
      p'
    }

    function method Children(e: Expr.t) : (s: seq<Expr.t>)
      ensures forall e' | e' in s :: e'.Depth() < e.Depth()
    {
      match e {
        // Expressions
        case Literal(lit: Expr.Literal) => []
        case Apply(aop, exprs: seq<Expr.t>) => exprs
        case Invalid(msg: string) => []
        case UnsupportedExpr(expr: C.Expression) => []

        // Statements
        case Block(exprs) => exprs
        case If(cond, thn, els) => [cond, thn, els]
        case UnsupportedStmt(_) => []
      }
    }

    lemma All_Expr_weaken(e: Expr.t, P: Expr.t -> bool, Q: Expr.t -> bool)
      requires Deep.All_Expr(e, P)
      requires forall e' :: P(e') ==> Q(e')
      decreases e
      ensures Deep.All_Expr(e, Q)
    { // NEAT
      forall e' | e' in Children(e) { All_Expr_weaken(e', P, Q); }
      // match e {
      //   case UnaryOp(uop: UnaryOp.Op, e': Expr.t) =>
      //     All_Expr_weaken(e', P, Q);
      //   case Binary(bop: BinaryOp.Op, e0: Expr.t, e1: Expr.t) =>
      //     All_Expr_weaken(e0, P, Q); All_Expr_weaken(e1, P, Q);
      //   case Literal(lit: Expr.Literal) =>
      //   case Invalid(msg: string) =>
      //   case UnsupportedExpr(expr: C.Expression) =>

      //   // Statements
      //   case Block(exprs) =>
      //     forall e | e in exprs { All_Expr_weaken(e, P, Q); }
      //   case Print(exprs) =>
      //     forall e | e in exprs { All_Expr_weaken(e, P, Q); }
      //   case UnsupportedStmt(_) =>
      // }
    }}
}
