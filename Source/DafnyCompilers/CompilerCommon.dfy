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

    module Types {
      import C = CSharpDafnyASTModel

      type Path = seq<string>

      datatype ClassType = ClassType(className: Path, typeArgs: seq<Type>)

      datatype CollectionKind =
        | Map(keyType: Type)
        | Multiset
        | Seq
        | Set

      datatype Type =
        | Unit
        | Bool
        | Char
        | Int
        | Nat
        | Real
        | BigOrdinal
        | BitVector(width: nat)
        | Collection(finite: bool, kind: CollectionKind, eltType: Type)
        | Unsupported(ty: C.Type)
        | Class(classType: ClassType)

      type T = Type
    }

    type Type = Types.T

    datatype Tokd<T> =
      Tokd(tok: Boogie.IToken, val: T)

    module BinaryOps {
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
        SetEq | SetNeq | Subset | Superset | ProperSubset | ProperSuperset |
        Disjoint | InSet | NotInSet | Union | Intersection | SetDifference
      datatype MultiSets =
        MultiSetEq | MultiSetNeq | MultiSubset | MultiSuperset |
        ProperMultiSubset | ProperMultiSuperset | MultiSetDisjoint | InMultiSet |
        NotInMultiSet | MultiSetUnion | MultiSetIntersection | MultiSetDifference
      datatype Sequences =
        SeqEq | SeqNeq | Prefix | ProperPrefix | Concat | InSeq | NotInSeq
      datatype Maps =
        MapEq | MapNeq | InMap | NotInMap | MapMerge | MapSubtraction
      datatype Datatypes =
        RankLt | RankGt
      datatype BinaryOp =
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
      type T = BinaryOp
    }

    type BinaryOp = BinaryOps.T

    module UnaryOps { // FIXME should be resolved ResolvedUnaryOp (see SinglePassCompiler.cs)
      datatype UnaryOp =
        | Not
        | Cardinality
        | Fresh
        | Allocated
        | Lit
      type T = UnaryOp
    }

    type UnaryOp = UnaryOps.T

    module Exprs {
      import Lib.Math
      import Lib.Seq

      import Types
      import UnaryOps
      import BinaryOps
      import C = CSharpDafnyASTModel

      // public class LiteralExpr : Expression
      datatype Literal =
        | LitBool(b: bool)
        | LitInt(i: int)
        | LitReal(r: real)
        | LitChar(c: string) // FIXME should this use a char?
        | LitString(s: string, verbatim: bool) // FIXME get rid of verbatim flag by unescaping
      {
        function method Depth() : nat { 1 }
      }

      datatype Receiver =
        | StaticReceiver(classType: Types.ClassType)
        | InstanceReceiver(obj: Expr) // TODO: also include ClassType?

      datatype MethodId =
        | Constructor
        | StaticMethod(name: string)
        | InstanceMethod(name: string) // First argument is target object

      datatype BuiltinFunction =
        | Display(ty: Types.Type)
        | Print

      datatype ApplyOp =
        | UnaryOp(uop: UnaryOps.UnaryOp)
        | BinaryOp(bop: BinaryOps.BinaryOp)
        | DataConstructor(name: Types.Path, typeArgs: seq<Types.Type>)
        | MethodCall(classType: Types.ClassType, receiver: MethodId, typeArgs: seq<Types.Type>)
        | FunctionCall // First argument is function
        | Builtin(fn: BuiltinFunction)

      datatype UnsupportedExpr =
        | Invalid(msg: string)
        | UnsupportedExpr(expr: C.Expression)
        | UnsupportedStmt(stmt: C.Statement)

      datatype Expr =
        | Literal(lit: Literal)
        | Apply(aop: ApplyOp, args: seq<Expr>)
        | Block(stmts: seq<Expr>)
        | If(cond: Expr, thn: Expr, els: Expr)
        | Unsupported(e: UnsupportedExpr)
      {
        function method Depth() : nat {
          1 + match this { // FIXME IDE rejects this, command line accepts it
            case Literal(lit: Literal) =>
              0
            case Apply(_, args) =>
              Seq.MaxF(var f := (e: Expr) requires e in args => e.Depth(); f, args, 0)
            case Block(stmts) =>
              Seq.MaxF(var f := (e: Expr) requires e in stmts => e.Depth(); f, stmts, 0)
            case If(cond, thn, els) =>
              Math.Max(cond.Depth(), Math.Max(thn.Depth(), els.Depth()))
            case Unsupported(e: UnsupportedExpr) =>
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

      type T = Expr
    }

    type Expr = Exprs.T

    datatype Method = Method(CompileName: string, methodBody: Exprs.T) {
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

    function method TranslateType(ty: C.Type): D.Types.Type
      reads *
      decreases TypeHeight(ty)
    {
      if ty is C.BoolType then
        D.Types.Bool
      else if ty is C.CharType then
        D.Types.Char
      else if ty is C.IntType then
        D.Types.Int
      else if ty is C.RealType then
        D.Types.Real
      else if ty is C.BigOrdinalType then
        D.Types.BigOrdinal
      else if ty is C.BitvectorType then
        var bvTy := ty as C.BitvectorType;
        D.Types.BitVector(bvTy.Width as int)
      // TODO: the following could be simplified
      else if ty is C.MapType then
        var mTy := ty as C.MapType;
        assume TypeHeight(mTy.Domain) < TypeHeight(mTy);
        assume TypeHeight(mTy.Range) < TypeHeight(mTy);
        var domainTy := TranslateType(mTy.Domain);
        var rangeTy := TranslateType(mTy.Range);
        D.Types.Collection(mTy.Finite, D.Types.CollectionKind.Map(domainTy), rangeTy)
      else if ty is C.SetType then
        var mTy := ty as C.SetType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        D.Types.Collection(mTy.Finite, D.Types.CollectionKind.Set, eltTy)
      else if ty is C.MultiSetType then
        var mTy := ty as C.MultiSetType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        D.Types.Collection(true, D.Types.CollectionKind.Multiset, eltTy)
      else if ty is C.SeqType then
        var mTy := ty as C.SeqType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        D.Types.Collection(true, D.Types.CollectionKind.Seq, eltTy)
      else D.Types.Unsupported(ty)
    }

    const UnaryOpCodeMap: map<C.UnaryOpExpr__Opcode, D.UnaryOps.UnaryOp> :=
      map[C.UnaryOpExpr__Opcode.Not := D.UnaryOps.Not]
         [C.UnaryOpExpr__Opcode.Cardinality := D.UnaryOps.Cardinality]
         [C.UnaryOpExpr__Opcode.Fresh := D.UnaryOps.Fresh]
         [C.UnaryOpExpr__Opcode.Allocated := D.UnaryOps.Allocated]
         [C.UnaryOpExpr__Opcode.Lit := D.UnaryOps.Lit]

    const BinaryOpCodeMap: map<C.BinaryExpr__ResolvedOpcode, D.BinaryOp> :=
      map[C.BinaryExpr__ResolvedOpcode.Iff := D.BinaryOps.Logical(D.BinaryOps.Iff)]
         [C.BinaryExpr__ResolvedOpcode.Imp := D.BinaryOps.Logical(D.BinaryOps.Imp)]
         [C.BinaryExpr__ResolvedOpcode.And := D.BinaryOps.Logical(D.BinaryOps.And)]
         [C.BinaryExpr__ResolvedOpcode.Or := D.BinaryOps.Logical(D.BinaryOps.Or)]
         [C.BinaryExpr__ResolvedOpcode.EqCommon := D.BinaryOps.Eq(D.BinaryOps.EqCommon)]
         [C.BinaryExpr__ResolvedOpcode.NeqCommon := D.BinaryOps.Eq(D.BinaryOps.NeqCommon)]
         [C.BinaryExpr__ResolvedOpcode.Lt := D.BinaryOps.Numeric(D.BinaryOps.Lt)]
         [C.BinaryExpr__ResolvedOpcode.Le := D.BinaryOps.Numeric(D.BinaryOps.Le)]
         [C.BinaryExpr__ResolvedOpcode.Ge := D.BinaryOps.Numeric(D.BinaryOps.Ge)]
         [C.BinaryExpr__ResolvedOpcode.Gt := D.BinaryOps.Numeric(D.BinaryOps.Gt)]
         [C.BinaryExpr__ResolvedOpcode.Add := D.BinaryOps.Numeric(D.BinaryOps.Add)]
         [C.BinaryExpr__ResolvedOpcode.Sub := D.BinaryOps.Numeric(D.BinaryOps.Sub)]
         [C.BinaryExpr__ResolvedOpcode.Mul := D.BinaryOps.Numeric(D.BinaryOps.Mul)]
         [C.BinaryExpr__ResolvedOpcode.Div := D.BinaryOps.Numeric(D.BinaryOps.Div)]
         [C.BinaryExpr__ResolvedOpcode.Mod := D.BinaryOps.Numeric(D.BinaryOps.Mod)]
         [C.BinaryExpr__ResolvedOpcode.LeftShift := D.BinaryOps.BV(D.BinaryOps.LeftShift)]
         [C.BinaryExpr__ResolvedOpcode.RightShift := D.BinaryOps.BV(D.BinaryOps.RightShift)]
         [C.BinaryExpr__ResolvedOpcode.BitwiseAnd := D.BinaryOps.BV(D.BinaryOps.BitwiseAnd)]
         [C.BinaryExpr__ResolvedOpcode.BitwiseOr := D.BinaryOps.BV(D.BinaryOps.BitwiseOr)]
         [C.BinaryExpr__ResolvedOpcode.BitwiseXor := D.BinaryOps.BV(D.BinaryOps.BitwiseXor)]
         [C.BinaryExpr__ResolvedOpcode.LtChar := D.BinaryOps.Char(D.BinaryOps.LtChar)]
         [C.BinaryExpr__ResolvedOpcode.LeChar := D.BinaryOps.Char(D.BinaryOps.LeChar)]
         [C.BinaryExpr__ResolvedOpcode.GeChar := D.BinaryOps.Char(D.BinaryOps.GeChar)]
         [C.BinaryExpr__ResolvedOpcode.GtChar := D.BinaryOps.Char(D.BinaryOps.GtChar)]
         [C.BinaryExpr__ResolvedOpcode.SetEq := D.BinaryOps.Sets(D.BinaryOps.SetEq)]
         [C.BinaryExpr__ResolvedOpcode.SetNeq := D.BinaryOps.Sets(D.BinaryOps.SetNeq)]
         [C.BinaryExpr__ResolvedOpcode.ProperSubset := D.BinaryOps.Sets(D.BinaryOps.ProperSubset)]
         [C.BinaryExpr__ResolvedOpcode.Subset := D.BinaryOps.Sets(D.BinaryOps.Subset)]
         [C.BinaryExpr__ResolvedOpcode.Superset := D.BinaryOps.Sets(D.BinaryOps.Superset)]
         [C.BinaryExpr__ResolvedOpcode.ProperSuperset := D.BinaryOps.Sets(D.BinaryOps.ProperSuperset)]
         [C.BinaryExpr__ResolvedOpcode.Disjoint := D.BinaryOps.Sets(D.BinaryOps.Disjoint)]
         [C.BinaryExpr__ResolvedOpcode.InSet := D.BinaryOps.Sets(D.BinaryOps.InSet)]
         [C.BinaryExpr__ResolvedOpcode.NotInSet := D.BinaryOps.Sets(D.BinaryOps.NotInSet)]
         [C.BinaryExpr__ResolvedOpcode.Union := D.BinaryOps.Sets(D.BinaryOps.Union)]
         [C.BinaryExpr__ResolvedOpcode.Intersection := D.BinaryOps.Sets(D.BinaryOps.Intersection)]
         [C.BinaryExpr__ResolvedOpcode.SetDifference := D.BinaryOps.Sets(D.BinaryOps.SetDifference)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetEq := D.BinaryOps.MultiSets(D.BinaryOps.MultiSetEq)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetNeq := D.BinaryOps.MultiSets(D.BinaryOps.MultiSetNeq)]
         [C.BinaryExpr__ResolvedOpcode.MultiSubset := D.BinaryOps.MultiSets(D.BinaryOps.MultiSubset)]
         [C.BinaryExpr__ResolvedOpcode.MultiSuperset := D.BinaryOps.MultiSets(D.BinaryOps.MultiSuperset)]
         [C.BinaryExpr__ResolvedOpcode.ProperMultiSubset := D.BinaryOps.MultiSets(D.BinaryOps.ProperMultiSubset)]
         [C.BinaryExpr__ResolvedOpcode.ProperMultiSuperset := D.BinaryOps.MultiSets(D.BinaryOps.ProperMultiSuperset)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetDisjoint := D.BinaryOps.MultiSets(D.BinaryOps.MultiSetDisjoint)]
         [C.BinaryExpr__ResolvedOpcode.InMultiSet := D.BinaryOps.MultiSets(D.BinaryOps.InMultiSet)]
         [C.BinaryExpr__ResolvedOpcode.NotInMultiSet := D.BinaryOps.MultiSets(D.BinaryOps.NotInMultiSet)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetUnion := D.BinaryOps.MultiSets(D.BinaryOps.MultiSetUnion)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetIntersection := D.BinaryOps.MultiSets(D.BinaryOps.MultiSetIntersection)]
         [C.BinaryExpr__ResolvedOpcode.MultiSetDifference := D.BinaryOps.MultiSets(D.BinaryOps.MultiSetDifference)]
         [C.BinaryExpr__ResolvedOpcode.SeqEq := D.BinaryOps.Sequences(D.BinaryOps.SeqEq)]
         [C.BinaryExpr__ResolvedOpcode.SeqNeq := D.BinaryOps.Sequences(D.BinaryOps.SeqNeq)]
         [C.BinaryExpr__ResolvedOpcode.ProperPrefix := D.BinaryOps.Sequences(D.BinaryOps.ProperPrefix)]
         [C.BinaryExpr__ResolvedOpcode.Prefix := D.BinaryOps.Sequences(D.BinaryOps.Prefix)]
         [C.BinaryExpr__ResolvedOpcode.Concat := D.BinaryOps.Sequences(D.BinaryOps.Concat)]
         [C.BinaryExpr__ResolvedOpcode.InSeq := D.BinaryOps.Sequences(D.BinaryOps.InSeq)]
         [C.BinaryExpr__ResolvedOpcode.NotInSeq := D.BinaryOps.Sequences(D.BinaryOps.NotInSeq)]
         [C.BinaryExpr__ResolvedOpcode.MapEq := D.BinaryOps.Maps(D.BinaryOps.MapEq)]
         [C.BinaryExpr__ResolvedOpcode.MapNeq := D.BinaryOps.Maps(D.BinaryOps.MapNeq)]
         [C.BinaryExpr__ResolvedOpcode.InMap := D.BinaryOps.Maps(D.BinaryOps.InMap)]
         [C.BinaryExpr__ResolvedOpcode.NotInMap := D.BinaryOps.Maps(D.BinaryOps.NotInMap)]
         [C.BinaryExpr__ResolvedOpcode.MapMerge := D.BinaryOps.Maps(D.BinaryOps.MapMerge)]
         [C.BinaryExpr__ResolvedOpcode.MapSubtraction := D.BinaryOps.Maps(D.BinaryOps.MapSubtraction)]
         [C.BinaryExpr__ResolvedOpcode.RankLt := D.BinaryOps.Datatypes(D.BinaryOps.RankLt)]
         [C.BinaryExpr__ResolvedOpcode.RankGt := D.BinaryOps.Datatypes(D.BinaryOps.RankGt)];

    function method TranslateUnary(u: C.UnaryExpr) : (e: D.Exprs.T)
      decreases ASTHeight(u), 0
      reads *
      ensures P.All_Expr(e, D.Exprs.WellFormed)
    {
      if u is C.UnaryOpExpr then
        var u := u as C.UnaryOpExpr;
        var op, e := u.Op, u.E;
        assume op in UnaryOpCodeMap.Keys; // FIXME expect
        D.Exprs.Apply(D.Exprs.ApplyOp.UnaryOp(UnaryOpCodeMap[op]), [TranslateExpression(e)])
      else
        D.Exprs.Unsupported(D.Exprs.UnsupportedExpr(u))
    }

    function {:axiom} ASTHeight(c: C.Expression) : nat
    function {:axiom} StmtHeight(t: C.Statement) : nat
    function {:axiom} TypeHeight(t: C.Type) : nat

    function method TranslateBinary(b: C.BinaryExpr) : (e: D.Exprs.T)
      decreases ASTHeight(b), 0
      reads *
      ensures P.All_Expr(e, D.Exprs.WellFormed)
    {
      var op, e0, e1 := b.ResolvedOp, b.E0, b.E1;
      // LATER b.AccumulatesForTailRecursion
      assume op in BinaryOpCodeMap.Keys; // FIXME expect
      assume ASTHeight(e0) < ASTHeight(b);
      assume ASTHeight(e1) < ASTHeight(b);
      D.Exprs.Apply(D.Exprs.ApplyOp.BinaryOp(BinaryOpCodeMap[op]), [TranslateExpression(e0), TranslateExpression(e1)])
    }

    function method TranslateLiteral(l: C.LiteralExpr): (e: D.Exprs.T)
      reads *
      ensures P.All_Expr(e, D.Exprs.WellFormed)
    {
      if l.Value is Boolean then
        D.Exprs.Literal(D.Exprs.LitBool(TypeConv.AsBool(l.Value)))
      else if l.Value is Numerics.BigInteger then
        D.Exprs.Literal(D.Exprs.LitInt(TypeConv.AsInt(l.Value)))
      else if l.Value is BaseTypes.BigDec then
        D.Exprs.Literal(D.Exprs.LitReal(TypeConv.AsReal(l.Value))) // TODO test
      else if l.Value is String then
        var str := TypeConv.AsString(l.Value);
        if l is C.CharLiteralExpr then
          D.Exprs.Literal(D.Exprs.LitChar(str))
        else if l is C.StringLiteralExpr then
          var sl := l as C.StringLiteralExpr;
          D.Exprs.Literal(D.Exprs.LitString(str, sl.IsVerbatim))
        else
          D.Exprs.Unsupported(D.Exprs.Invalid("LiteralExpr with .Value of type string must be a char or a string."))
      else D.Exprs.Unsupported(D.Exprs.UnsupportedExpr(l))
    }

    function method TranslateFunctionCall(fce: C.FunctionCallExpr): (e: D.Exprs.T)
      reads *
      decreases ASTHeight(fce), 0
      ensures P.All_Expr(e, D.Exprs.WellFormed)
    {
      assume ASTHeight(fce.Receiver) < ASTHeight(fce);
      var fnExpr := TranslateExpression(fce.Receiver);
      var argsC := ListUtils.ToSeq(fce.Args);
      var argExprs := Seq.Map((e requires e in argsC reads * =>
        assume ASTHeight(e) < ASTHeight(fce); TranslateExpression(e)), argsC);
      D.Exprs.Apply(D.Exprs.ApplyOp.FunctionCall, [fnExpr] + argExprs)
    }

    function method TranslateDatatypeValue(dtv: C.DatatypeValue): (e: D.Exprs.T)
      reads *
      decreases ASTHeight(dtv), 0
      ensures P.All_Expr(e, D.Exprs.WellFormed)
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
      D.Exprs.Apply(D.Exprs.DataConstructor([n], typeArgs), argExprs) // TODO: proper path
    }

    function method TranslateDisplayExpr(de: C.DisplayExpression): (e: D.Exprs.T)
      reads *
      decreases ASTHeight(de), 0
      ensures P.All_Expr(e, D.Exprs.WellFormed)
    {
      var elSeq := ListUtils.ToSeq(de.Elements);
      var exprs := Seq.Map((e requires e in elSeq reads * =>
        assume ASTHeight(e) < ASTHeight(de); TranslateExpression(e)), elSeq);
      var ty := TranslateType(de.Type);
      D.Exprs.Apply(D.Exprs.ApplyOp.Builtin(D.Exprs.Display(ty)), exprs)
    }

    function method TranslateExpressionPair(mde: C.MapDisplayExpr, ep: C.ExpressionPair): (e: D.Exprs.T)
      reads *
      requires Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde)
      decreases ASTHeight(mde), 0
      ensures P.All_Expr(e, D.Exprs.WellFormed)
    {
      var tyA := TranslateType(ep.A.Type);
      // TODO: This isn't really a sequence of type tyA! It should really construct pairs
      var ty := D.Types.Collection(true, D.Types.CollectionKind.Seq, tyA);
      D.Exprs.Apply(D.Exprs.ApplyOp.Builtin(D.Exprs.Display(ty)), [TranslateExpression(ep.A), TranslateExpression(ep.B)])
    }

    function method TranslateMapDisplayExpr(mde: C.MapDisplayExpr): (e: D.Exprs.T)
      reads *
      decreases ASTHeight(mde), 1
      ensures P.All_Expr(e, D.Exprs.WellFormed)
    {
      var elSeq := ListUtils.ToSeq(mde.Elements);
      var exprs := Seq.Map((ep: C.ExpressionPair) reads * =>
        assume Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde);
        TranslateExpressionPair(mde, ep), elSeq);
      var ty := TranslateType(mde.Type);
      D.Exprs.Apply(D.Exprs.ApplyOp.Builtin(D.Exprs.Display(ty)), exprs)
    }

    function method TranslateExpression(c: C.Expression) : (e: D.Exprs.T)
      reads *
      decreases ASTHeight(c), 2
      ensures P.All_Expr(e, D.Exprs.WellFormed)
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
      else D.Exprs.Unsupported(D.Exprs.UnsupportedExpr(c))
    }

    function method TranslateStatement(s: C.Statement) : D.Exprs.T
      reads *
      decreases StmtHeight(s)
    {
      if s is C.PrintStmt then
        var p := s as C.PrintStmt;
        D.Exprs.Apply(D.Exprs.ApplyOp.Builtin(D.Exprs.Print), Seq.Map(TranslateExpression, ListUtils.ToSeq(p.Args)))
      else if s is C.BlockStmt then
        var b := s as C.BlockStmt;
        var stmts := ListUtils.ToSeq(b.Body);
        var stmts' := Seq.Map(s' requires s' in stmts reads * =>
          assume StmtHeight(s') < StmtHeight(s); TranslateStatement(s'), stmts);
        D.Exprs.Block(stmts')
      else if s is C.IfStmt then
        var i := s as C.IfStmt;
        // TODO: look at i.IsBindingGuard
        assume ASTHeight(i.Guard) < StmtHeight(i);
        assume StmtHeight(i.Thn) < StmtHeight(i);
        assume StmtHeight(i.Els) < StmtHeight(i);
        var cond := TranslateExpression(i.Guard);
        var thn := TranslateStatement(i.Thn);
        var els := TranslateStatement(i.Els);
        D.Exprs.If(cond, thn, els)
      else D.Exprs.Unsupported(D.Exprs.UnsupportedStmt(s))
    }

    function method TranslateMethod(m: C.Method) : D.Method reads * {
      // var compileName := m.CompileName;
      // FIXME “Main”
      D.Method("Main", D.Exprs.Block(Seq.Map(TranslateStatement, ListUtils.ToSeq(m.Body.Body))))
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
      reads f.reads
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

    type ExprTransformer = Transformer<Expr, Expr>

    lemma Map_All_TR<A(!new), B(00)>(tr: Transformer<A, B>, ts: seq<A>)
      ensures Seq.All(tr.PC, Seq.Map(tr.f, ts))
    {}

    module Shallow {
      import opened Lib
      import opened AST

      function method All_Method(m: Method, P: Expr -> bool) : bool {
        match m {
          case Method(CompileName_, methodBody) => P(methodBody)
        }
      }

      function method All_Program(p: Program, P: Expr -> bool) : bool {
        match p {
          case Program(mainMethod) => All_Method(mainMethod, P)
        }
      }

      function method All(p: Program, P: Expr -> bool) : bool {
        All_Program(p, P)
      }
    }

    module Deep {
      import opened Lib
      import opened AST
      import Shallow

      function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool
        decreases e, 0
      {
        match e {
          case Literal(lit: Exprs.Literal) => true
          case Apply(_, exprs) =>
            Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
          case Block(exprs) => Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
          case If(cond, thn, els) =>
            All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
          case Unsupported(e) => true
        }
      }

      // FIXME rewrite in terms Expr_Children below
      function method All_Expr(e: Expr, P: Expr -> bool) : bool {
        && P(e)
        && AllChildren_Expr(e, P)
      }

      function method All_Method(m: Method, P: Expr -> bool) : bool {
        Shallow.All_Method(m, e => All_Expr(e, P))
      }

      function method All_Program(p: Program, P: Expr -> bool) : bool {
        Shallow.All_Program(p, e => All_Expr(e, P))
      }
    }

    import opened AST

    lemma Shallow_Deep(p: Program, P: Expr -> bool)
      requires Shallow.All_Program(p, (e => Deep.All_Expr(e, P)))
      ensures Deep.All_Program(p, P)
    {}

    lemma AllImpliesChildren(e: Expr, p: Expr -> bool)
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
      // function method Map_Expr(e: Expr, f: Expr -> Expr) : (e': Expr)
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

      predicate IsBottomUpTransformer(f: Expr -> Expr, PC: Expr -> bool) {
        forall e | Deep.AllChildren_Expr(e, PC) :: Deep.All_Expr(f(e), PC)
      }

      type BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.PC)
        witness TR(d => d, _ => true)

      function method MapChildren_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
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

          // Statements
          case Block(exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Predicates.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            Expr.Block(exprs')
          case If(cond, thn, els) =>
            Expr.If(Map_Expr(cond, tr), Map_Expr(thn, tr), Map_Expr(els, tr))
          case Unsupported(_) =>
            e
        }
      }

      function method Map_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
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

    function method FlipNegatedBinop1(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
    {
      match op {
        case Eq(NeqCommon) => BinaryOps.Eq(BinaryOps.EqCommon)
        case Maps(MapNeq) => BinaryOps.Maps(BinaryOps.MapEq)
        case Maps(NotInMap) => BinaryOps.Maps(BinaryOps.InMap)
        case MultiSets(MultiSetNeq) => BinaryOps.MultiSets(BinaryOps.MultiSetEq)
        case MultiSets(NotInMultiSet) => BinaryOps.MultiSets(BinaryOps.InMultiSet)
        case Sequences(SeqNeq) => BinaryOps.Sequences(BinaryOps.SeqEq)
        case Sets(SetNeq) => BinaryOps.Sets(BinaryOps.SetEq)
        case Sets(NotInSet) => BinaryOps.Sets(BinaryOps.InSet)
        case Sequences(NotInSeq) => BinaryOps.Sequences(BinaryOps.InSeq)
        case _ => op
      }
    }

    function method FlipNegatedBinop(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
      ensures !IsNegatedBinop(op')
    {
      FlipNegatedBinop1(op)
    }

    predicate method IsNegatedBinop(op: BinaryOps.BinaryOp) {
      FlipNegatedBinop1(op) != op
    }

    predicate method IsNegatedBinopExpr(e: Exprs.T) {
      match e {
        case Apply(BinaryOp(op), _) => IsNegatedBinop(op)
        case _ => false
      }
    }

    predicate NotANegatedBinopExpr(e: Exprs.T) {
      !IsNegatedBinopExpr(e)
    }

    // function method EliminateNegatedBinops_Expr1(e: Exprs.T) : (e': Exprs.T)
    //   ensures NotANegatedBinopExpr(e')
    // {
    //   match e {
    //     case Binary(bop, e0, e1) =>
    //       if IsNegatedBinop(bop) then
    //         Expr.UnaryOp(UnaryOps.Not, Expr.Binary(FlipNegatedBinop(bop), e0, e1))
    //       else
    //         Expr.Binary(bop, e0, e1)
    //     case _ => e
    //   }
    // }

    // FIXME Add `require Deep.AllChildren_Expr(e, NotANegatedBinopExpr)`
    function method EliminateNegatedBinops_Expr1(e: Exprs.T) : (e': Exprs.T)
      ensures NotANegatedBinopExpr(e')
    {
      match e {
        case Apply(BinaryOp(op), es) =>
          if IsNegatedBinop(op) then
            Exprs.Apply(Exprs.ApplyOp.UnaryOp(UnaryOps.Not), [Expr.Apply(Exprs.ApplyOp.BinaryOp(FlipNegatedBinop(op)), es)])
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
              Expr.Apply(Exprs.ApplyOp.BinaryOp(FlipNegatedBinop(op)), es)
          };
          var e' := Exprs.Apply(Exprs.ApplyOp.UnaryOp(UnaryOps.Not), [e'']);
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

    function method EliminateNegatedBinops_Expr_direct(e: Exprs.T) : (e': Exprs.T)
      requires Deep.All_Expr(e, Exprs.WellFormed)
      ensures Deep.All_Expr(e', NotANegatedBinopExpr)
      ensures Deep.All_Expr(e', Exprs.WellFormed)
    {
      AllImpliesChildren(e, Exprs.WellFormed);
      match e {
        case Literal(lit_) => e
        case Apply(BinaryOp(bop), exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          if IsNegatedBinop(bop) then
            var e'' := Expr.Apply(Exprs.ApplyOp.BinaryOp(FlipNegatedBinop(bop)), exprs');
            assert Deep.All_Expr(e'', NotANegatedBinopExpr);
            assert Deep.All_Expr(e'', Exprs.WellFormed);
            var e' := Exprs.Apply(Exprs.ApplyOp.UnaryOp(UnaryOps.Not), [e'']);
            e'
          else
            Expr.Apply(Exprs.ApplyOp.BinaryOp(bop), exprs')
        case Apply(aop, exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Expr.Apply(aop, exprs')

        case Block(exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Expr.Block(exprs')
        case If(cond, thn, els) =>
          Expr.If(EliminateNegatedBinops_Expr_direct(cond),
                  EliminateNegatedBinops_Expr_direct(thn),
                  EliminateNegatedBinops_Expr_direct(els))
        case Unsupported(_) =>
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

    function method Children(e: Exprs.T) : (s: seq<Exprs.T>)
      ensures forall e' | e' in s :: e'.Depth() < e.Depth()
    {
      match e {
        case Literal(lit: Exprs.Literal) => []
        case Apply(aop, exprs: seq<Exprs.T>) => exprs
        case Block(exprs) => exprs
        case If(cond, thn, els) => [cond, thn, els]
        case Unsupported(_) => []
      }
    }

    lemma All_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
      requires Deep.All_Expr(e, P)
      requires forall e' :: P(e') ==> Q(e')
      decreases e
      ensures Deep.All_Expr(e, Q)
    { // NEAT
      forall e' | e' in Children(e) { All_Expr_weaken(e', P, Q); }
      // match e {
      //   case UnaryOp(uop: UnaryOps.UnaryOp, e': Exprs.T) =>
      //     All_Expr_weaken(e', P, Q);
      //   case Binary(bop: BinaryOps.BinaryOp, e0: Exprs.T, e1: Exprs.T) =>
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
