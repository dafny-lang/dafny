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
        | Seq
        | Set
        | Multiset
        | Map(keyType: Type)

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
        | Unsupported // DISCUSS: !new (ty: C.Type)
        | Invalid // DISCUSS: !new (ty: C.Type)
        | Class(classType: ClassType)

      type T(!new,00,==) = Type
    }

    type Type = Types.T

    datatype Tokd<T> =
      Tokd(tok: Boogie.IToken, val: T)

    module BinaryOps {
      datatype Logical =
        Iff // And, Or, and Imp are in LazyOp
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
      datatype Multisets =
        MultisetEq | MultisetNeq | MultiSubset | MultiSuperset |
        ProperMultiSubset | ProperMultiSuperset | MultisetDisjoint | InMultiset |
        NotInMultiset | MultisetUnion | MultisetIntersection | MultisetDifference
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
        | Multisets(oMultisets: Multisets)
        | Sequences(oSequences: Sequences)
        | Maps(oMaps: Maps)
        | Datatypes(oDatatypes: Datatypes)
      type T(!new,00,==) = BinaryOp
    }

    type BinaryOp = BinaryOps.T

    module TernaryOps {
      import Types

      datatype TernaryOp =
        | CollectionUpdate(kind: Types.CollectionKind)

      type T(!new,00,==) = TernaryOp
    }

    type TernaryOp = TernaryOps.T

    module UnaryOps { // FIXME should be resolved ResolvedUnaryOp (see SinglePassCompiler.cs)
      datatype UnaryOp =
        | Not
        | Cardinality
        | Fresh
        | Allocated
        | Lit
      type T(!new,00,==) = UnaryOp
    }

    type UnaryOp = UnaryOps.T

    module Exprs {
      import Lib.Math
      import Lib.Seq

      import Types
      import UnaryOps
      import BinaryOps
      import TernaryOps
      import C = CSharpDafnyASTModel

      datatype Literal =
        | LitBool(b: bool)
        | LitInt(i: int)
        | LitReal(r: real)
        | LitChar(c: char)
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

      datatype EagerOp =
        | UnaryOp(uop: UnaryOps.T)
        | BinaryOp(bop: BinaryOps.T)
        | TernaryOp(top: TernaryOps.T)
        | DataConstructor(name: Types.Path, typeArgs: seq<Types.Type>)
        | MethodCall(classType: Types.ClassType, receiver: MethodId, typeArgs: seq<Types.Type>)
        | FunctionCall // First argument is function
        | Builtin(fn: BuiltinFunction)

      datatype LazyOp =
        | And
        | Or
        | Imp

      datatype ApplyOp =
        | Lazy(lOp: LazyOp)
        | Eager(eOp: EagerOp)

      datatype UnsupportedExpr =
        | Invalid(msg: string)
        | UnsupportedExpr // DISCUSS: !new (expr: C.Expression)
        | UnsupportedStmt // DISCUSS: !new (stmt: C.Statement)

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

        function method Children() : (s: seq<Expr>)
          ensures forall e' | e' in s :: e'.Depth() < this.Depth()
        {
          match this {
            case Literal(lit: Literal) => []
            case Apply(aop, exprs: seq<Expr>) => exprs
            case Block(exprs) => exprs
            case If(cond, thn, els) => [cond, thn, els]
            case Unsupported(_) => []
          }
        }
      }

      function method WellFormed(e: Expr): bool {
        match e {
          case Apply(Lazy(_), es) =>
            |es| == 2
          case Apply(Eager(UnaryOp(_)), es) =>
            |es| == 1
          case Apply(Eager(BinaryOp(_)), es) =>
            |es| == 2
          case Apply(Eager(TernaryOp(top)), es) =>
            |es| == 3 &&
            (top.CollectionUpdate? ==> top.kind != Types.Set())
          case Apply(Eager(Builtin(Display(ty))), es) =>
            ty.Collection? && ty.finite
          case _ => true
        }
      }

      type T(!new,00,==) = Expr
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
    import DE = AST.Exprs
    import DT = AST.Types
    import P = Predicates.Deep

    function method TranslateType(ty: C.Type): DT.Type
      reads *
      decreases TypeHeight(ty)
    {
      if ty is C.BoolType then
        DT.Bool
      else if ty is C.CharType then
        DT.Char
      else if ty is C.IntType then
        DT.Int
      else if ty is C.RealType then
        DT.Real
      else if ty is C.BigOrdinalType then
        DT.BigOrdinal
      else if ty is C.BitvectorType then
        var bvTy := ty as C.BitvectorType;
        if bvTy.Width >= 0 then DT.BitVector(bvTy.Width as int)
        else DT.Invalid//(ty)
      // TODO: the following could be simplified
      else if ty is C.MapType then
        var mTy := ty as C.MapType;
        assume TypeHeight(mTy.Domain) < TypeHeight(mTy);
        assume TypeHeight(mTy.Range) < TypeHeight(mTy);
        var domainTy := TranslateType(mTy.Domain);
        var rangeTy := TranslateType(mTy.Range);
        DT.Collection(mTy.Finite, DT.CollectionKind.Map(domainTy), rangeTy)
      else if ty is C.SetType then
        var mTy := ty as C.SetType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        DT.Collection(mTy.Finite, DT.CollectionKind.Set, eltTy)
      else if ty is C.MultiSetType then
        var mTy := ty as C.MultiSetType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        DT.Collection(true, DT.CollectionKind.Multiset, eltTy)
      else if ty is C.SeqType then
        var mTy := ty as C.SeqType;
        assume TypeHeight(mTy.Arg) < TypeHeight(mTy);
        var eltTy := TranslateType(mTy.Arg);
        DT.Collection(true, DT.CollectionKind.Seq, eltTy)
      else DT.Unsupported//(ty)
    }

    const UnaryOpMap: map<C.UnaryOpExpr__Opcode, D.UnaryOp> :=
      map[C.UnaryOpExpr__Opcode.Not := D.UnaryOps.Not,
          C.UnaryOpExpr__Opcode.Cardinality := D.UnaryOps.Cardinality,
          C.UnaryOpExpr__Opcode.Fresh := D.UnaryOps.Fresh,
          C.UnaryOpExpr__Opcode.Allocated := D.UnaryOps.Allocated,
          C.UnaryOpExpr__Opcode.Lit := D.UnaryOps.Lit]

    const LazyBinopMap: map<C.BinaryExpr__ResolvedOpcode, DE.LazyOp> :=
      map[C.BinaryExpr__ResolvedOpcode.Imp := DE.Imp,
          C.BinaryExpr__ResolvedOpcode.And := DE.And,
          C.BinaryExpr__ResolvedOpcode.Or := DE.Or]

    const EagerBinopMap: map<C.BinaryExpr__ResolvedOpcode, DE.BinaryOps.T> :=
      map[C.BinaryExpr__ResolvedOpcode.Iff := D.BinaryOps.Logical(D.BinaryOps.Iff),
          C.BinaryExpr__ResolvedOpcode.EqCommon := D.BinaryOps.Eq(D.BinaryOps.EqCommon),
          C.BinaryExpr__ResolvedOpcode.NeqCommon := D.BinaryOps.Eq(D.BinaryOps.NeqCommon),
          C.BinaryExpr__ResolvedOpcode.Lt := D.BinaryOps.Numeric(D.BinaryOps.Lt),
          C.BinaryExpr__ResolvedOpcode.Le := D.BinaryOps.Numeric(D.BinaryOps.Le),
          C.BinaryExpr__ResolvedOpcode.Ge := D.BinaryOps.Numeric(D.BinaryOps.Ge),
          C.BinaryExpr__ResolvedOpcode.Gt := D.BinaryOps.Numeric(D.BinaryOps.Gt),
          C.BinaryExpr__ResolvedOpcode.Add := D.BinaryOps.Numeric(D.BinaryOps.Add),
          C.BinaryExpr__ResolvedOpcode.Sub := D.BinaryOps.Numeric(D.BinaryOps.Sub),
          C.BinaryExpr__ResolvedOpcode.Mul := D.BinaryOps.Numeric(D.BinaryOps.Mul),
          C.BinaryExpr__ResolvedOpcode.Div := D.BinaryOps.Numeric(D.BinaryOps.Div),
          C.BinaryExpr__ResolvedOpcode.Mod := D.BinaryOps.Numeric(D.BinaryOps.Mod),
          C.BinaryExpr__ResolvedOpcode.LeftShift := D.BinaryOps.BV(D.BinaryOps.LeftShift),
          C.BinaryExpr__ResolvedOpcode.RightShift := D.BinaryOps.BV(D.BinaryOps.RightShift),
          C.BinaryExpr__ResolvedOpcode.BitwiseAnd := D.BinaryOps.BV(D.BinaryOps.BitwiseAnd),
          C.BinaryExpr__ResolvedOpcode.BitwiseOr := D.BinaryOps.BV(D.BinaryOps.BitwiseOr),
          C.BinaryExpr__ResolvedOpcode.BitwiseXor := D.BinaryOps.BV(D.BinaryOps.BitwiseXor),
          C.BinaryExpr__ResolvedOpcode.LtChar := D.BinaryOps.Char(D.BinaryOps.LtChar),
          C.BinaryExpr__ResolvedOpcode.LeChar := D.BinaryOps.Char(D.BinaryOps.LeChar),
          C.BinaryExpr__ResolvedOpcode.GeChar := D.BinaryOps.Char(D.BinaryOps.GeChar),
          C.BinaryExpr__ResolvedOpcode.GtChar := D.BinaryOps.Char(D.BinaryOps.GtChar),
          C.BinaryExpr__ResolvedOpcode.SetEq := D.BinaryOps.Sets(D.BinaryOps.SetEq),
          C.BinaryExpr__ResolvedOpcode.SetNeq := D.BinaryOps.Sets(D.BinaryOps.SetNeq),
          C.BinaryExpr__ResolvedOpcode.ProperSubset := D.BinaryOps.Sets(D.BinaryOps.ProperSubset),
          C.BinaryExpr__ResolvedOpcode.Subset := D.BinaryOps.Sets(D.BinaryOps.Subset),
          C.BinaryExpr__ResolvedOpcode.Superset := D.BinaryOps.Sets(D.BinaryOps.Superset),
          C.BinaryExpr__ResolvedOpcode.ProperSuperset := D.BinaryOps.Sets(D.BinaryOps.ProperSuperset),
          C.BinaryExpr__ResolvedOpcode.Disjoint := D.BinaryOps.Sets(D.BinaryOps.Disjoint),
          C.BinaryExpr__ResolvedOpcode.InSet := D.BinaryOps.Sets(D.BinaryOps.InSet),
          C.BinaryExpr__ResolvedOpcode.NotInSet := D.BinaryOps.Sets(D.BinaryOps.NotInSet),
          C.BinaryExpr__ResolvedOpcode.Union := D.BinaryOps.Sets(D.BinaryOps.Union),
          C.BinaryExpr__ResolvedOpcode.Intersection := D.BinaryOps.Sets(D.BinaryOps.Intersection),
          C.BinaryExpr__ResolvedOpcode.SetDifference := D.BinaryOps.Sets(D.BinaryOps.SetDifference),
          C.BinaryExpr__ResolvedOpcode.MultiSetEq := D.BinaryOps.Multisets(D.BinaryOps.MultisetEq),
          C.BinaryExpr__ResolvedOpcode.MultiSetNeq := D.BinaryOps.Multisets(D.BinaryOps.MultisetNeq),
          C.BinaryExpr__ResolvedOpcode.MultiSubset := D.BinaryOps.Multisets(D.BinaryOps.MultiSubset),
          C.BinaryExpr__ResolvedOpcode.MultiSuperset := D.BinaryOps.Multisets(D.BinaryOps.MultiSuperset),
          C.BinaryExpr__ResolvedOpcode.ProperMultiSubset := D.BinaryOps.Multisets(D.BinaryOps.ProperMultiSubset),
          C.BinaryExpr__ResolvedOpcode.ProperMultiSuperset := D.BinaryOps.Multisets(D.BinaryOps.ProperMultiSuperset),
          C.BinaryExpr__ResolvedOpcode.MultiSetDisjoint := D.BinaryOps.Multisets(D.BinaryOps.MultisetDisjoint),
          C.BinaryExpr__ResolvedOpcode.InMultiSet := D.BinaryOps.Multisets(D.BinaryOps.InMultiset),
          C.BinaryExpr__ResolvedOpcode.NotInMultiSet := D.BinaryOps.Multisets(D.BinaryOps.NotInMultiset),
          C.BinaryExpr__ResolvedOpcode.MultiSetUnion := D.BinaryOps.Multisets(D.BinaryOps.MultisetUnion),
          C.BinaryExpr__ResolvedOpcode.MultiSetIntersection := D.BinaryOps.Multisets(D.BinaryOps.MultisetIntersection),
          C.BinaryExpr__ResolvedOpcode.MultiSetDifference := D.BinaryOps.Multisets(D.BinaryOps.MultisetDifference),
          C.BinaryExpr__ResolvedOpcode.SeqEq := D.BinaryOps.Sequences(D.BinaryOps.SeqEq),
          C.BinaryExpr__ResolvedOpcode.SeqNeq := D.BinaryOps.Sequences(D.BinaryOps.SeqNeq),
          C.BinaryExpr__ResolvedOpcode.ProperPrefix := D.BinaryOps.Sequences(D.BinaryOps.ProperPrefix),
          C.BinaryExpr__ResolvedOpcode.Prefix := D.BinaryOps.Sequences(D.BinaryOps.Prefix),
          C.BinaryExpr__ResolvedOpcode.Concat := D.BinaryOps.Sequences(D.BinaryOps.Concat),
          C.BinaryExpr__ResolvedOpcode.InSeq := D.BinaryOps.Sequences(D.BinaryOps.InSeq),
          C.BinaryExpr__ResolvedOpcode.NotInSeq := D.BinaryOps.Sequences(D.BinaryOps.NotInSeq),
          C.BinaryExpr__ResolvedOpcode.MapEq := D.BinaryOps.Maps(D.BinaryOps.MapEq),
          C.BinaryExpr__ResolvedOpcode.MapNeq := D.BinaryOps.Maps(D.BinaryOps.MapNeq),
          C.BinaryExpr__ResolvedOpcode.InMap := D.BinaryOps.Maps(D.BinaryOps.InMap),
          C.BinaryExpr__ResolvedOpcode.NotInMap := D.BinaryOps.Maps(D.BinaryOps.NotInMap),
          C.BinaryExpr__ResolvedOpcode.MapMerge := D.BinaryOps.Maps(D.BinaryOps.MapMerge),
          C.BinaryExpr__ResolvedOpcode.MapSubtraction := D.BinaryOps.Maps(D.BinaryOps.MapSubtraction),
          C.BinaryExpr__ResolvedOpcode.RankLt := D.BinaryOps.Datatypes(D.BinaryOps.RankLt),
          C.BinaryExpr__ResolvedOpcode.RankGt := D.BinaryOps.Datatypes(D.BinaryOps.RankGt)];

    const BinaryOpCodeMap: map<C.BinaryExpr__ResolvedOpcode, DE.ApplyOp> :=
      (map k | k in LazyBinopMap  :: DE.Lazy(LazyBinopMap[k])) +
      (map k | k in EagerBinopMap :: DE.Eager(DE.BinaryOp(EagerBinopMap[k])))

    function method TranslateUnary(u: C.UnaryExpr) : (e: DE.T)
      decreases ASTHeight(u), 0
      reads *
      ensures P.All_Expr(e, DE.WellFormed)
    {
      if u is C.UnaryOpExpr then
        var u := u as C.UnaryOpExpr;
        var op, e := u.Op, u.E;
        assume op in UnaryOpMap.Keys; // FIXME expect
        DE.Apply(DE.Eager(DE.UnaryOp(UnaryOpMap[op])), [TranslateExpression(e)])
      else
        DE.Unsupported(DE.UnsupportedExpr)//(u))
    }

    function {:axiom} ASTHeight(c: C.Expression) : nat
    function {:axiom} StmtHeight(t: C.Statement) : nat
    function {:axiom} TypeHeight(t: C.Type) : nat

    function method TranslateBinary(b: C.BinaryExpr) : (e: DE.T)
      decreases ASTHeight(b), 0
      reads *
      ensures P.All_Expr(e, DE.WellFormed)
    {
      var op, e0, e1 := b.ResolvedOp, b.E0, b.E1;
      // LATER b.AccumulatesForTailRecursion
      assume ASTHeight(e0) < ASTHeight(b);
      assume ASTHeight(e1) < ASTHeight(b);
      if op in BinaryOpCodeMap then
        DE.Apply(BinaryOpCodeMap[op], [TranslateExpression(e0), TranslateExpression(e1)])
      else
        DE.Unsupported(DE.UnsupportedExpr)//(b))
    }

    function method TranslateLiteral(l: C.LiteralExpr): (e: DE.T)
      reads *
      ensures P.All_Expr(e, DE.WellFormed)
    {
      if l.Value is Boolean then
        DE.Literal(DE.LitBool(TypeConv.AsBool(l.Value)))
      else if l.Value is Numerics.BigInteger then
        DE.Literal(DE.LitInt(TypeConv.AsInt(l.Value)))
      else if l.Value is BaseTypes.BigDec then
        DE.Literal(DE.LitReal(TypeConv.AsReal(l.Value))) // TODO test
      else if l.Value is String then
        var str := TypeConv.AsString(l.Value);
        if l is C.CharLiteralExpr then
          if |str| == 1 then DE.Literal(DE.LitChar(str[0]))
          else DE.Unsupported(DE.Invalid("CharLiteralExpr must contain a single character."))
        else if l is C.StringLiteralExpr then
          var sl := l as C.StringLiteralExpr;
          DE.Literal(DE.LitString(str, sl.IsVerbatim))
        else
          DE.Unsupported(DE.Invalid("LiteralExpr with .Value of type string must be a char or a string."))
      else DE.Unsupported(DE.UnsupportedExpr)//(l))
    }

    function method TranslateFunctionCall(fce: C.FunctionCallExpr): (e: DE.T)
      reads *
      decreases ASTHeight(fce), 0
      ensures P.All_Expr(e, DE.WellFormed)
    {
      assume ASTHeight(fce.Receiver) < ASTHeight(fce);
      var fnExpr := TranslateExpression(fce.Receiver);
      var argsC := ListUtils.ToSeq(fce.Args);
      var argExprs := Seq.Map((e requires e in argsC reads * =>
        assume ASTHeight(e) < ASTHeight(fce); TranslateExpression(e)), argsC);
      DE.Apply(DE.Eager(DE.FunctionCall), [fnExpr] + argExprs)
    }

    function method TranslateDatatypeValue(dtv: C.DatatypeValue): (e: DE.T)
      reads *
      decreases ASTHeight(dtv), 0
      ensures P.All_Expr(e, DE.WellFormed)
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
      DE.Apply(DE.Eager(DE.DataConstructor([n], typeArgs)), argExprs) // TODO: proper path
    }

    function method TranslateDisplayExpr(de: C.DisplayExpression): (e: DE.T)
      reads *
      decreases ASTHeight(de), 0
      ensures P.All_Expr(e, DE.WellFormed)
    {
      var ty := TranslateType(de.Type);
      if ty.Collection? && ty.finite then
        var elSeq := ListUtils.ToSeq(de.Elements);
        var exprs := Seq.Map((e requires e in elSeq reads * =>
          assume ASTHeight(e) < ASTHeight(de); TranslateExpression(e)), elSeq);
        DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), exprs)
      else
        DE.Unsupported(DE.Invalid("`DisplayExpr` must be a finite collection."))
    }

    function method TranslateExpressionPair(mde: C.MapDisplayExpr, ep: C.ExpressionPair): (e: DE.T)
      reads *
      requires Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde)
      decreases ASTHeight(mde), 0
      ensures P.All_Expr(e, DE.WellFormed)
    {
      var tyA := TranslateType(ep.A.Type);
      // TODO: This isn't really a sequence of type tyA! It should really construct pairs
      var ty := DT.Collection(true, DT.CollectionKind.Seq, tyA);
      DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), [TranslateExpression(ep.A), TranslateExpression(ep.B)])
    }

    function method TranslateMapDisplayExpr(mde: C.MapDisplayExpr): (e: DE.T)
      reads *
      decreases ASTHeight(mde), 1
      ensures P.All_Expr(e, DE.WellFormed)
    {
      var ty := TranslateType(mde.Type);
      if ty.Collection? && ty.kind.Map? && ty.finite then
        var elSeq := ListUtils.ToSeq(mde.Elements);
        var exprs := Seq.Map((ep: C.ExpressionPair) reads * =>
          assume Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde);
          TranslateExpressionPair(mde, ep), elSeq);
        DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), exprs)
      else
        DE.Unsupported(DE.Invalid("`MapDisplayExpr` must be a map."))
    }

    function method TranslateSeqUpdateExpr(se: C.SeqUpdateExpr): (e: DE.T)
      reads *
      decreases ASTHeight(se), 0
      ensures P.All_Expr(e, DE.WellFormed)
    {
      var ty := TranslateType(se.Type);
      if ty.Collection? && ty.kind != DT.Set() then
        assume Math.Max(ASTHeight(se.Seq), Math.Max(ASTHeight(se.Index), ASTHeight(se.Value))) < ASTHeight(se);
        DE.Apply(DE.Eager(DE.TernaryOp(DE.TernaryOps.CollectionUpdate(ty.kind))),
                 [TranslateExpression(se.Seq),
                  TranslateExpression(se.Index),
                  TranslateExpression(se.Value)])
      else
        DE.Unsupported(DE.Invalid("`SeqUpdate` must be a map, sequence, or multiset."))
    }

    function method TranslateExpression(c: C.Expression) : (e: DE.T)
      reads *
      decreases ASTHeight(c), 2
      ensures P.All_Expr(e, DE.WellFormed)
    {
      if c is C.BinaryExpr then // TODO Unary
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
      else if c is C.SeqUpdateExpr then
        TranslateSeqUpdateExpr(c as C.SeqUpdateExpr)
      else DE.Unsupported(DE.UnsupportedExpr)//(c))
    }

    function method TranslateStatement(s: C.Statement) : DE.T
      reads *
      decreases StmtHeight(s)
    {
      if s is C.PrintStmt then
        var p := s as C.PrintStmt;
        DE.Apply(DE.Eager(DE.Builtin(DE.Print)), Seq.Map(TranslateExpression, ListUtils.ToSeq(p.Args)))
      else if s is C.BlockStmt then
        var b := s as C.BlockStmt;
        var stmts := ListUtils.ToSeq(b.Body);
        var stmts' := Seq.Map(s' requires s' in stmts reads * =>
          assume StmtHeight(s') < StmtHeight(s); TranslateStatement(s'), stmts);
        DE.Block(stmts')
      else if s is C.IfStmt then
        var i := s as C.IfStmt;
        // TODO: look at i.IsBindingGuard
        assume ASTHeight(i.Guard) < StmtHeight(i);
        assume StmtHeight(i.Thn) < StmtHeight(i);
        assume StmtHeight(i.Els) < StmtHeight(i);
        var cond := TranslateExpression(i.Guard);
        var thn := TranslateStatement(i.Thn);
        var els := TranslateStatement(i.Els);
        DE.If(cond, thn, els)
      else DE.Unsupported(DE.UnsupportedStmt)//(s))
    }

    function method TranslateMethod(m: C.Method) : D.Method reads * {
      // var compileName := m.CompileName;
      // FIXME “Main”
      D.Method("Main", DE.Block(Seq.Map(TranslateStatement, ListUtils.ToSeq(m.Body.Body))))
    }

    function method TranslateProgram(p: C.Program) : D.Program reads * {
      D.Program(TranslateMethod(p.MainMethod))
    }
  }

  module Predicates {
    import opened AST

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

    module DeepImpl {
      abstract module Base {
        import opened Lib
        import opened AST
        import Shallow

        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool
          decreases e.Depth(), 0

        function method All_Expr(e: Expr, P: Expr -> bool) : bool
          decreases e.Depth(), 1
        {
          && P(e)
          && AllChildren_Expr(e, P)
        }

        function method All_Method(m: Method, P: Expr -> bool) : bool {
          Shallow.All_Method(m, e => All_Expr(e, P))
        }

        function method All_Program(p: Program, P: Expr -> bool) : bool {
          Shallow.All_Program(p, e => All_Expr(e, P))
        }

        // This lemma allows callers to force one level of unfolding of All_Expr
        lemma AllImpliesChildren(e: Expr, p: Expr -> bool)
          requires All_Expr(e, p)
          ensures AllChildren_Expr(e, p)
        {}

        lemma AllChildren_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
          requires AllChildren_Expr(e, P)
          requires forall e' :: P(e') ==> Q(e')
          decreases e
          ensures AllChildren_Expr(e, Q)

        lemma All_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
          requires All_Expr(e, P)
          requires forall e' :: P(e') ==> Q(e')
          ensures All_Expr(e, Q)
        {
          AllChildren_Expr_weaken(e, P, Q);
        }
      }

      module Rec refines Base { // DISCUSS
        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
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

        lemma AllChildren_Expr_weaken ... { // NEAT
          forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
        }
      }

      module NonRec refines Base {
        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
          forall e' | e' in e.Children() :: All_Expr(e', P)
        }

        lemma AllChildren_Expr_weaken ... {
          forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
        }
      }

      module Equiv {
        import Rec
        import NonRec
        import opened AST

        lemma AllChildren_Expr(e: Expr, P: Expr -> bool)
          decreases e.Depth(), 0
          ensures Rec.AllChildren_Expr(e, P) == NonRec.AllChildren_Expr(e, P)
        {
          forall e' | e' in e.Children() { All_Expr(e', P); }
        }

        lemma All_Expr(e: Expr, P: Expr -> bool)
          decreases e.Depth(), 1
          ensures Rec.All_Expr(e, P) == NonRec.All_Expr(e, P)
        {
          AllChildren_Expr(e, P);
        }
      }
    }

    // Both implementations of Deep should work, but NonRec can be somewhat
    // simpler to work with.  If needed, use ``DeepImpl.Equiv.All_Expr`` to
    // switch between implementations.
    module Deep refines DeepImpl.NonRec {}
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
        case Multisets(MultisetNeq) => BinaryOps.Multisets(BinaryOps.MultisetEq)
        case Multisets(NotInMultiset) => BinaryOps.Multisets(BinaryOps.InMultiset)
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
        case Apply(Eager(BinaryOp(op)), _) => IsNegatedBinop(op)
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
        case Apply(Eager(BinaryOp(op)), es) =>
          if IsNegatedBinop(op) then
            Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.Not)),
                        [Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), es)])
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
            case Apply(Eager(BinaryOp(op)), es) =>
              Expr.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), es)
          };
          var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.Not)), [e'']);
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
      Deep.AllImpliesChildren(e, Exprs.WellFormed);
      match e {
        case Literal(lit_) => e
        case Apply(Eager(BinaryOp(bop)), exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          if IsNegatedBinop(bop) then
            var e'' := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(bop))), exprs');
            assert Deep.All_Expr(e'', NotANegatedBinopExpr);
            assert Deep.All_Expr(e'', Exprs.WellFormed);
            var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.Not)), [e'']);
            e'
          else
            Expr.Apply(Exprs.Eager(Exprs.BinaryOp(bop)), exprs')
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
      Map_Program(p, EliminateNegatedBinops_Expr)
    }
  }
}
