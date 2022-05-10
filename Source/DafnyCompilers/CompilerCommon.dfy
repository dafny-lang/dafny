include "CSharpDafnyASTModel.dfy"
include "CSharpInterop.dfy"
include "CSharpDafnyInterop.dfy"
include "CSharpDafnyASTInterop.dfy"
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
        | Real
        | BigOrdinal
        | BitVector(width: nat)
        | Collection(finite: bool, kind: CollectionKind, eltType: Type)
        | Function(args: seq<Type>, ret: Type) // TODO
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
      datatype Sequences =
        SeqEq | SeqNeq | Prefix | ProperPrefix | Concat | InSeq | NotInSeq |
        SeqSelect | SeqTake | SeqDrop // Separate nodes in DafnyAST.cs
      datatype Sets =
        SetEq | SetNeq | Subset | Superset | ProperSubset | ProperSuperset |
        Disjoint | InSet | NotInSet | Union | Intersection | SetDifference
      datatype Multisets =
        MultisetEq | MultisetNeq | MultiSubset | MultiSuperset |
        ProperMultiSubset | ProperMultiSuperset | MultisetDisjoint | InMultiset |
        NotInMultiset | MultisetUnion | MultisetIntersection | MultisetDifference |
        MultisetSelect // Separate node in DafnyAST.cs
      datatype Maps =
        MapEq | MapNeq | InMap | NotInMap | MapMerge | MapSubtraction |
        MapSelect // Separate node in DafnyAST.cs
      datatype Datatypes =
        RankLt | RankGt
      datatype BinaryOp =
        | Logical(oLogical: Logical)
        | Eq(oEq: Eq)
        | Numeric(oNumeric: Numeric)
        | BV(oBV: BV)
        | Char(oChar: Char)
        | Sequences(oSequences: Sequences)
        | Sets(oSets: Sets)
        | Multisets(oMultisets: Multisets)
        | Maps(oMaps: Maps)
        | Datatypes(oDatatypes: Datatypes)
      type T(!new,00,==) = BinaryOp
    }

    type BinaryOp = BinaryOps.T

    module TernaryOps {
      import Types

      datatype Sequences =
        SeqUpdate | SeqSubseq
      datatype Multisets =
        MultisetUpdate
      datatype Maps =
        MapUpdate

      datatype TernaryOp =
        | Sequences(oSequences: Sequences)
        | Multisets(oMultisets: Multisets)
        | Maps(oMaps: Maps)

      type T(!new,00,==) = TernaryOp
    }

    type TernaryOp = TernaryOps.T

    module UnaryOps {
      datatype UnaryOp =
        | BVNot
        | BoolNot
        | SeqLength
        | SetCard
        | MultisetCard
        | MapCard
        | MemberSelect(name: string)
        // Ghost operators
        // | Fresh
        // | Allocated
        // | Lit
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

      // FIXME should literals just be Values.T?
      datatype Literal =
        | LitBool(b: bool)
        | LitInt(i: int)
        | LitReal(r: real)
        | LitChar(c: char)
        | LitString(s: string, verbatim: bool) // FIXME get rid of verbatim flag by unescaping
      {
        function method Depth() : nat { 1 }
      }

      datatype BuiltinFunction =
        | Display(ty: Types.Type)
        | Print

      // DafnyAst.cs handles `f(1)` differently from `(var g := f; g)(1)`, but not us
      datatype EagerOp =
        | UnaryOp(uop: UnaryOps.T)
        | BinaryOp(bop: BinaryOps.T)
        | TernaryOp(top: TernaryOps.T)
        | Builtin(builtin: BuiltinFunction)
        | FunctionCall() // First argument is expression that resolves to function or method
        | DataConstructor(name: Types.Path, typeArgs: seq<Types.Type>)

      datatype LazyOp =
        | And
        | Or
        | Imp

      datatype ApplyOp =
        | Lazy(lOp: LazyOp)
        | Eager(eOp: EagerOp)

      datatype Expr =
        | Var(name: string)
        | Literal(lit: Literal)
        | Abs(vars: seq<string>, body: Expr)
        | Apply(aop: ApplyOp, args: seq<Expr>)
        | Block(stmts: seq<Expr>)
        | If(cond: Expr, thn: Expr, els: Expr)
      {
        function method Depth() : nat {
          1 + match this {
            case Var(_) =>
              0
            case Literal(lit: Literal) =>
              0
            case Abs(vars, body) =>
              body.Depth()
            case Apply(_, args) =>
              Seq.MaxF(var f := (e: Expr) requires e in args => e.Depth(); f, args, 0)
            case Block(stmts) =>
              Seq.MaxF(var f := (e: Expr) requires e in stmts => e.Depth(); f, stmts, 0)
            case If(cond, thn, els) =>
              Math.Max(cond.Depth(), Math.Max(thn.Depth(), els.Depth()))
          }
        }

        function method Children() : (s: seq<Expr>)
          ensures forall e' | e' in s :: e'.Depth() < this.Depth()
        {
          match this {
            case Var(_) => []
            case Literal(lit) => []
            case Abs(vars, body) => [body]
            case Apply(aop, exprs) => exprs
            case Block(exprs) => exprs
            case If(cond, thn, els) => [cond, thn, els]
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
            |es| == 3
          case Apply(Eager(FunctionCall()), es) =>
            |es| >= 1 // Needs a function to call
          case Apply(Eager(Builtin(Display(ty))), es) =>
            ty.Collection? && ty.finite
          case _ => true
        }
      }

      function method ConstructorsMatch(e: Expr, e': Expr): bool {
        match e {
          case Var(name) =>
            e'.Var? && name == e'.name
          case Literal(l) =>
            e'.Literal? && l == e'.lit
          case Abs(vars, body) =>
            e'.Abs? && vars == e'.vars
          case Apply(aop, args) =>
            e'.Apply? && aop == e'.aop && |args| == |e'.args|
          case Block(stmts) =>
            e'.Block? && |stmts| == |e'.stmts|
          case If(cond, thn, els) =>
            e'.If?
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
    import opened Lib.Datatypes
    import opened CSharpInterop
    import opened CSharpInterop.System
    import opened CSharpDafnyInterop
    import opened CSharpDafnyInterop.Microsoft
    import opened CSharpDafnyASTInterop
    import C = CSharpDafnyASTModel
    import D = AST
    import DE = AST.Exprs
    import DT = AST.Types
    import P = Predicates.Deep

    datatype TranslationError =
      | Invalid(msg: string)
      | GhostExpr(expr: C.Expression)
      | UnsupportedType(ty: C.Type)
      | UnsupportedExpr(expr: C.Expression)
      | UnsupportedStmt(stmt: C.Statement)
    {
      function method ToString() : string {
        match this
          case Invalid(msg) =>
            "Invalid term: " + msg
          case GhostExpr(expr) =>
            "Ghost expression: " + TypeConv.ObjectToString(expr)
          case UnsupportedType(ty) =>
            "Unsupported type: " + TypeConv.ObjectToString(ty)
          case UnsupportedExpr(expr) =>
            "Unsupported expression: " + TypeConv.ObjectToString(expr)
          case UnsupportedStmt(stmt) =>
            "Unsupported statement: " + TypeConv.ObjectToString(stmt)
      }
    }

    type WfExpr = e: DE.Expr | P.All_Expr(e, DE.WellFormed)
      witness DE.Block([])

    type TranslationResult<+A> =
      Result<A, TranslationError>

    function method TranslateType(ty: C.Type)
      : TranslationResult<DT.Type>
      reads *
      decreases TypeHeight(ty)
    {
      var ty := TypeUtils.NormalizeExpand(ty);
      if ty is C.BoolType then
        Success(DT.Bool)
      else if ty is C.CharType then
        Success(DT.Char)
      else if ty is C.IntType then
        Success(DT.Int)
      else if ty is C.RealType then
        Success(DT.Real)
      else if ty is C.BigOrdinalType then
        Success(DT.BigOrdinal)
      else if ty is C.BitvectorType then
        var bvTy := ty as C.BitvectorType;
        :- Need(bvTy.Width >= 0, Invalid("BV width must be >= 0"));
        Success(DT.BitVector(bvTy.Width as int))
      // TODO: the following could be simplified
      else if ty is C.MapType then
        var ty := ty as C.MapType;
        assume TypeHeight(ty.Domain) < TypeHeight(ty);
        assume TypeHeight(ty.Range) < TypeHeight(ty);
        var domainTy :- TranslateType(ty.Domain);
        var rangeTy :- TranslateType(ty.Range);
        Success(DT.Collection(ty.Finite, DT.CollectionKind.Map(domainTy), rangeTy))
      else if ty is C.SetType then
        var ty := ty as C.SetType;
        assume TypeHeight(ty.Arg) < TypeHeight(ty);
        var eltTy :- TranslateType(ty.Arg);
        Success(DT.Collection(ty.Finite, DT.CollectionKind.Set, eltTy))
      else if ty is C.MultiSetType then
        var ty := ty as C.MultiSetType;
        assume TypeHeight(ty.Arg) < TypeHeight(ty);
        var eltTy :- TranslateType(ty.Arg);
        Success(DT.Collection(true, DT.CollectionKind.Multiset, eltTy))
      else if ty is C.SeqType then
        var ty := ty as C.SeqType;
        assume TypeHeight(ty.Arg) < TypeHeight(ty);
        var eltTy :- TranslateType(ty.Arg);
        Success(DT.Collection(true, DT.CollectionKind.Seq, eltTy))
      else
        Failure(UnsupportedType(ty))
    }

    const GhostUnaryOps: set<C.UnaryOpExpr__ResolvedOpcode> :=
      {C.UnaryOpExpr__ResolvedOpcode.Fresh,
       C.UnaryOpExpr__ResolvedOpcode.Allocated,
       C.UnaryOpExpr__ResolvedOpcode.Lit}

    const UnaryOpMap: map<C.UnaryOpExpr__ResolvedOpcode, D.UnaryOp> :=
      map[C.UnaryOpExpr__ResolvedOpcode.BVNot := D.UnaryOps.BVNot,
          C.UnaryOpExpr__ResolvedOpcode.BoolNot := D.UnaryOps.BoolNot,
          C.UnaryOpExpr__ResolvedOpcode.SeqLength := D.UnaryOps.SeqLength,
          C.UnaryOpExpr__ResolvedOpcode.SetCard := D.UnaryOps.SetCard,
          C.UnaryOpExpr__ResolvedOpcode.MultiSetCard := D.UnaryOps.MultisetCard,
          C.UnaryOpExpr__ResolvedOpcode.MapCard := D.UnaryOps.MapCard]

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
          C.BinaryExpr__ResolvedOpcode.SeqEq := D.BinaryOps.Sequences(D.BinaryOps.SeqEq),
          C.BinaryExpr__ResolvedOpcode.SeqNeq := D.BinaryOps.Sequences(D.BinaryOps.SeqNeq),
          C.BinaryExpr__ResolvedOpcode.ProperPrefix := D.BinaryOps.Sequences(D.BinaryOps.ProperPrefix),
          C.BinaryExpr__ResolvedOpcode.Prefix := D.BinaryOps.Sequences(D.BinaryOps.Prefix),
          C.BinaryExpr__ResolvedOpcode.Concat := D.BinaryOps.Sequences(D.BinaryOps.Concat),
          C.BinaryExpr__ResolvedOpcode.InSeq := D.BinaryOps.Sequences(D.BinaryOps.InSeq),
          C.BinaryExpr__ResolvedOpcode.NotInSeq := D.BinaryOps.Sequences(D.BinaryOps.NotInSeq),
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

    function method TranslateIdentifierExpr(ie: C.IdentifierExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
    {
      Success(DE.Var(TypeConv.AsString(ie.Name)))
    }

    predicate Decreases(u: object, v: object)
      requires u is C.Expression || u is C.Statement
      requires v is C.Expression || v is C.Statement
    {
      ASTHeight(u) < ASTHeight(v)
    }

    function method TranslateUnary(u: C.UnaryExpr)
      : (e: TranslationResult<WfExpr>)
      decreases ASTHeight(u), 0
      reads *
    {
      :- Need(u is C.UnaryOpExpr, UnsupportedExpr(u));
      var u := u as C.UnaryOpExpr;
      var op, e := u.ResolvedOp, u.E;
      assume Decreases(e, u);
      :- Need(op !in GhostUnaryOps, GhostExpr(u));
      :- Need(op in UnaryOpMap.Keys, UnsupportedExpr(u));
      var te :- TranslateExpression(e);
      Success(DE.Apply(DE.Eager(DE.UnaryOp(UnaryOpMap[op])), [te]))
    }

    function method TranslateBinary(b: C.BinaryExpr)
      : (e: TranslationResult<WfExpr>)
      decreases ASTHeight(b), 0
      reads *
    {
      var op, e0, e1 := b.ResolvedOp, b.E0, b.E1;
      // LATER b.AccumulatesForTailRecursion
      assume Decreases(e0, b);
      assume Decreases(e1, b);
      :- Need(op in BinaryOpCodeMap, UnsupportedExpr(b));
      var t0 :- TranslateExpression(e0);
      var t1 :- TranslateExpression(e1);
      Success(DE.Apply(BinaryOpCodeMap[op], [t0, t1]))
    }

    function method TranslateLiteral(l: C.LiteralExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
    {
      if l.Value is Boolean then
        Success(DE.Literal(DE.LitBool(TypeConv.AsBool(l.Value))))
      else if l.Value is Numerics.BigInteger then
        Success(DE.Literal(DE.LitInt(TypeConv.AsInt(l.Value))))
      else if l.Value is BaseTypes.BigDec then
        Success(DE.Literal(DE.LitReal(TypeConv.AsReal(l.Value)))) // TODO test
      else if l.Value is String then
        var str := TypeConv.AsString(l.Value);
        if l is C.CharLiteralExpr then
          :- Need(|str| == 1, Invalid("CharLiteralExpr must contain a single character."));
          Success(DE.Literal(DE.LitChar(str[0])))
        else if l is C.StringLiteralExpr then
          var sl := l as C.StringLiteralExpr;
          Success(DE.Literal(DE.LitString(str, sl.IsVerbatim)))
        else
          Failure(Invalid("LiteralExpr with .Value of type string must be a char or a string."))
      else
        Failure(UnsupportedExpr(l))
    }

    function method TranslateApplyExpr(ae: C.ApplyExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(ae), 0
    {
      assume Decreases(ae.Function, ae);
      var fn :- TranslateExpression(ae.Function);
      var args := ListUtils.ToSeq(ae.Args);
      var args :- Seq.MapResult(args, e requires e in args reads * =>
        assume Decreases(e, ae); TranslateExpression(e));
      Success(DE.Apply(DE.Eager(DE.FunctionCall()), [fn] + args))
    }

    function method TranslateFunctionCall(fce: C.FunctionCallExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(fce), 0
    {
      // FIXME do we need to consider the receiver?
      var fname := TypeConv.AsString(fce.Function.FullName);
      var fn :- if fce.Receiver.Resolved is C.StaticReceiverExpr then
          Success(DE.Var(fname))
        else
          assume Decreases(fce.Receiver, fce);
          var receiver :- TranslateExpression(fce.Receiver);
          Success(DE.Apply(DE.Eager(DE.UnaryOp(DE.UnaryOps.MemberSelect(fname))), [receiver]));
      assert P.All_Expr(fn, DE.WellFormed);
      var args := ListUtils.ToSeq(fce.Args);
      var args :- Seq.MapResult(args, e requires e in args reads * =>
        assume Decreases(e, fce); TranslateExpression(e));
      Success(DE.Apply(DE.Eager(DE.FunctionCall()), [fn] + args))
    }

    function method TranslateDatatypeValue(dtv: C.DatatypeValue)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(dtv), 0
    {
      var ctor := dtv.Ctor;
      var n := TypeConv.AsString(ctor.Name);
      var typeArgs :- Seq.MapResult(ListUtils.ToSeq(dtv.InferredTypeArgs), TranslateType);
      // TODO: also include formals in the following, and filter out ghost arguments
      var args := ListUtils.ToSeq(dtv.Arguments);
      var args :- Seq.MapResult(args, e requires e in args reads * =>
        assume Decreases(e, dtv); TranslateExpression(e));
      Success(DE.Apply(DE.Eager(DE.DataConstructor([n], typeArgs)), args)) // TODO: proper path
    }

    function method TranslateDisplayExpr(de: C.DisplayExpression)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(de), 0
    {
      var ty :- TranslateType(de.Type);
      :- Need(ty.Collection? && ty.finite, Invalid("`DisplayExpr` must be a finite collection."));
      var elems := ListUtils.ToSeq(de.Elements);
      var elems :- Seq.MapResult(elems, e requires e in elems reads * =>
        assume Decreases(e, de); TranslateExpression(e));
      Success(DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), elems))
    }

    function method TranslateExpressionPair(mde: C.MapDisplayExpr, ep: C.ExpressionPair)
      : (e: TranslationResult<WfExpr>)
      reads *
      requires Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde)
      decreases ASTHeight(mde), 0
    {
      var tyA :- TranslateType(ep.A.Type);
      // TODO: This isn't really a sequence of type tyA! It should really construct pairs
      var ty := DT.Collection(true, DT.CollectionKind.Seq, tyA);
      var tA :- TranslateExpression(ep.A);
      var tB :- TranslateExpression(ep.B);
      Success(DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), [tA, tB]))
    }

    function method TranslateMapDisplayExpr(mde: C.MapDisplayExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(mde), 1
    {
      var ty :- TranslateType(mde.Type);
      :- Need(ty.Collection? && ty.kind.Map? && ty.finite, Invalid("`MapDisplayExpr` must be a map."));
      var elems := ListUtils.ToSeq(mde.Elements);
      var elems :- Seq.MapResult(elems, (ep: C.ExpressionPair) requires ep in elems reads * =>
        assume Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde);
        TranslateExpressionPair(mde, ep));
      Success(DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), elems))
    }

    function method TranslateSeqUpdateExpr(se: C.SeqUpdateExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(se), 0
    {
      var ty :- TranslateType(se.Type);
      :- Need(ty.Collection? && ty.kind != DT.Set(),
              Invalid("`SeqUpdate` must be a map, sequence, or multiset."));
      assume Math.Max(ASTHeight(se.Seq), Math.Max(ASTHeight(se.Index), ASTHeight(se.Value))) < ASTHeight(se);
      var tSeq :- TranslateExpression(se.Seq);
      var tIndex :- TranslateExpression(se.Index);
      var tValue :- TranslateExpression(se.Value);
      var op := match ty.kind
        case Seq() => DE.TernaryOps.Sequences(DE.TernaryOps.SeqUpdate)
        case Map(_) => DE.TernaryOps.Maps(DE.TernaryOps.MapUpdate)
        case Multiset() => DE.TernaryOps.Multisets(DE.TernaryOps.MultisetUpdate);
      Success(DE.Apply(DE.Eager(DE.TernaryOp(op)), [tSeq, tIndex, tValue]))
    }

    function method TranslateLambdaExpr(le: C.LambdaExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(le), 0
    {
      var bvars := Seq.Map((bv: C.BoundVar) reads * => TypeConv.AsString(bv.Name),
        ListUtils.ToSeq(le.BoundVars));
      assume Decreases(le.Term, le);
      var body :- TranslateExpression(le.Term);
      Success(DE.Abs(bvars, body))
    }

    function method TranslateConcreteSyntaxExpression(ce: C.ConcreteSyntaxExpression)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(ce), 0
    {
      assume Decreases(ce.ResolvedExpression, ce);
      TranslateExpression(ce.ResolvedExpression)
    }

    function method TranslateITEExpr(ie: C.ITEExpr)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(ie), 0
    {
      // TODO: look at i.IsBindingGuard
      assume Decreases(ie.Test, ie);
      assume Decreases(ie.Thn, ie);
      assume Decreases(ie.Els, ie);
      var cond :- TranslateExpression(ie.Test);
      var thn :- TranslateExpression(ie.Thn);
      var els :- TranslateExpression(ie.Els);
      Success(DE.If(cond, thn, els))
    }

    function method TranslateExpression(c: C.Expression)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(c), 2
    {
      if c is C.IdentifierExpr then
        TranslateIdentifierExpr(c as C.IdentifierExpr)
      else if c is C.UnaryExpr then
        TranslateUnary(c as C.UnaryExpr)
      else if c is C.BinaryExpr then
        TranslateBinary(c as C.BinaryExpr)
      else if c is C.LiteralExpr then
        TranslateLiteral(c as C.LiteralExpr)
      else if c is C.ApplyExpr then
        TranslateApplyExpr(c as C.ApplyExpr)
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
      else if c is C.LambdaExpr then
        TranslateLambdaExpr(c as C.LambdaExpr)
      else if c is C.ConcreteSyntaxExpression then
        TranslateConcreteSyntaxExpression(c as C.ConcreteSyntaxExpression)
      else if c is C.ITEExpr then
        TranslateITEExpr(c as C.ITEExpr)
      else Failure(UnsupportedExpr(c))
    }

    function method TranslatePrintStmt(p: C.PrintStmt)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(p), 0
    {
      var exprs :- Seq.MapResult(ListUtils.ToSeq(p.Args), TranslateExpression);
      Success(DE.Apply(DE.Eager(DE.Builtin(DE.Print)), exprs))
    }

    function method TranslateBlockStmt(b: C.BlockStmt)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(b), 0
    {
      var stmts := ListUtils.ToSeq(b.Body);
      var stmts' :- Seq.MapResult(stmts, s' requires s' in stmts reads * =>
        assume Decreases(s', b); TranslateStatement(s'));
      Success(DE.Block(stmts'))
    }

    function method TranslateIfStmt(i: C.IfStmt)
      : (e: TranslationResult<WfExpr>)
      reads *
      decreases ASTHeight(i), 0
    {
      // TODO: look at i.IsBindingGuard
      assume Decreases(i.Guard, i);
      assume Decreases(i.Thn, i);
      assume Decreases(i.Els, i);
      var cond :- TranslateExpression(i.Guard);
      var thn :- TranslateStatement(i.Thn);
      var els :- TranslateStatement(i.Els);
      Success(DE.If(cond, thn, els))
    }

    function method TranslateStatement(s: C.Statement)
      : TranslationResult<WfExpr>
      reads *
      decreases ASTHeight(s), 1
    {
      if s is C.PrintStmt then
        TranslatePrintStmt(s as C.PrintStmt)
      else if s is C.BlockStmt then
        TranslateBlockStmt(s as C.BlockStmt)
      else if s is C.IfStmt then
        TranslateIfStmt(s as C.IfStmt)
      else Failure(UnsupportedStmt(s))
    }

    function method TranslateMethod(m: C.Method)
      : TranslationResult<D.Method>
      reads *
    {
      // var compileName := m.CompileName;
      // FIXME “Main”
      var stmts :- Seq.MapResult(ListUtils.ToSeq(m.Body.Body), TranslateStatement);
      Success(D.Method("Main", DE.Block(stmts)))
    }

    // DISCUSS: It should be possible to ensure termination by checking for
    // cycles instead of assuming that ASTHeight decreases.  Would that be
    // enough? (Does Dafny assume that allocated memory is finite?)
    function method TranslateProgram(p: C.Program)
      : TranslationResult<D.Program>
      reads *
    {
      var tm :- TranslateMethod(p.MainMethod);
      Success(D.Program(tm))
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
      TR(f: A --> B, ghost Post: B -> bool)

    predicate HasValidPC<A(!new), B>(tr: Transformer'<A, B>) {
      forall a: A :: tr.f.requires(a) ==> tr.Post(tr.f(a))
    }

    type Transformer<!A(!new), !B(0)> = tr: Transformer'<A, B> | HasValidPC(tr)
      witness *

    type ExprTransformer = Transformer<Expr, Expr>

    lemma Map_All_TR<A(!new), B(00)>(tr: Transformer<A, B>, ts: seq<A>)
      requires forall x | x in ts :: tr.f.requires(x)
      ensures Seq.All(tr.Post, Seq.Map(tr.f, ts))
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

        function method All_Expr(e: Expr, P: Expr -> bool)
          : (b: bool)
          decreases e.Depth(), 1

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

        lemma AllChildren_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
          requires AllChildren_Expr(e, P)
          requires forall e' :: P(e') ==> Q(e')
          decreases e, 0
          ensures AllChildren_Expr(e, Q)

        lemma All_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
          requires All_Expr(e, P)
          requires forall e' :: P(e') ==> Q(e')
          decreases e, 1
          ensures All_Expr(e, Q)
      }

      module Rec refines Base { // DISCUSS
        function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
          P(e) &&
          // https://github.com/dafny-lang/dafny/issues/2107
          // https://github.com/dafny-lang/dafny/issues/2109
          // Duplicated to avoid mutual recursion with AllChildren_Expr
          match e {
            case Var(_) => true
            case Literal(lit) => true
            case Abs(vars, body) => All_Expr(body, P)
            case Apply(_, exprs) =>
              Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
            case Block(exprs) => Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
            case If(cond, thn, els) =>
              All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
          }
        }

        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
          match e {
            case Var(_) => true
            case Literal(lit) => true
            case Abs(vars, body) => All_Expr(body, P)
            case Apply(_, exprs) =>
              Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
            case Block(exprs) => Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
            case If(cond, thn, els) =>
              All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
          }
        }

        lemma AllExprTrue(e: Expr)
          ensures All_Expr(e, _ => true)
        {}

        lemma AllImpliesChildren ... {}

        lemma All_Expr_weaken ... {
          AllChildren_Expr_weaken(e, P, Q);
        }

        lemma AllChildren_Expr_weaken ... { // NEAT
          forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
        }
      }

      module NonRec refines Base {
        // https://github.com/dafny-lang/dafny/issues/2107
        // https://github.com/dafny-lang/dafny/issues/2109
        function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
          P(e) && forall e' | e' in e.Children() :: All_Expr(e', P)
        }

        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
          forall e' | e' in e.Children() :: All_Expr(e', P)
        }

        lemma AllImpliesChildren ... {}

        lemma AllChildren_Expr_weaken ... {
          forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
        }

        lemma All_Expr_weaken ... {
          AllChildren_Expr_weaken(e, P, Q);
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
    module Deep refines DeepImpl.Rec {}
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
        requires Shallow.All_Method(m, tr.f.requires)
        ensures Shallow.All_Method(m', tr.Post) // FIXME Deep
      {
        match m {
          case Method(CompileName, methodBody) =>
            Method(CompileName, tr.f(methodBody))
        }
      }

      function method {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
        requires Shallow.All_Program(p, tr.f.requires)
        ensures Shallow.All_Program(p', tr.Post)
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

      predicate MapChildrenPreservesPre(f: Expr --> Expr, post: Expr -> bool) {
        forall e, e' ::
          (&& Exprs.ConstructorsMatch(e, e')
           && f.requires(e)
           && Deep.AllChildren_Expr(e', post)) ==> f.requires(e')
       }

      predicate TransformerMatchesPrePost(f: Expr --> Expr, post: Expr -> bool) {
        forall e: Expr | Deep.AllChildren_Expr(e, post) && f.requires(e) ::
          Deep.All_Expr(f(e), post)
      }

      predicate IsBottomUpTransformer(f: Expr --> Expr, post: Expr -> bool) {
        && TransformerMatchesPrePost(f, post)
        && MapChildrenPreservesPre(f, post)
      }

      const IdentityTransformer: ExprTransformer :=
        TR(d => d, _ => true)

      lemma IdentityMatchesPrePost()
        ensures TransformerMatchesPrePost(IdentityTransformer.f, IdentityTransformer.Post)
      { }

      lemma IdentityPreservesPre()
        ensures MapChildrenPreservesPre(IdentityTransformer.f, IdentityTransformer.Post)
      { }

      type BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.Post)
        witness (IdentityMatchesPrePost();
                 IdentityPreservesPre();
                 IdentityTransformer)

      function method {:vcs_split_on_every_assert} MapChildren_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 0
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.AllChildren_Expr(e', tr.Post)
        ensures Exprs.ConstructorsMatch(e, e')
      {
        Deep.AllImpliesChildren(e, tr.f.requires);

        // Not using datatype updates below to ensure that we get a warning if a
        // type gets new arguments
        match e {
          // Expressions
          case Var(_) => e
          case Literal(lit_) => e
          case Abs(vars, body) => Expr.Abs(vars, Map_Expr(body, tr))
          case Apply(aop, exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Predicates.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Apply(aop, exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'

          // Statements
          case Block(exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Predicates.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Block(exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'
          case If(cond, thn, els) =>
            var e' := Expr.If(Map_Expr(cond, tr), Map_Expr(thn, tr), Map_Expr(els, tr));
            assert Exprs.ConstructorsMatch(e, e');
            e'
        }
      }

      function method Map_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 1
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.All_Expr(e', tr.Post)
      {
        Deep.AllImpliesChildren(e, tr.f.requires);
        tr.f(MapChildren_Expr(e, tr))
      }

      function method Map_Expr_Transformer(tr: BottomUpTransformer) : (tr': ExprTransformer)
      {
        TR(e requires Deep.All_Expr(e, tr.f.requires) => Map_Expr(e, tr),
           e' => Deep.All_Expr(e', tr.Post))
      }

      function method {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) : (m': Method)
        requires Deep.All_Method(m, tr.f.requires)
        ensures Deep.All_Method(m', tr.Post)
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      function method {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) : (p': Program)
        requires Deep.All_Program(p, tr.f.requires)
        ensures Deep.All_Program(p', tr.Post)
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
        case Sequences(SeqNeq) => BinaryOps.Sequences(BinaryOps.SeqEq)
        case Sequences(NotInSeq) => BinaryOps.Sequences(BinaryOps.InSeq)
        case Sets(SetNeq) => BinaryOps.Sets(BinaryOps.SetEq)
        case Sets(NotInSet) => BinaryOps.Sets(BinaryOps.InSet)
        case Multisets(MultisetNeq) => BinaryOps.Multisets(BinaryOps.MultisetEq)
        case Multisets(NotInMultiset) => BinaryOps.Multisets(BinaryOps.InMultiset)
        case Maps(MapNeq) => BinaryOps.Maps(BinaryOps.MapEq)
        case Maps(NotInMap) => BinaryOps.Maps(BinaryOps.InMap)
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
    //         Expr.UnaryOp(UnaryOps.BoolNot, Expr.Binary(FlipNegatedBinop(bop), e0, e1))
    //       else
    //         Expr.Binary(bop, e0, e1)
    //     case _ => e
    //   }
    // }

    function method EliminateNegatedBinops_Expr1(e: Exprs.T) : (e': Exprs.T)
      ensures NotANegatedBinopExpr(e')
    {
      match e {
        case Apply(Eager(BinaryOp(op)), es) =>
          if IsNegatedBinop(op) then
            var flipped := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), es);
            var negated := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [flipped]);
            negated
          else
            e
        case _ => e
      }
    }

    lemma EliminateNegatedBinopsMatchesPrePost()
      ensures TransformerMatchesPrePost(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr)
      {}

    lemma EliminateNegatedBinopsPreservesPre()
      ensures MapChildrenPreservesPre(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr)
    { forall e, e'
        ensures ((Exprs.ConstructorsMatch(e, e') &&
                  EliminateNegatedBinops_Expr1.requires(e) &&
                  Deep.AllChildren_Expr(e', NotANegatedBinopExpr)) ==>
                  EliminateNegatedBinops_Expr1.requires(e'))
        { Deep.AllExprTrue(e'); }
     }

     const EliminateNegatedBinops_Expr : BottomUpTransformer :=
      ( EliminateNegatedBinopsMatchesPrePost();
        EliminateNegatedBinopsPreservesPre();
        TR(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr))

    function method EliminateNegatedBinops_Expr_direct(e: Exprs.T) : (e': Exprs.T)
      requires Deep.All_Expr(e, Exprs.WellFormed)
      ensures Deep.All_Expr(e', NotANegatedBinopExpr)
      ensures Deep.All_Expr(e', Exprs.WellFormed)
    {
      Deep.AllImpliesChildren(e, Exprs.WellFormed);
      match e {
        case Var(_) => e
        case Literal(lit_) => e
        case Abs(vars, body) => Exprs.Abs(vars, EliminateNegatedBinops_Expr_direct(body))
        case Apply(Eager(BinaryOp(bop)), exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          if IsNegatedBinop(bop) then
            var e'' := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(bop))), exprs');
            var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [e'']);
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
      }
    }

    function method EliminateNegatedBinops(p: Program) : (p': Program)
      requires Deep.All_Program(p, EliminateNegatedBinops_Expr.f.requires)
      ensures Deep.All_Program(p', NotANegatedBinopExpr)
    {
      Map_Program(p, EliminateNegatedBinops_Expr)
    }
  }
}
