include "CSharpDafnyASTModel.dfy"
include "CSharpInterop.dfy"
include "CSharpDafnyInterop.dfy"
include "CSharpDafnyASTInterop.dfy"
include "Library.dfy"
include "StrTree.dfy"
include "Interp.dfy"

module CompilerRewriter {
  module Transformer {
    import DCC = DafnyCompilerCommon
    import opened DCC.AST

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
      TR(f: A --> B, ghost post: B -> bool, ghost rel: (A,B) -> bool)

    predicate HasValidPost<A(!new), B>(tr: Transformer'<A, B>) {
      forall a: A :: tr.f.requires(a) ==> tr.post(tr.f(a))
    }

    predicate HasValidRel<A(!new), B(0)>(tr: Transformer'<A, B>) {
      forall a: A :: tr.f.requires(a) ==> tr.rel(a, tr.f(a))
    }

    type Transformer<!A(!new), !B(0)> = tr: Transformer'<A, B>
      | HasValidPost(tr) && HasValidRel(tr)
      witness *

    type ExprTransformer = Transformer<Expr, Expr>

    lemma Map_All_TR<A(!new), B(00)>(tr: Transformer<A, B>, ts: seq<A>)
      requires forall x | x in ts :: tr.f.requires(x)
      ensures Seq.All(tr.post, Seq.Map(tr.f, ts))
    {}
  }

  module Rewriter {
    import DCC = DafnyCompilerCommon
    import Lib
    import opened DCC.AST
    import opened StrTree
    import opened Lib.Datatypes
    import opened CSharpInterop

    module Shallow {
      import DCC = DafnyCompilerCommon
      import opened Lib
      import opened DCC.AST
      import opened DCC.Predicates
      import opened Transformer

      function method {:opaque} Map_Method(m: Method, tr: ExprTransformer) : (m': Method)
        requires Shallow.All_Method(m, tr.f.requires)
        ensures Shallow.All_Method(m', tr.post) // FIXME Deep
        ensures tr.rel(m.methodBody, m'.methodBody)
      {
        match m {
          case Method(CompileName, methodBody) =>
            Method(CompileName, tr.f(methodBody))
        }
      }

      function method {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
        requires Shallow.All_Program(p, tr.f.requires)
        ensures Shallow.All_Program(p', tr.post)
        ensures tr.rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
      {
        match p {
          case Program(mainMethod) => Program(Map_Method(mainMethod, tr))
        }
      }
    }

    module BottomUp {
      import DCC = DafnyCompilerCommon
      import opened DCC.AST
      import opened Lib
      import opened DCC.Predicates
      import opened Transformer
      import Shallow

      // This predicate gives us the conditions for which, if we deeply apply `f` to all
      // the children of an expression, then the resulting expression satisfies the pre
      // of `f` (i.e., we can call `f` on it).
      // 
      // Given `e`, `e'`, if:
      // - `e` and `e'` have the same constructor
      // - `e` satisfies the pre of `f`
      // - all the children of `e'` deeply satisfy the post of `f`
      // Then:
      // - `e'` satisfies the pre of `f`
      predicate MapChildrenPreservesPre(f: Expr --> Expr, post: Expr -> bool) {
        (forall e, e' ::
           (&& Exprs.ConstructorsMatch(e, e')
            && f.requires(e)
            && Deep.AllChildren_Expr(e', post)) ==> f.requires(e'))
       }

      // This predicate gives us the conditions for which, if we deeply apply `f` to an
      // expression, the resulting expression satisfies the postcondition we give for `f`.
      // 
      // Given `e`, if:
      // - all the children of `e` deeply satisfy the post of `f`
      // - `e` satisfies the pre of `f`
      // Then:
      // - `f(e)` deeply satisfies the post of `f`
      predicate TransformerMatchesPrePost(f: Expr --> Expr, post: Expr -> bool) {
        forall e: Expr | Deep.AllChildren_Expr(e, post) && f.requires(e) ::
          Deep.All_Expr(f(e), post)
      }

      // TODO: add comment
      predicate TransformerPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool) {
        (forall e, e' ::
           (&& Exprs.ConstructorsMatch(e, e')
            && f.requires(e')
            && |e'.Children()| == |e.Children()|
            && forall i:nat | i < |e.Children()| :: rel(e.Children()[i], e'.Children()[i]))
            ==> rel(e, f(e')))
      }
      
      // Predicate for ``BottomUpTransformer``
      predicate IsBottomUpTransformer(f: Expr --> Expr, post: Expr -> bool, rel: (Expr,Expr) -> bool) {
        && TransformerMatchesPrePost(f, post)
        && MapChildrenPreservesPre(f, post)
        && TransformerPreservesRel(f, rel)
      }

      // Identity bottom-up transformer: we need it only because we need a witness when
      // defining ``BottomUpTransformer``, to prove that the type is inhabited.
      const IdentityTransformer: ExprTransformer :=
        TR(d => d, _ => true, (_,_) => true)

      lemma IdentityMatchesPrePost()
        ensures TransformerMatchesPrePost(IdentityTransformer.f, IdentityTransformer.post)
      { }

      lemma IdentityPreservesPre()
        ensures MapChildrenPreservesPre(IdentityTransformer.f, IdentityTransformer.post)
      { }

      lemma IdentityPreservesRel()
        ensures TransformerPreservesRel(IdentityTransformer.f, IdentityTransformer.rel)
      { }

      // A bottom-up transformer, i.e.: a transformer we can recursively apply bottom-up to
      // an expression, and get the postcondition we expect on the resulting expression.
      type BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.post, tr.rel)
        witness (IdentityMatchesPrePost();
                 IdentityPreservesPre();
                 IdentityPreservesRel();
                 IdentityTransformer)

      // Apply a transformer bottom-up on the children of an expression.
      function method {:vcs_split_on_every_assert} MapChildren_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 0
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.AllChildren_Expr(e', tr.post)
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
            Transformer.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Apply(aop, exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'

          // Statements
          case Block(exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Transformer.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Block(exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'
          case If(cond, thn, els) =>
            var e' := Expr.If(Map_Expr(cond, tr), Map_Expr(thn, tr), Map_Expr(els, tr));
            assert Exprs.ConstructorsMatch(e, e');
            e'
        }
      }

      // Apply a transformer bottom-up on an expression.
      function method Map_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 1
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.All_Expr(e', tr.post)
      {
        Deep.AllImpliesChildren(e, tr.f.requires);
        tr.f(MapChildren_Expr(e, tr))
      }

      // Given a bottom-up transformer tr, return a transformer which applies tr in a bottom-up
      // manner.
      function method Map_Expr_Transformer(tr: BottomUpTransformer) : (tr': ExprTransformer)
      {
        var tr': Transformer'<Expr, Expr> :=
          TR(e requires Deep.All_Expr(e, tr.f.requires) => Map_Expr(e, tr),
             e' => Deep.All_Expr(e', tr.post),
             tr.rel);
        assume HasValidRel(tr'); // TODO: prove
        tr'
      }

      // Apply a transformer to a method, in a bottom-up manner.
      function method {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) : (m': Method)
        requires Deep.All_Method(m, tr.f.requires)
        ensures Deep.All_Method(m', tr.post)
        ensures tr.rel(m.methodBody, m'.methodBody)
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      // Apply a transformer to a program, in a bottom-up manner.
      function method {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) : (p': Program)
        requires Deep.All_Program(p, tr.f.requires)
        ensures Deep.All_Program(p', tr.post)
        ensures tr.rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
      {
        Shallow.Map_Program(p, Map_Expr_Transformer(tr))
      }
    }
  }

  module EliminateNegatedBinops {
    import DCC = DafnyCompilerCommon
    import Lib
    import opened DCC.AST
    import opened Lib.Datatypes
    import opened Rewriter.BottomUp

    import opened DCC.Predicates
    import opened Transformer

    // Auxiliarly function (no postcondition): flip the negated binary operations
    // (of the form "not binop(...)") to the equivalent non-negated operations ("binop(...)").
    // Ex.: `neq` ~~> `eq`
    function method FlipNegatedBinop'(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
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
      FlipNegatedBinop'(op)
    }

    predicate method IsNegatedBinop(op: BinaryOps.BinaryOp) {
      FlipNegatedBinop'(op) != op
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

    // function method Tr_Expr1(e: Exprs.T) : (e': Exprs.T)
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

    predicate Tr_Expr_Post(e: Exprs.T) {
      NotANegatedBinopExpr(e)
    }

    predicate Tr_Expr_Rel(e: Exprs.T, e': Exprs.T) {
      true
    }

    function method Tr_Expr_Shallow(e: Exprs.T) : (e': Exprs.T)
      ensures Tr_Expr_Post(e')
    {
      match e {
        case Apply(Eager(BinaryOp(op)), es) =>
          if IsNegatedBinop(op) then
            var flipped := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), es);
            Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [flipped])
          else
            e
        case _ => e
      }
    }

    lemma TrMatchesPrePost()
      ensures TransformerMatchesPrePost(Tr_Expr_Shallow, Tr_Expr_Post)
    {}

    lemma TrPreservesPre()
      ensures MapChildrenPreservesPre(Tr_Expr_Shallow,Tr_Expr_Post)
    {}

    lemma TrPreservesRel()
      ensures TransformerPreservesRel(Tr_Expr_Shallow,Tr_Expr_Rel)
    {}

    const Tr_Expr : BottomUpTransformer :=
      ( TrMatchesPrePost();
        TrPreservesPre();
        TrPreservesRel();
        TR(Tr_Expr_Shallow,
           Tr_Expr_Post,
           Tr_Expr_Rel))

    // TODO: remove
    function method Apply_Expr_direct(e: Exprs.T) : (e': Exprs.T)
      requires Deep.All_Expr(e, Exprs.WellFormed)
      ensures Deep.All_Expr(e', NotANegatedBinopExpr)
      ensures Deep.All_Expr(e', Exprs.WellFormed)
    {
      Deep.AllImpliesChildren(e, Exprs.WellFormed);
      match e {
        case Var(_) => e
        case Literal(lit_) => e
        case Abs(vars, body) => Exprs.Abs(vars, Apply_Expr_direct(body))
        case Apply(Eager(BinaryOp(bop)), exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => Apply_Expr_direct(e), exprs);
          Transformer.Map_All_IsMap(e requires e in exprs => Apply_Expr_direct(e), exprs);
          if IsNegatedBinop(bop) then
            var e'' := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(bop))), exprs');
            var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [e'']);
            e'
          else
            Expr.Apply(Exprs.Eager(Exprs.BinaryOp(bop)), exprs')
        case Apply(aop, exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => Apply_Expr_direct(e), exprs);
          Transformer.Map_All_IsMap(e requires e in exprs => Apply_Expr_direct(e), exprs);
          Expr.Apply(aop, exprs')

        case Block(exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => Apply_Expr_direct(e), exprs);
          Transformer.Map_All_IsMap(e requires e in exprs => Apply_Expr_direct(e), exprs);
          Expr.Block(exprs')
        case If(cond, thn, els) =>
          Expr.If(Apply_Expr_direct(cond),
                  Apply_Expr_direct(thn),
                  Apply_Expr_direct(els))
      }
    }

    function method Apply(p: Program) : (p': Program)
      requires Deep.All_Program(p, Tr_Expr.f.requires)
      ensures Deep.All_Program(p', Tr_Expr_Post)
      ensures Tr_Expr_Rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
    {
      Map_Program(p, Tr_Expr)
    }
  }
}
