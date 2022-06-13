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

    function {:verify false} IsMap<T(!new), T'>(f: T --> T') : T' -> bool {
      y => exists x | f.requires(x) :: y == f(x)
    }

    lemma {:verify false} Map_All_IsMap<A, B>(f: A --> B, xs: seq<A>)
      requires forall a | a in xs :: f.requires(a)
      ensures Seq.All(IsMap(f), Seq.Map(f, xs))
    {}

    lemma {:verify false} Map_All_PC<A, B>(f: A --> B, P: B -> bool, xs: seq<A>)
      requires forall a | a in xs :: f.requires(a)
      requires forall a | a in xs :: P(f(a))
      ensures Seq.All(P, Seq.Map(f, xs))
    {}

    predicate {:verify false} Map_All_Rel<A(!new), B>(f: A --> B, rel: (A,B) -> bool, xs: seq<A>, ys: seq<B>)
      requires |xs| == |ys|
      requires forall a | a in xs :: f.requires(a)
      requires forall a | a in xs :: rel(a, f(a))
    {
      if xs == [] then true
      else
        rel(xs[0], ys[0]) && Map_All_Rel(f, rel, xs[1..], ys[1..])
    }

    predicate {:verify false} All_Rel_Forall<A, B>(rel: (A,B) -> bool, xs: seq<A>, ys: seq<B>)
    {
      && |xs| == |ys|
      && forall i | 0 <= i < |xs| :: rel(xs[i], ys[i])
    }

    // TODO: remove?
    function method {:verify false} {:opaque} MapWithPost_old<A, B>(f: A ~> B, ghost post: B -> bool, xs: seq<A>) : (ys: seq<B>)
      reads f.reads
      requires forall a | a in xs :: f.requires(a)
      requires forall a | a in xs :: post(f(a))
      ensures |ys| == |xs|
      ensures forall i | 0 <= i < |xs| :: ys[i] == f(xs[i])
      ensures forall y | y in ys :: post(y)
      ensures Seq.All(post, ys)
      //ensures Map_All_Rel(f, rel, xs, ys)
    {
      Seq.Map(f, xs)
    }

    function method {:verify false} {:opaque} MapWithPost<A(!new), B>(
      f: A ~> B, ghost post: B -> bool, ghost rel: (A,B) -> bool, xs: seq<A>) : (ys: seq<B>)
      reads f.reads
      requires forall a | a in xs :: f.requires(a)
      requires forall a | a in xs :: post(f(a))
      requires forall a | a in xs :: rel(a, f(a))
      ensures |ys| == |xs|
      ensures forall i | 0 <= i < |xs| :: ys[i] == f(xs[i])
      ensures forall y | y in ys :: post(y)
      ensures Seq.All(post, ys)
      ensures forall i | 0 <= i < |xs| :: rel(xs[i], ys[i])
      //ensures Map_All_Rel(f, rel, xs, ys)
    {
      Seq.Map(f, xs)
    }

    datatype {:verify false} Transformer'<!A, !B> =
      TR(f: A --> B, ghost post: B -> bool, ghost rel: (A,B) -> bool)

    predicate {:verify false} HasValidPost<A(!new), B>(tr: Transformer'<A, B>) {
      forall a: A :: tr.f.requires(a) ==> tr.post(tr.f(a))
    }

    predicate {:verify false} HasValidRel<A(!new), B(0)>(tr: Transformer'<A, B>) {
      forall a: A :: tr.f.requires(a) ==> tr.rel(a, tr.f(a))
    }

    type {:verify false} Transformer<!A(!new), !B(0)> = tr: Transformer'<A, B>
      | HasValidPost(tr) && HasValidRel(tr)
      witness *

    type {:verify false} ExprTransformer = Transformer<Expr, Expr>

    lemma {:verify false} Map_All_TR<A(!new), B(00)>(tr: Transformer<A, B>, ts: seq<A>)
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

      function method {:verify false} {:opaque} Map_Method(m: Method, tr: ExprTransformer) : (m': Method)
        requires Shallow.All_Method(m, tr.f.requires)
        ensures Shallow.All_Method(m', tr.post) // FIXME Deep
        ensures tr.rel(m.methodBody, m'.methodBody)
      {
        match m {
          case Method(CompileName, methodBody) =>
            Method (CompileName, tr.f(methodBody))
        }
      }

      function method {:verify false} {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
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
      predicate {:verify false} MapChildrenPreservesPre(f: Expr --> Expr, post: Expr -> bool) {
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
      predicate {:verify false} TransformerMatchesPrePost(f: Expr --> Expr, post: Expr -> bool) {
        forall e: Expr | Deep.AllChildren_Expr(e, post) && f.requires(e) ::
          Deep.All_Expr(f(e), post)
      }

      // TODO: add comment
      predicate {:verify false} TransformerPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool) {
        (forall e, e' ::
           (&& Exprs.ConstructorsMatch(e, e')
            && f.requires(e')
            //&& |e'.Children()| == |e.Children()|
            //&& forall i:nat | i < |e.Children()| :: rel(e.Children()[i], e'.Children()[i]))
            && All_Rel_Forall(rel, e.Children(), e'.Children()))
            ==> rel(e, f(e')))
      }
      
      // Predicate for ``BottomUpTransformer``
      predicate {:verify false} IsBottomUpTransformer(f: Expr --> Expr, post: Expr -> bool, rel: (Expr,Expr) -> bool) {
        && TransformerMatchesPrePost(f, post)
        && MapChildrenPreservesPre(f, post)
        && TransformerPreservesRel(f, rel)
      }

      // Identity bottom-up transformer: we need it only because we need a witness when
      // defining ``BottomUpTransformer``, to prove that the type is inhabited.
      const {:verify false} IdentityTransformer: ExprTransformer :=
        TR(d => d, _ => true, (_,_) => true)

      lemma {:verify false} IdentityMatchesPrePost()
        ensures TransformerMatchesPrePost(IdentityTransformer.f, IdentityTransformer.post)
      { }

      lemma {:verify false} IdentityPreservesPre()
        ensures MapChildrenPreservesPre(IdentityTransformer.f, IdentityTransformer.post)
      { }

      lemma {:verify false} IdentityPreservesRel()
        ensures TransformerPreservesRel(IdentityTransformer.f, IdentityTransformer.rel)
      { }
      
      // A bottom-up transformer, i.e.: a transformer we can recursively apply bottom-up to
      // an expression, and get the postcondition we expect on the resulting expression.
      type {:verify false} BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.post, tr.rel)
        witness (IdentityMatchesPrePost();
                 IdentityPreservesPre();
                 IdentityPreservesRel();
                 IdentityTransformer)

      // Apply a transformer bottom-up on the children of an expression.
      function method {:verify false} {:vcs_split_on_every_assert} MapChildren_Expr(e: Expr, tr: BottomUpTransformer) :
        (e': Expr)
        decreases e, 0
        requires Deep.AllChildren_Expr(e, tr.f.requires)
        ensures Deep.AllChildren_Expr(e', tr.post)
        ensures Exprs.ConstructorsMatch(e, e')
        ensures All_Rel_Forall(tr.rel, e.Children(), e'.Children())
      {
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
      function method {:verify false} Map_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 1
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.All_Expr(e', tr.post)
      {
        Deep.AllImpliesChildren(e, tr.f.requires);
        tr.f(MapChildren_Expr(e, tr))
      }

      // Auxiliary function
      // TODO: remove?
      function method {:verify false} MapChildren_Expr_Transformer'(tr: BottomUpTransformer) :
        (tr': Transformer'<Expr,Expr>) {
        TR(e requires Deep.AllChildren_Expr(e, tr.f.requires) => MapChildren_Expr(e, tr),
           e' => Deep.AllChildren_Expr(e', tr.post),
           tr.rel)
      }

      // We can write aggregated statements only in lemmas.
      // This forces me to cut this definition into pieces...
      function method {:verify false} Map_Expr_Transformer'(tr: BottomUpTransformer) : (tr': Transformer'<Expr,Expr>) {
        TR(e requires Deep.All_Expr(e, tr.f.requires) => Map_Expr(e, tr),
           e' => Deep.All_Expr(e', tr.post),
           tr.rel)
      }

      lemma {:verify false} {:vcs_split_on_every_assert} Map_Expr_Transformer'_Lem(tr: BottomUpTransformer)
        ensures HasValidRel(Map_Expr_Transformer'(tr))
      {
        var tr' := Map_Expr_Transformer'(tr);
        forall e:Expr
          ensures tr'.f.requires(e) ==> tr.rel(e, tr'.f(e)) {
          if !(tr'.f.requires(e)) {}
          else {
            var e2 := tr'.f(e);
            match e {
              case Var(_) => {}
              case Literal(_) => {}
              case Abs(vars, body) =>
                assert tr.rel(e, tr'.f(e));
              case Apply(applyOp, args) =>
                assert tr.rel(e, tr'.f(e));
              case Block(stmts) =>
                assert tr.rel(e, tr'.f(e));
              case If(cond, thn, els) => {
                assert tr.rel(e, tr'.f(e));
              }
            }
          }
        }
      }

      // Given a bottom-up transformer tr, return a transformer which applies tr in a bottom-up
      // manner.
      function method {:verify false} Map_Expr_Transformer(tr: BottomUpTransformer) : (tr': ExprTransformer)
      {
        var tr': Transformer'<Expr,Expr> := Map_Expr_Transformer'(tr);
        Map_Expr_Transformer'_Lem(tr);
        tr'
      }

      // Apply a transformer to a method, in a bottom-up manner.
      function method {:verify false} {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) : (m': Method)
        requires Deep.All_Method(m, tr.f.requires)
        ensures Deep.All_Method(m', tr.post)
        ensures tr.rel(m.methodBody, m'.methodBody)
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      // Apply a transformer to a program, in a bottom-up manner.
      function method {:verify false} {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) : (p': Program)
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
    import Lib.Debug
    import opened DCC.AST
    import opened Lib.Datatypes
    import opened Rewriter.BottomUp

    import opened DCC.Predicates
    import opened Transformer
    import opened Interp
    import opened Values

    // Auxiliarly function (no postcondition): flip the negated binary operations
    // (of the form "not binop(...)") to the equivalent non-negated operations ("binop(...)").
    // Ex.: `neq` ~~> `eq`
    function method {:verify false} FlipNegatedBinop'(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
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

    function method {:verify false} FlipNegatedBinop(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
      ensures !IsNegatedBinop(op')
    {
      FlipNegatedBinop'(op)
    }

    predicate method {:verify false} IsNegatedBinop(op: BinaryOps.BinaryOp) {
      FlipNegatedBinop'(op) != op
    }

    predicate method {:verify false} IsNegatedBinopExpr(e: Exprs.T) {
      match e {
        case Apply(Eager(BinaryOp(op)), _) => IsNegatedBinop(op)
        case _ => false
      }
    }

    predicate {:verify false} NotANegatedBinopExpr(e: Exprs.T) {
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

    predicate {:verify false} Tr_Expr_Post(e: Exprs.T) {
      NotANegatedBinopExpr(e)
    }
    
    // Interpretation results are "similar".
    // We might want to be a bit more precise, especially with regards to the "out of fuel" error.
    predicate {:verify false} SameResult<T(0)>(res: InterpResult<T>, res': InterpResult<T>) {
      match (res, res') {
        case (Success(Return(v,ctx)), Success(Return(v',ctx'))) =>
          && v == v'
          && ctx == ctx'
        case (Failure(_), Failure(_)) =>
          true
        case _ =>
          false
      }
    }

    predicate {:verify true} SamePureResult<T(0)>(res: PureInterpResult<T>, res': PureInterpResult<T>) {
      match (res, res') {
        case (Success(v), Success(v')) =>
          && v == v'
        case (Failure(_), Failure(_)) =>
          true
        case _ =>
          false
      }
    }

    predicate {:verify false} SameSeq1Result(res: InterpResult<WV>, res': InterpResult<seq<WV>>) {
      match (res, res') {
        case (Success(Return(v,ctx)), Success(Return(sv,ctx'))) =>
          && [v] == sv
          && ctx == ctx'
        case (Failure(err), Failure(err')) =>
          err == err'
        case _ =>
          false
      }
    }

    // Auxiliary lemma: evaluating a sequence of one expression is equivalent to evaluating the single expression.
    lemma {:verify false} InterpExprs1_Lem(e: Expr, fuel: nat, ctx: State)
      requires SupportsInterp(e)
      ensures forall e' | e' in [e] :: SupportsInterp(e')
      ensures SameSeq1Result(InterpExpr(e, fuel, ctx), InterpExprs([e], fuel, ctx))
    {
      var res := InterpExpr(e, fuel, ctx);
      var sres := InterpExprs([e], fuel, ctx);

      match InterpExpr(e, fuel, ctx) {
        case Success(Return(v, ctx1)) => {
          var s := [e];
          var s' := s[1..];
          assert s' == [];
          assert InterpExprs(s', fuel, ctx1) == Success(Return([], ctx1));
          assert [v] + [] == [v];
        }
        case Failure(_) => {}
      }
    }

    // TODO: move
    predicate {:verify false} SameInterp(e: Exprs.T, e': Exprs.T) {
      SupportsInterp(e) ==>
      (&& SupportsInterp(e')
       && forall fuel, ctx :: SameResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx)))
    }

    // TODO: move
    // Sometimes, quantifiers are not triggered
    lemma {:verify false} SameInterp_Lem(e: Exprs.T, e': Exprs.T, fuel: nat, ctx: State)
      requires SupportsInterp(e)
      requires SameInterp(e, e')
      ensures SupportsInterp(e')
      ensures SameResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx))
    {}

    // TODO: move - TODO: remove?
    predicate {:verify false} Tr_SameInterp(f: Expr --> Expr, rel: (Expr, Expr) -> bool) {
      forall e | f.requires(e) :: rel(e, f(e)) ==> SameInterp(e, f(e))
    }

    // TODO: move
    lemma {:verify false} All_Rel_Forall_SameInterp_SameResult_Lem(es: seq<Expr>, es': seq<Expr>, fuel: nat, ctx: State)
      requires forall e | e in es :: SupportsInterp(e)
      requires All_Rel_Forall(SameInterp, es, es')
      ensures forall e | e in es' :: SupportsInterp(e)
      ensures SameResult(InterpExprs(es, fuel, ctx), InterpExprs(es', fuel, ctx))
    {
      if es == [] {}
      else {
        // Evaluate the first expression in the sequence
        match InterpExpr(es[0], fuel, ctx) {
          case Success(Return(v, ctx1)) => {
            var res1: InterpResult<WV> := InterpExpr(es'[0], fuel, ctx);
            assert res1.Success?;

            // TODO: the following statement generates the error:
            // "value does not satisfy the subset constraints of 'WV' (dafny)"
            //var Success(Return(v', ctx1')) := res1;
            //assert v' == v;
            //assert ctx1' == ctx1;

            // Evaluate the rest of the sequence
            All_Rel_Forall_SameInterp_SameResult_Lem(es[1..], es'[1..], fuel, ctx1);
          }
          case Failure(_) => {}
        }
      }
    }

    lemma {:verify false} Map_PairOfMapDisplaySeq_Lem(e: Expr, e': Expr, argvs: seq<WV>)
      ensures SamePureResult(Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv)),
                             Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e', argv)))
    {
      if argvs == [] {
        
      }
      else {
        var argv := argvs[0];
        assert SamePureResult(PairOfMapDisplaySeq(e, argv), PairOfMapDisplaySeq(e', argv));
        reveal Seq.MapResult();
        Map_PairOfMapDisplaySeq_Lem(e, e', argvs[1..]);
      }
    }

    // TODO: move
    lemma {:verify false} InterpMapDisplay_SameArgs_Lem(e: Expr, e': Expr, argvs: seq<WV>)
      ensures SamePureResult(InterpMapDisplay(e, argvs), InterpMapDisplay(e', argvs)) {
        Map_PairOfMapDisplaySeq_Lem(e, e', argvs);
    }

    // TODO: move
    lemma {:verify true} Tr_SameInterp_Expr_Lem(f: Expr --> Expr)
      requires forall e | f.requires(e) :: SameInterp(e, f(e))
      //requires Tr_SameInterp(f,rel)
      //requires TransformerPreservesRel(f,rel)
      ensures TransformerPreservesRel(f, SameInterp)
    {
      forall e, e' |
        && Exprs.ConstructorsMatch(e, e')
        && f.requires(e')
        && All_Rel_Forall(SameInterp, e.Children(), e'.Children())
        && SupportsInterp(e) // Constraining a bit
        ensures SameInterp(e, f(e'))
        {
          forall exprs, exprs', fuel, ctx | (forall e | e in exprs :: SupportsInterp(e)) && All_Rel_Forall(SameInterp, exprs, exprs')
            ensures forall e | e in exprs' :: SupportsInterp(e)
            ensures SameResult(InterpExprs(exprs, fuel, ctx), InterpExprs(exprs', fuel, ctx)) {
              All_Rel_Forall_SameInterp_SameResult_Lem(exprs, exprs', fuel, ctx);
          }

          match e {
            case Var(_) => {
              assert SameInterp(e, e');
            }
            case Literal(lit_) => {
              assert SameInterp(e, e');
            }
            case Abs(vars, body) => {
              assume SupportsInterp(e'); // TODO
              assume SameInterp(e, e'); // TODO
            }
            case Apply(Eager(op), exprs) => {
              assert SupportsInterp(e');

              var Apply(Eager(op'), exprs') := e';
              assert op' == op;
              assert All_Rel_Forall(SameInterp, exprs, exprs');
              forall fuel, ctx
                ensures SameResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx))
              {
                var res := InterpExpr(e, fuel, ctx);
                var res' := InterpExpr(e', fuel, ctx);

                // The arguments evaluate to similar results
                assert SameResult(InterpExprs(exprs, fuel, ctx), InterpExprs(exprs', fuel, ctx));
                
                // Check that the applications also evaluate to similar results
                match InterpExprs(exprs, fuel, ctx) {
                  case Success(Return(vs:seq<WV>, ctx1)) => {

                    // TODO: this doesn't work for some reason:
                    // var Success(Return(vs':seq<WV>, ctx1')) := InterpExprs(exprs', fuel, ctx);
                    assert InterpExprs(exprs', fuel, ctx).Success?;
                    var vs' := InterpExprs(exprs', fuel, ctx).value.ret;
                    var ctx1' := InterpExprs(exprs', fuel, ctx).value.ctx;
                    assert vs' == vs;
                    assert ctx1' == ctx1;
                    
                    match op {
                      case UnaryOp(op: UnaryOp) => {
                        assert SameResult(res, res');
                      }
                      case BinaryOp(bop: BinaryOp) => {
                        assert SameResult(res, res');
                      }
                      case TernaryOp(top: TernaryOp) => {
                        assert SameResult(res, res');
                      }
                      case Builtin(Display(ty)) => {
                        assert res == LiftPureResult(ctx1, InterpDisplay(e, ty.kind, vs));
                        assert res' == LiftPureResult(ctx1, InterpDisplay(e', ty.kind, vs));
                        match ty.kind {
                          case Map(_) => {
                            InterpMapDisplay_SameArgs_Lem(e, e', vs);
                            assert SameResult(res, res');
                          }
                          case _ => {
                            assert SameResult(res, res');
                          }
                        }
                      }
                      case FunctionCall() => {
                        var fn := vs[0];
                        var argvs := vs[1..];
                        assert res == LiftPureResult(ctx1, InterpFunctionCall(e, fuel, fn, argvs));
                        assert res' == LiftPureResult(ctx1, InterpFunctionCall(e', fuel, fn, argvs));
                        assert SameResult(res, res');
                      }
                    }
                  }
                  case Failure(_) => {
                    assert SameResult(res, res');
                  }
                }
              }

              assert SameInterp(e, e');
            }
            case Apply(Lazy(op), exprs) => {
              forall fuel, ctx
                ensures SameResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx))
              {
                var res := InterpExpr(e, fuel, ctx);
                var res' := InterpExpr(e', fuel, ctx);

                assert res == InterpLazy(e, fuel, ctx);
                assert res' == InterpLazy(e', fuel, ctx);

                var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
                var op', e0', e1' := e'.aop.lOp, e'.args[0], e'.args[1];
                assert op == op';

                SameInterp_Lem(e0, e0', fuel, ctx);
                var res0 := InterpExprWithType(e0, Type.Bool, fuel, ctx);
                var res0' := InterpExprWithType(e0', Type.Bool, fuel, ctx);
                assert SameResult(res0, res0');
                
                match res0 {
                  case Success(Return(v0, ctx0)) => {
                    SameInterp_Lem(e1, e1', fuel, ctx0);
                    assert SameResult(InterpExprWithType(e1, Type.Bool, fuel, ctx0), InterpExprWithType(e1', Type.Bool, fuel, ctx0)); // Fails without this
                    assert SameResult(res, res');
                  }
                  case Failure(_) => {
                    assert res.Failure?;
                    assert res0'.Failure?; // Fails without this
                    assert SameResult(res, res');
                  }
                }
                assume SameResult(res, res');
              }
              
              assert SameInterp(e, e');
            }
            case Block(exprs) => {
              assert SameInterp(e, e');
            }
            case If(cond, thn, els) => {
              var If(cond', thn', els') := e';

              assert cond == e.Children()[0];
              assert thn == e.Children()[1];
              assert els == e.Children()[2];

              assert cond' == e'.Children()[0];
              assert thn' == e'.Children()[1];
              assert els' == e'.Children()[2];

              assert SameInterp(cond, cond');
              assert SameInterp(thn, thn');
              assert SameInterp(els, els');

              assert SupportsInterp(e');

              forall fuel, ctx
                ensures SameResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx)) {
                  var res := InterpExpr(e, fuel, ctx);
                  var res' := InterpExpr(e', fuel, ctx);

                  var res1 := InterpExprWithType(cond, Type.Bool, fuel, ctx);
                  var res1' := InterpExprWithType(cond', Type.Bool, fuel, ctx);

                  SameInterp_Lem(cond, cond', fuel, ctx); // Below assert fails without this lemma
                  assert SameResult(res1, res1');

                  match res1 {
                    case Success(Return(condv, ctx1)) => {
                      var condv' := res1'.value.ret;
                      var ctx1' := res1'.value.ctx;

                      assert condv' == condv;
                      assert ctx1' == ctx1;
                      
                      SameInterp_Lem(thn, thn', fuel, ctx1); // Proof fails without this lemma
                      SameInterp_Lem(els, els', fuel, ctx1); // Proof fails without this lemma
                    }
                    case Failure(_) => {
                      assert InterpExprWithType(cond', Type.Bool, fuel, ctx).Failure?; // Proof fails without this
                      assert SameResult(res, res');
                    }
                  }
              }
              assert SameInterp(e, e');
            }
          }
          assert SameInterp(e, e');
          assert SameInterp(e, f(e'));
        }
    }
    
    predicate {:verify false} Tr_Expr_Rel(e: Exprs.T, e': Exprs.T) {
      SameInterp(e, e')
    }

    function method {:verify false} FlipNegatedBinop_Expr(op: BinaryOp, args: seq<Expr>) : (e':Exprs.T)
      requires IsNegatedBinop(op)
    {
      var flipped := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), args);
      var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [flipped]);
      e'
    }

    lemma {:verify false} FlipNegatedBinop_Expr_Rel_Lem(op: BinaryOp, args: seq<Expr>)
      requires IsNegatedBinop(op)
      ensures (
        var e := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(op)), args);
        var e' := FlipNegatedBinop_Expr(op, args);
        Tr_Expr_Rel(e, e')
      )
    {
      var e := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(op)), args);
      var e' := FlipNegatedBinop_Expr(op, args);
      if SupportsInterp(e) {
        assert SupportsInterp(e');
        // Prove that for every fuel and context, the interpreter returns the same result
        forall fuel, ctx
          ensures SameResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx)) {
          // Start by proving that the flipped binary operation (not wrapped in the "not") returns exactly the
          // opposite result of the non-flipped binary operation.
          var flipped := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), args);

          // Intermediate result: evaluating (the sequence of expressions) `[flipped]` is the same as evaluating (the expression) `flipped`.
          InterpExprs1_Lem(flipped, fuel, ctx);
          assert SameSeq1Result(InterpExpr(flipped, fuel, ctx), InterpExprs([flipped], fuel, ctx));

          match (InterpExpr(e, fuel, ctx), InterpExpr(flipped, fuel, ctx)) {
            case (Success(Return(v,ctx1)), Success(Return(v',ctx1'))) => {
              // Check that the results are the opposite of each other
              assert v.Bool?;
              assert v'.Bool?;
              assert v.b == !v'.b;
              assert ctx1 == ctx1';

              // Prove that if we add the "not", we get the expected result
              assert InterpExpr(e', fuel, ctx) == LiftPureResult(ctx1', InterpUnaryOp(e', UnaryOps.BoolNot, v'));
              assert InterpUnaryOp(e', UnaryOps.BoolNot, v') == Success(Bool(!v'.b));
              assert InterpExpr(e, fuel, ctx) == InterpExpr(e', fuel, ctx);
            }
            case (Failure(err), Failure(err')) => {
              // We don't have the fact that `err == err'` (investigate why)
            }
            case _ => {
              assert false;
            }
          }
          assert SameResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx));
        }
      }
      else {
        assert Tr_Expr_Rel(e, e');
      }
    }

    function method {:verify false} Tr_Expr_Shallow(e: Exprs.T) : (e': Exprs.T)
      ensures Tr_Expr_Post(e')
      ensures Tr_Expr_Rel(e, e')
    {
      match e {
        case Apply(Eager(BinaryOp(op)), args) =>
          if IsNegatedBinop(op) then
            var e' := FlipNegatedBinop_Expr(op, args);
            FlipNegatedBinop_Expr_Rel_Lem(op, args);
            e'
          else
            e
        case _ => e
      }
    }

    lemma {:verify false} TrMatchesPrePost()
      ensures TransformerMatchesPrePost(Tr_Expr_Shallow, Tr_Expr_Post)
    {}

    lemma {:verify false} TrPreservesPre()
      ensures MapChildrenPreservesPre(Tr_Expr_Shallow,Tr_Expr_Post)
    {}

    lemma {:verify false} TrPreservesRel()
      ensures TransformerPreservesRel(Tr_Expr_Shallow,Tr_Expr_Rel)
    {
      var f := Tr_Expr_Shallow;
      var rel := Tr_Expr_Rel;
      Tr_SameInterp_Expr_Lem(f);
    }

    const {:verify false} Tr_Expr : BottomUpTransformer :=
      ( TrMatchesPrePost();
        TrPreservesPre();
        TrPreservesRel();
        TR(Tr_Expr_Shallow,
           Tr_Expr_Post,
           Tr_Expr_Rel))

    // TODO: remove
    function method {:verify false} Apply_Expr_direct(e: Exprs.T) : (e': Exprs.T)
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

    function method {:verify false} Apply(p: Program) : (p': Program)
      requires Deep.All_Program(p, Tr_Expr.f.requires)
      ensures Deep.All_Program(p', Tr_Expr_Post)
      ensures Tr_Expr_Rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
    {
      Map_Program(p, Tr_Expr)
    }
  }
}
