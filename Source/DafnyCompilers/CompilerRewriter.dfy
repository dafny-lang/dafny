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
      
      predicate {:verify false} RelCanBeMapLifted(rel: (Expr, Expr) -> bool)
      // In many situations, the binary relation between the input and the output is transitive
      // and can be lifted through the map function.
      {
        (forall e, e' ::
           (&& Exprs.ConstructorsMatch(e, e')
            && All_Rel_Forall(rel, e.Children(), e'.Children()))
            ==> rel(e, e'))
      }

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

      function method {:verify false} Map_Expr_Transformer(tr: BottomUpTransformer) : (tr': ExprTransformer)
      // Given a bottom-up transformer tr, return a transformer which applies tr in a bottom-up
      // manner.
      {
        var tr': Transformer'<Expr,Expr> := Map_Expr_Transformer'(tr);
        Map_Expr_Transformer'_Lem(tr);
        tr'
      }

      function method {:verify false} {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) : (m': Method)
        requires Deep.All_Method(m, tr.f.requires)
        ensures Deep.All_Method(m', tr.post)
        ensures tr.rel(m.methodBody, m'.methodBody)
      // Apply a transformer to a method, in a bottom-up manner.
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      function method {:verify false} {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) : (p': Program)
      // Apply a transformer to a program, in a bottom-up manner.
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

    function method {:verify false} FlipNegatedBinop'(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
    // Auxiliarly function (no postcondition): flip the negated binary operations
    // (of the form "not binop(...)") to the equivalent non-negated operations ("binop(...)").
    // Ex.: `neq` ~~> `eq`
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

    predicate {:verify false} GEqInterpResult<T(0)>(
      eq_ctx: (State,State) -> bool, eq_value: (T,T) -> bool, res: InterpResult<T>, res': InterpResult<T>)
    // Interpretation results are equivalent.
    // "G" stands for "generic" (TODO: update)
    // TODO: be a bit more precise in the error case, especially in case of "out of fuel".
    {
      match (res, res') {
        case (Success(Return(v,ctx)), Success(Return(v',ctx'))) =>
          && eq_ctx(ctx, ctx')
          && eq_value(v, v')
        case (Failure(_), Failure(_)) =>
          true
        case _ =>
          false
      }
    }

    predicate method {:verify false} GEqCtx(
      eq_value: (WV,WV) -> bool, ctx: Context, ctx': Context)
      requires WellFormedContext(ctx)
      requires WellFormedContext(ctx')
    {
      && ctx.Keys == ctx'.Keys
      && (forall x | x in ctx.Keys :: eq_value(ctx[x], ctx'[x])) 
    }

    predicate method {:verify false} GEqState(
      eq_value: (WV,WV) -> bool, ctx: State, ctx': State)
    {
      GEqCtx(eq_value, ctx.locals, ctx'.locals)
    }

    function method {:verify false} Mk_EqState(eq_value: (WV,WV) -> bool): (State,State) -> bool
    {
      (ctx, ctx') => GEqState(eq_value, ctx, ctx')
    }

    function method {:opaque} {:verify false} InterpCallFunctionBody(fn: WV, fuel: nat, argvs: seq<WV>)
      : (r: PureInterpResult<WV>)
      requires fn.Closure?
      requires |fn.vars| == |argvs|
    // Call a function body with some arguments.
    // We introduce this auxiliary function to opacify its content (otherwise ``EqValue_Closure``
    // takes too long to typecheck).
    {
        var ctx := BuildCallState(fn.ctx, fn.vars, argvs);
        var Return(val, ctx) :- InterpExpr(fn.body, fuel, ctx);
        Success(val)
    }

    predicate {:verify false} {:vcs_split_on_every_assert} EqValue(v: WV, v': WV)
      decreases ValueTypeHeight(v) + ValueTypeHeight(v'), 1
    // Equivalence between values.
    // 
    // Two values are equivalent if:
    // - they are not closures and are equal/have equivalent children values
    // - they are closures and, when applied to equivalent inputs, they return equivalent outputs
    //
    // Rk.: we could write the predicate in a simpler manner by using `==` in case the values are not
    // closures, but we prepare the terrain for a more general handling of collections.
    //
    // Rk.: for now, we assume the termination. This function terminates because the size of the
    // type of the values decreases, the interesting case being the closures (see ``EqValue_Closure``).
    // Whenever we find a closure `fn_ty = (ty_0, ..., ty_n) -> ret_ty`, we need to call ``EqValue``
    // on valid inputs (with types `ty_i < fn_ty`) and on its output (with type `ret_ty < fn_ty`).
    //
    // Rk.: I initially wanted to make the definition opaque to prevent context saturation, because
    // in most situations we don't need to know the content of EqValue.
    // However it made me run into the following issue:
    // https://github.com/dafny-lang/dafny/issues/2260
    // As ``EqValue`` appears a lot in foralls, using the `reveal` trick seemed too cumbersome
    // to be a valid option.
    {
      match (v, v') {
        case (Bool(b), Bool(b')) => b == b'
        case (Char(c), Char(c')) => c == c'
        case (Int(i), Int(i')) => i == i'
        case (Real(r), Real(r')) => r == r'
        case (BigOrdinal(o), BigOrdinal(o')) => o == o'
        case (BitVector(width, value), BitVector(width', value')) =>
          && width == width'
          && value == value'
        case (Map(m), Map(m')) =>
          ValueTypeHeight_Children_Lem(v); // For termination
          ValueTypeHeight_Children_Lem(v'); // For termination
          && m.Keys == m'.Keys
          && (forall x | x in m :: EqValue(m[x], m'[x]))
        case (Multiset(ms), Multiset(ms')) =>
          ValueTypeHeight_Children_Lem(v); // For termination
          ValueTypeHeight_Children_Lem(v'); // For termination
          && (forall x :: x in ms <==> x in ms')
          && (forall x | x in ms :: ms[x] == ms'[x])
        case (Seq(sq), Seq(sq')) =>
          ValueTypeHeight_Children_Lem(v); // For termination
          ValueTypeHeight_Children_Lem(v'); // For termination
          && |sq| == |sq'|
          && (forall i | 0 <= i < |sq| :: EqValue(sq[i], sq'[i]))
        case (Set(st), Set(st')) =>
          && st == st'
        case (Closure(ctx, vars, body), Closure(ctx', vars', body')) =>
          EqValue_Closure(v, v')

        // DISCUSS: Better way to write this?  Need exhaustivity checking
        case (Bool(b), _) => false
        case (Char(c), _) => false
        case (Int(i), _) => false
        case (Real(r), _) => false
        case (BigOrdinal(o), _) => false
        case (BitVector(width, value), _) => false
        case (Map(m), _) => false
        case (Multiset(ms), _) => false
        case (Seq(sq), _) => false
        case (Set(st), _) => false
        case (Closure(ctx, vars, body), _) => false
      }
    }

    predicate {:verify false} {:opaque} {:vcs_split_on_every_assert} EqValue_Closure(v: WV, v': WV)
      requires v.Closure?
      requires v'.Closure?
      decreases ValueTypeHeight(v) + ValueTypeHeight(v'), 0
    // Equivalence between values: closure case.
    //
    // See ``EqValue``.
    //
    // Rk.: contraty to ``EqValue``, it seems ok to make ``EqValue_Closure`` opaque.
    {
      var Closure(ctx, vars, body) := v;
      var Closure(ctx', vars', body') := v';
      && |vars| == |vars'| // no partial applications are allowed in Dafny
      && (
      forall fuel:nat, argvs: seq<WV>, argvs': seq<WV> |
        && |argvs| == |argvs'| == |vars|
        // We need the argument types to be smaller than the closure types, to prove termination.\
        // In effect, the arguments types should be given by the closure's input types.
        && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs[i]) < ValueTypeHeight(v))
        && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs'[i]) < ValueTypeHeight(v'))
        && (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i])) ::
        var res := InterpCallFunctionBody(v, fuel, argvs);
        var res' := InterpCallFunctionBody(v', fuel, argvs');
        // We can't use naked functions in recursive setting: this forces us to write the expanded
        // match rather than using an auxiliary function like `EqPureInterpResult`.
        match (res, res') {
          case (Success(ov), Success(ov')) =>
            // We need to assume those assertions to prove termination: the value returned by a closure
            // has a type which is smaller than the closure type (its type is given by the closure return
            // type)
            assume ValueTypeHeight(ov) < ValueTypeHeight(v);
            assume ValueTypeHeight(ov') < ValueTypeHeight(v');
            EqValue(ov, ov')
          case (Failure(_), Failure(_)) =>
            true
          case _ =>
            false
        })
    }

    predicate {:verify false} EqState(ctx: State, ctx': State)
    {
      GEqState(EqValue, ctx, ctx')
    }

    predicate {:verify false} EqCtx(ctx: Context, ctx': Context)
      requires WellFormedContext(ctx)
      requires WellFormedContext(ctx')
    {
      GEqCtx(EqValue, ctx, ctx')
    }

    predicate {:verify false} EqInterpResult<T(0)>(
      eq_value: (T,T) -> bool, res: InterpResult<T>, res': InterpResult<T>)
    {
      GEqInterpResult(Mk_EqState(EqValue), eq_value, res, res')
    }

    // If values are equivalent and don't contain functions, they are necessarily equal
    lemma {:verify false} EqValueHasEq_Lem(v: WV, v': WV)
      requires EqValue(v,v')
      requires HasEqValue(v)
      requires HasEqValue(v')
      ensures v == v'
    {
      reveal EqValue_Closure();
    }

    lemma {:verify false} EqValueHasEq_Forall_Lem()
      ensures forall v: WV, v': WV | EqValue(v,v') && HasEqValue(v) && HasEqValue(v') :: v == v'
    {
      forall v: WV, v': WV | EqValue(v,v') && HasEqValue(v) && HasEqValue(v') ensures v == v' {
        EqValueHasEq_Lem(v, v');
      }
    }

    lemma {:verify false} EqValue_Refl_Lem(v: WV)
      ensures EqValue(v, v)
    {
      // TODO: the proof for the closure case is tricky, because we need to show that if
      // we evaluate an expression starting in environments which are equivalent, then the
      // results are equivalent...
      assume EqValue(v, v);
    }

    lemma {:verify false} EqValue_Trans_Lem(v0: WV, v1: WV, v2: WV)
      requires EqValue(v0, v1)
      requires EqValue(v1, v2)
      ensures EqValue(v0, v2)
    {
      // TODO:
      assume EqValue(v0, v2);
    }

    lemma {:verify false} EqValue_Refl_Forall_Lem()
      ensures forall v : WV :: EqValue(v, v)
    {      
      forall v : WV | true
        ensures EqValue(v, v)
      {
        EqValue_Refl_Lem(v);
        assert EqValue(v, v);
      }
    }

    lemma {:verify false} EqState_Refl_Lem(ctx: State)
      ensures EqState(ctx, ctx)
    {
      EqValue_Refl_Forall_Lem();
    }

    lemma {:verify false} EqState_Trans_Lem(ctx0: State, ctx1: State, ctx2: State)
      requires EqState(ctx0, ctx1)
      requires EqState(ctx1, ctx2)
      ensures EqState(ctx0, ctx2)
    {
      forall x | x in ctx0.locals.Keys ensures EqValue(ctx0.locals[x], ctx2.locals[x]) {
        EqValue_Trans_Lem(ctx0.locals[x], ctx1.locals[x], ctx2.locals[x]);
      }
    }

    predicate {:verify false} EqSeq<T(0)>(eq_values: (T,T) -> bool, vs: seq<T>, vs': seq<T>) {
      && |vs| == |vs'|
      && (forall i | 0 <= i < |vs| :: eq_values(vs[i], vs'[i]))
    }

    predicate {:verify false} EqMap<T(0,!new), U(0,!new)>(eq_values: (U,U) -> bool, vs: map<T, U>, vs': map<T, U>) {
      && (forall x :: x in vs <==> x in vs')
      && (forall x | x in vs :: eq_values(vs[x], vs'[x]))
    }

    predicate {:verify false} EqPairs<T(0), U(0)>(same_t: (T,T) -> bool, same_u: (U,U) -> bool, v: (T,U), v': (T,U)) {
      && same_t(v.0, v'.0)
      && same_u(v.1, v'.1)
    }
    
    predicate {:verify false} EqSeqValue(vs: seq<WV>, vs': seq<WV>) {
      EqSeq(EqValue, vs, vs')
    }

    predicate {:verify false} EqMapValue(m: map<EqWV, WV>, m': map<EqWV,WV>) {
      && (forall x :: x in m <==> x in m')
      && (forall x | x in m :: EqValue(m[x], m'[x]))
    }

    predicate {:verify false} EqSeqPairEqValueValue(vs: seq<(EqWV,WV)>, vs': seq<(EqWV,WV)>) {
      EqSeq((v: (EqWV,WV),v': (EqWV,WV)) => EqValue(v.0, v'.0) && EqValue(v.1, v'.1), vs, vs')
    }

    predicate {:verify false} EqEqValue(v: EqWV, v': EqWV) {
      EqValue(v, v')
    }

    predicate {:verify false} EqPairEqValueValue(v: (EqWV,WV), v': (EqWV,WV)) {
      EqPairs(EqEqValue, EqValue, v, v')
    }
    
    // Interpretation results are equivalent.
    // We might want to be a bit more precise, especially with regards to the "out of fuel" error.
    predicate {:verify false} EqValueResult(res: InterpResult<WV>, res': InterpResult<WV>) {
      EqInterpResult(EqValue, res, res')
    }

    predicate {:verify false} EqInterpResultSeqValue(res: InterpResult<seq<WV>>, res': InterpResult<seq<WV>>) {
      EqInterpResult(EqSeqValue, res, res')
    }

    predicate {:verify false} GEqInterpResultSeq(eq: Equivs, res: InterpResult<seq<WV>>, res': InterpResult<seq<WV>>) {
      GEqInterpResult(eq.eq_state, (x, x') => EqSeq(eq.eq_value, x, x'), res, res')
    }
    
    predicate {:verify false} EqPureInterpResult<T(0)>(eq_values: (T,T) -> bool, res: PureInterpResult<T>, res': PureInterpResult<T>) {
      match (res, res') {
        case (Success(v), Success(v')) =>
          eq_values(v, v')
        case (Failure(_), Failure(_)) =>
          true
        case _ =>
          false
      }
    }

    predicate {:verify false} EqPureInterpResultValue(res: PureInterpResult<WV>, res': PureInterpResult<WV>) {
      EqPureInterpResult(EqValue, res, res')
    }

    predicate {:verify false} EqPureInterpResultSeqValue(res: PureInterpResult<seq<WV>>, res': PureInterpResult<seq<WV>>) {
      EqPureInterpResult(EqSeqValue, res, res')
    }

    predicate {:verify false} EqInterpResultSeq1Value(res: InterpResult<WV>, res': InterpResult<seq<WV>>) {
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

    // TODO: move up
    datatype Equivs =
      EQ(eq_value: (WV, WV) -> bool, eq_state: (State, State) -> bool)

    // TODO: move
    predicate {:verify false} GEqInterp(eq: Equivs, e: Exprs.T, e': Exprs.T) {
      SupportsInterp(e) ==>
      (&& SupportsInterp(e')
       && forall fuel, ctx, ctx' | eq.eq_state(ctx, ctx') ::
         GEqInterpResult(eq.eq_state, eq.eq_value,
                         InterpExpr(e, fuel, ctx),
                         InterpExpr(e', fuel, ctx')))
    }

    function {:verify false} Mk_EqInterp(eq: Equivs): (Expr, Expr) -> bool {
      (e, e') => GEqInterp(eq, e, e')
    }

    // TODO: move
    // TODO: change the definition to quantify over equivalent contexts
    // TODO: make opaque?
    predicate {:verify false} EqInterp(e: Exprs.T, e': Exprs.T) {
      GEqInterp(EQ(EqValue, Mk_EqState(EqValue)), e, e')
    }

    lemma {:verify false} InterpExprs1_Lem(e: Expr, fuel: nat, ctx: State)
      requires SupportsInterp(e)
      ensures forall e' | e' in [e] :: SupportsInterp(e')
      ensures EqInterpResultSeq1Value(InterpExpr(e, fuel, ctx), InterpExprs([e], fuel, ctx))
      // Auxiliary lemma: evaluating a sequence of one expression is equivalent to evaluating
      // the single expression.
    {
      reveal InterpExprs();
      var res := InterpExpr(e, fuel, ctx);
      var sres := InterpExprs([e], fuel, ctx);

      match InterpExpr(e, fuel, ctx) {
        case Success(Return(v, ctx1)) => {
          var s := [e];
          var s' := s[1..];
          assert s' == [];
          assert InterpExprs(s', fuel, ctx1) == Success(Return([], ctx1));
          EqState_Refl_Lem(ctx);
          EqValue_Refl_Lem(v);
          assert [v] + [] == [v];
        }
        case Failure(_) => {}
      }
    }

    // TODO: move
    // Sometimes, quantifiers are not triggered
    lemma {:verify false} EqInterp_Lem(e: Exprs.T, e': Exprs.T, fuel: nat, ctx: State, ctx': State)
      requires SupportsInterp(e)
      requires EqInterp(e, e')
      requires EqState(ctx, ctx')
      ensures SupportsInterp(e')
      ensures EqValueResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx'))
    {}

    // TODO: move - TODO: remove?
    predicate {:verify false} Tr_EqInterp(f: Expr --> Expr, rel: (Expr, Expr) -> bool) {
      forall e | f.requires(e) :: rel(e, f(e)) ==> EqInterp(e, f(e))
    }

/*    predicate {:verify false} {:opaque} {:vcs_split_on_every_assert} OEqValue(v: WV, v': WV)
    // Opaque version of ``EqValue`` (having a hard time controling the context, especially
    // when some bugs prevent me from doing so: https://github.com/dafny-lang/dafny/issues/2260).
    // TODO: remove?
    {
      EqValue(v, v')
    }*/

    lemma {:verify false} {:vcs_split_on_every_assert}
      All_Rel_Forall_GEqInterp_GEqInterpResult_Lem(
      eq: Equivs, es: seq<Expr>, es': seq<Expr>, fuel: nat, ctx: State, ctx': State)
      requires forall e | e in es :: SupportsInterp(e)
      requires All_Rel_Forall(Mk_EqInterp(eq), es, es')
      requires eq.eq_state(ctx, ctx')
      ensures forall e | e in es' :: SupportsInterp(e)
      ensures GEqInterpResultSeq(eq, InterpExprs(es, fuel, ctx), InterpExprs(es', fuel, ctx'))
    // Auxiliary lemma: if two sequences contain equivalent expressions, evaluating those two
    // sequences in the same context leads to equivalent results.
    // This lemma is written generically over the equivalence relations over the states and
    // values. We don't do this because it seems elegant: we do this as a desperate attempt
    // to reduce the context size, while we are unable to use the `opaque` attribute on
    // some definitions.
    {
      reveal InterpExprs();

      var res := InterpExprs(es, fuel, ctx);
      var res' := InterpExprs(es', fuel, ctx');
      if es == [] {
        assert res == Success(Return([], ctx));
        assert res' == Success(Return([], ctx'));
        assert eq.eq_state(ctx, ctx');
      }
      else {
        // Evaluate the first expression in the sequence
        var res1 := InterpExpr(es[0], fuel, ctx);
        var res1' := InterpExpr(es'[0], fuel, ctx');
        
        match res1 {
          case Success(Return(v, ctx1)) => {
            //assume false;
            // TODO: the following statement generates an error.
            // See: https://github.com/dafny-lang/dafny/issues/2258
            //var Success(Return(v', ctx1')) := res1;
            var Return(v', ctx1') := res1'.value;
            assert eq.eq_value(v, v');
            assert eq.eq_state(ctx1, ctx1');

            // Evaluate the rest of the sequence
            var res2 := InterpExprs(es[1..], fuel, ctx1);
            var res2' := InterpExprs(es'[1..], fuel, ctx1');

            // Recursive call
            All_Rel_Forall_GEqInterp_GEqInterpResult_Lem(eq, es[1..], es'[1..], fuel, ctx1, ctx1');

            match res2 {
              case Success(Return(vs, ctx2)) => {
                var Return(vs', ctx2') := res2'.value;
                assert EqSeq(eq.eq_value, vs, vs');
                assert eq.eq_state(ctx2, ctx2');
                
              }
              case Failure(_) => {
                assert res2'.Failure?;
              }
            }
          }
          case Failure(_) => {
            assert res1'.Failure?;
          }
        }
      }
    }

    lemma {:verify false} {:vcs_split_on_every_assert}
    All_Rel_Forall_EqInterp_EqInterpResult_Lem(
      es: seq<Expr>, es': seq<Expr>, fuel: nat, ctx: State, ctx': State)
      requires forall e | e in es :: SupportsInterp(e)
      requires All_Rel_Forall(EqInterp, es, es')
      requires EqState(ctx, ctx')
      ensures forall e | e in es' :: SupportsInterp(e)
      ensures EqInterpResultSeqValue(InterpExprs(es, fuel, ctx), InterpExprs(es', fuel, ctx'))
    // Auxiliary lemma: if two sequences contain equivalent expressions, evaluating those two
    // sequences in the same context leads to equivalent results.
    {
      All_Rel_Forall_GEqInterp_GEqInterpResult_Lem(EQ(EqValue, EqState), es, es', fuel, ctx, ctx');
    }

    lemma {:verify false} Map_PairOfMapDisplaySeq_Lem(e: Expr, e': Expr, argvs: seq<WV>)
      ensures EqPureInterpResult(EqSeqPairEqValueValue,
                                 Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv)),
                                 Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e', argv)))
    {
      if argvs == [] {}
      else {
        var argv := argvs[0];
        var res0 := PairOfMapDisplaySeq(e, argv);
        var res0' := PairOfMapDisplaySeq(e', argv);
        EqValue_Refl_Forall_Lem();
        assert EqPureInterpResult(EqPairEqValueValue, res0, res0');
        reveal Seq.MapResult();
        Map_PairOfMapDisplaySeq_Lem(e, e', argvs[1..]);
      }
    }

    lemma {:verify false} MapOfPairs_EqArgs_Lem(argvs: seq<(EqWV, WV)>, argvs': seq<(EqWV, WV)>)
      requires EqSeqPairEqValueValue(argvs, argvs')
      ensures EqMap(EqValue, MapOfPairs(argvs), MapOfPairs(argvs'))
    {
      if argvs == [] {}
      else {
        var lastidx := |argvs| - 1;
        EqValueHasEq_Forall_Lem();   
        MapOfPairs_EqArgs_Lem(argvs[..lastidx], argvs'[..lastidx]);
      }
    }

    lemma {:verify false} InterpMapDisplay_EqArgs_Lem(e: Expr, e': Expr, argvs: seq<WV>)
      ensures EqPureInterpResult(EqMapValue, InterpMapDisplay(e, argvs), InterpMapDisplay(e', argvs)) {
      var res0 := Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv));
      var res0' := Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e', argv));

      Map_PairOfMapDisplaySeq_Lem(e, e', argvs);

      match res0 {
        case Success(pairs) => {
          var pairs' := res0'.value;
          MapOfPairs_EqArgs_Lem(pairs, pairs');
        }
        case Failure(_) => {}
      }
    }

    predicate {:verify false} EqInterp_CanBeMapLifted_Pre(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
    {
      && EqState(ctx, ctx')
      && Exprs.ConstructorsMatch(e, e')
      && All_Rel_Forall(EqInterp, e.Children(), e'.Children())
      && SupportsInterp(e)
      && SupportsInterp(e')
    }

    predicate {:verify false} EqInterp_CanBeMapLifted_Post(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
    {
      EqValueResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx'))
    }

    // TODO: move
    // TODO: this lemma, which does nothing else than calling sub-lemmas, takes 2.5 minutes to
    // verify!!
    lemma {:verify false} {:vcs_split_on_every_assert} EqInterp_Expr_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 2
    {
      reveal InterpExpr();
      match e {
        case Var(_) => {
          assert EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx') by {
            reveal TryGetLocal();
          }
        }
        case Literal(_) => {
          assert EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx') by {
            reveal InterpLiteral();
          }
        }
        case Abs(_, _) => {
          EqInterp_Expr_Abs_CanBeMapLifted_Lem(e, e', fuel, ctx, ctx');
        }
        case Apply(Lazy(_), _) => {
          EqInterp_Expr_ApplyLazy_CanBeMapLifted_Lem(e, e', fuel, ctx, ctx');
        }
        case Apply(Eager(_), _) => {
          EqInterp_Expr_ApplyEager_CanBeMapLifted_Lem(e, e', fuel, ctx, ctx');
        }
        case If(_, _, _) => {
          EqInterp_Expr_If_CanBeMapLifted_Lem(e, e', fuel, ctx, ctx');
        }
        case _ => {
          // Unsupported branch
          assert false;
        }
      }
    }

    // TODO: move
    lemma {:verify false} {:vcs_split_on_every_assert}
    EqInterp_Expr_Abs_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Abs?
      requires e'.Abs?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 1
    {
      var Abs(vars, body) := e;
      var Abs(vars', body') := e';
      assert vars == vars';
      assert body == e.Children()[0];
      assert body' == e'.Children()[0];
      assert EqInterp(body, body');

      var cv := Closure(ctx.locals, vars, body);
      var cv' := Closure(ctx'.locals, vars', body');
      assert InterpExpr(e, fuel, ctx) == Success(Return(cv, ctx)) by { reveal InterpExpr(); }
      assert InterpExpr(e', fuel, ctx') == Success(Return(cv', ctx')) by {reveal InterpExpr(); }

      forall fuel: nat, argvs: seq<WV>, argvs': seq<WV> |
        && |argvs| == |argvs'| == |vars|
        && (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
        ensures
          var res := InterpCallFunctionBody(cv, fuel, argvs);
          var res' := InterpCallFunctionBody(cv', fuel, argvs');
          EqPureInterpResultValue(res, res') {
        EqInterp_Expr_AbsClosure_CanBeMapLifted_Lem(cv, cv', fuel, argvs, argvs');
      }

      assert EqValue_Closure(cv, cv') by {
        reveal EqValue_Closure();
      }
    }

    lemma {:verify false} {:vcs_split_on_every_assert}
    EqInterp_Expr_AbsClosure_CanBeMapLifted_Lem(cv: WV, cv': WV, fuel: nat, argvs: seq<WV>, argvs': seq<WV>)
      requires cv.Closure?
      requires cv'.Closure?
      requires |argvs| == |argvs'| == |cv.vars|
      requires (forall i | 0 <= i < |argvs| :: EqValue(argvs[i], argvs'[i]))
      requires cv.vars == cv'.vars
      requires EqCtx(cv.ctx, cv'.ctx)
      requires EqInterp(cv.body, cv'.body)
      ensures
          var res := InterpCallFunctionBody(cv, fuel, argvs);
          var res' := InterpCallFunctionBody(cv', fuel, argvs');
          EqPureInterpResultValue(res, res')
    {
      var res := InterpCallFunctionBody(cv, fuel, argvs);
      var res' := InterpCallFunctionBody(cv', fuel, argvs');

      var ctx1 := BuildCallState(cv.ctx, cv.vars, argvs);
      var ctx1' := BuildCallState(cv'.ctx, cv'.vars, argvs');
      BuildCallState_EqState_Lem(cv.ctx, cv'.ctx, cv.vars, argvs, argvs');
      assert EqState(ctx1, ctx1');

      assert EqPureInterpResultValue(res, res') by {
        reveal InterpCallFunctionBody();
      }
    }

    lemma {:verify false} {:vcs_split_on_every_assert}
    BuildCallState_EqState_Lem(ctx: Context, ctx': Context, vars: seq<string>, argvs: seq<WV>, argvs': seq<WV>)
      requires WellFormedContext(ctx)
      requires WellFormedContext(ctx')
      requires |argvs| == |argvs'| == |vars|
      requires (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
      requires EqCtx(ctx, ctx')
      ensures
        var ctx1 := BuildCallState(ctx, vars, argvs);
        var ctx1' := BuildCallState(ctx', vars, argvs');
        EqState(ctx1, ctx1')
    {
      MapOfPairs_SeqZip_EqCtx_Lem(vars, argvs, argvs');
      var m := MapOfPairs(Seq.Zip(vars, argvs));
      var m' := MapOfPairs(Seq.Zip(vars, argvs'));
      reveal BuildCallState();
      var ctx1 := BuildCallState(ctx, vars, argvs);
      var ctx1' := BuildCallState(ctx', vars, argvs');
      assert ctx1.locals == ctx + m;
      assert ctx1'.locals == ctx' + m';
    }

    lemma {:verify false}
    MapOfPairs_EqCtx_Lem(pl: seq<(string, WV)>, pl': seq<(string, WV)>)
      requires |pl| == |pl'|
      requires (forall i | 0 <= i < |pl| :: pl[i].0 == pl'[i].0)
      requires (forall i | 0 <= i < |pl| :: EqValue(pl[i].1, pl'[i].1))
      ensures
        var m := MapOfPairs(pl);
        var m' := MapOfPairs(pl');
        && EqCtx(m, m')
    {
      if pl == [] {}
      else {
        var lastidx := |pl| - 1;
        MapOfPairs_EqCtx_Lem(pl[..lastidx], pl'[..lastidx]);
      }
    }

    lemma {:verify false} {:vcs_split_on_every_assert}
    MapOfPairs_SeqZip_EqCtx_Lem(vars: seq<string>, argvs: seq<WV>, argvs': seq<WV>)
      requires |argvs| == |argvs'| == |vars|
      requires (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
      ensures
        var m := MapOfPairs(Seq.Zip(vars, argvs));
        var m' := MapOfPairs(Seq.Zip(vars, argvs'));
        && EqCtx(m, m')
    {
      var pl := Seq.Zip(vars, argvs);
      var pl' := Seq.Zip(vars, argvs');

      assert |pl| == |pl'|;
      assert forall i | 0 <= i < |pl| :: pl[i].0 == pl'[i].0;
      assert forall i | 0 <= i < |pl| :: EqValue(pl[i].1, pl'[i].1);

      MapOfPairs_EqCtx_Lem(pl, pl');
    }

    // TODO: HERE
    lemma {:verify false} EqInterp_Expr_ApplyLazy_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Apply? && e.aop.Lazy?
      requires e'.Apply? && e'.aop.Lazy?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 1
    {
      assume false; // TODO: prove
    }

    lemma {:verify false} EqInterp_Expr_ApplyEager_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Apply? && e.aop.Eager?
      requires e'.Apply? && e'.aop.Eager?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 1
    {
      assume false; // TODO: prove
    }

    lemma {:verify false} EqInterp_Expr_If_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.If?
      requires e'.If?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 1
    {
      assume false; // TODO: prove
    }

    // TODO: remove
    // TODO: HERE
    lemma {:verify false} Tr_EqInterp_Expr_Lem_old(f: Expr --> Expr)
      requires forall e | f.requires(e) :: EqInterp(e, f(e))
      //requires Tr_EqInterp(f,rel)
      //requires TransformerPreservesRel(f,rel)
      ensures TransformerPreservesRel(f, EqInterp)
    {
      forall e, e' |
        && Exprs.ConstructorsMatch(e, e')
        && f.requires(e')
        && All_Rel_Forall(EqInterp, e.Children(), e'.Children())
        && SupportsInterp(e) // Constraining a bit
        ensures EqInterp(e, f(e'))
        {
          forall exprs, exprs', fuel, ctx | (forall e | e in exprs :: SupportsInterp(e)) && All_Rel_Forall(EqInterp, exprs, exprs')
            ensures forall e | e in exprs' :: SupportsInterp(e)
            ensures EqInterpResult(EqSeqValue, InterpExprs(exprs, fuel, ctx), InterpExprs(exprs', fuel, ctx)) {
              // TODO: fix this
              EqState_Refl_Lem(ctx);
              All_Rel_Forall_EqInterp_EqInterpResult_Lem(exprs, exprs', fuel, ctx, ctx);
          }

          match e {
            case Var(_) => {
              assert EqInterp(e, e');
            }
            case Literal(lit_) => {
              assert EqInterp(e, e');
            }
            case Abs(vars, body) => {
              assume SupportsInterp(e'); // TODO
              assume EqInterp(e, e'); // TODO
            }
            case Apply(Eager(op), exprs) => {
              assert SupportsInterp(e');

              var Apply(Eager(op'), exprs') := e';
              assert op' == op;
              assert All_Rel_Forall(EqInterp, exprs, exprs');
              forall fuel, ctx
                ensures EqValueResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx))
              {
                var res := InterpExpr(e, fuel, ctx);
                var res' := InterpExpr(e', fuel, ctx);

                // The arguments evaluate to similar results
                assert EqInterpResult(EqSeqValue, InterpExprs(exprs, fuel, ctx), InterpExprs(exprs', fuel, ctx));
                
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
                        assert EqValueResult(res, res');
                      }
                      case BinaryOp(bop: BinaryOp) => {
                        assert EqValueResult(res, res');
                      }
                      case TernaryOp(top: TernaryOp) => {
                        assert EqValueResult(res, res');
                      }
                      case Builtin(Display(ty)) => {
                        assert res == LiftPureResult(ctx1, InterpDisplay(e, ty.kind, vs));
                        assert res' == LiftPureResult(ctx1, InterpDisplay(e', ty.kind, vs));
                        match ty.kind {
                          case Map(_) => {
                            InterpMapDisplay_EqArgs_Lem(e, e', vs);
                            assert EqValueResult(res, res');
                          }
                          case _ => {
                            assert EqValueResult(res, res');
                          }
                        }
                      }
                      case FunctionCall() => {
                        var fn := vs[0];
                        var argvs := vs[1..];
                        assert res == LiftPureResult(ctx1, InterpFunctionCall(e, fuel, fn, argvs));
                        assert res' == LiftPureResult(ctx1, InterpFunctionCall(e', fuel, fn, argvs));
                        assert EqValueResult(res, res');
                      }
                    }
                  }
                  case Failure(_) => {
                    assert EqValueResult(res, res');
                  }
                }
              }

              assert EqInterp(e, e');
            }
            case Apply(Lazy(op), exprs) => {
              forall fuel, ctx
                ensures EqValueResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx))
              {
                var res := InterpExpr(e, fuel, ctx);
                var res' := InterpExpr(e', fuel, ctx);

                assert res == InterpLazy(e, fuel, ctx);
                assert res' == InterpLazy(e', fuel, ctx);

                var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
                var op', e0', e1' := e'.aop.lOp, e'.args[0], e'.args[1];
                assert op == op';

                EqInterp_Lem(e0, e0', fuel, ctx, ctx); // TODO: ctx, ctx'
                var res0 := InterpExprWithType(e0, Type.Bool, fuel, ctx);
                var res0' := InterpExprWithType(e0', Type.Bool, fuel, ctx);
                assert EqValueResult(res0, res0');
                
                match res0 {
                  case Success(Return(v0, ctx0)) => {
                    EqInterp_Lem(e1, e1', fuel, ctx0, ctx0); // TODO: ctx0, ctx0'
                    assert EqValueResult(InterpExprWithType(e1, Type.Bool, fuel, ctx0), InterpExprWithType(e1', Type.Bool, fuel, ctx0)); // Fails without this
                    assert EqValueResult(res, res');
                  }
                  case Failure(_) => {
                    assert res.Failure?;
                    assert res0'.Failure?; // Fails without this
                    assert EqValueResult(res, res');
                  }
                }
                assume EqValueResult(res, res');
              }
              
              assert EqInterp(e, e');
            }
            case Block(exprs) => {
              assert EqInterp(e, e');
            }
            case If(cond, thn, els) => {
              var If(cond', thn', els') := e';

              assert cond == e.Children()[0];
              assert thn == e.Children()[1];
              assert els == e.Children()[2];

              assert cond' == e'.Children()[0];
              assert thn' == e'.Children()[1];
              assert els' == e'.Children()[2];

              assert EqInterp(cond, cond');
              assert EqInterp(thn, thn');
              assert EqInterp(els, els');

              assert SupportsInterp(e');

              forall fuel, ctx
                ensures EqValueResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx)) {
                  var res := InterpExpr(e, fuel, ctx);
                  var res' := InterpExpr(e', fuel, ctx);

                  var res1 := InterpExprWithType(cond, Type.Bool, fuel, ctx);
                  var res1' := InterpExprWithType(cond', Type.Bool, fuel, ctx);

                  // TODO: ctx, ctx'
                  EqInterp_Lem(cond, cond', fuel, ctx, ctx); // Below assert fails without this lemma
                  assert EqValueResult(res1, res1');

                  match res1 {
                    case Success(Return(condv, ctx1)) => {
                      var condv' := res1'.value.ret;
                      var ctx1' := res1'.value.ctx;

                      assert condv' == condv;
                      assert ctx1' == ctx1;
                      
                      // TODO: ctx1, ctx1'
                      EqInterp_Lem(thn, thn', fuel, ctx1, ctx1); // Proof fails without this lemma
                      EqInterp_Lem(els, els', fuel, ctx1, ctx1); // Proof fails without this lemma
                    }
                    case Failure(_) => {
                      assert InterpExprWithType(cond', Type.Bool, fuel, ctx).Failure?; // Proof fails without this
                      assert EqValueResult(res, res');
                    }
                  }
              }
              assert EqInterp(e, e');
            }
          }
          assert EqInterp(e, e');
          assert EqInterp(e, f(e'));
        }
    }
    
    predicate {:verify false} Tr_Expr_Rel(e: Exprs.T, e': Exprs.T) {
      EqInterp(e, e')
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
          ensures EqValueResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx)) {
          // Start by proving that the flipped binary operation (not wrapped in the "not") returns exactly the
          // opposite result of the non-flipped binary operation.
          var flipped := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), args);

          // Intermediate result: evaluating (the sequence of expressions) `[flipped]` is the same as evaluating (the expression) `flipped`.
          InterpExprs1_Lem(flipped, fuel, ctx);
          assert EqInterpResultSeq1Value(InterpExpr(flipped, fuel, ctx), InterpExprs([flipped], fuel, ctx));

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
          assert EqValueResult(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx));
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
      Tr_EqInterp_Expr_Lem_old(f);
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
