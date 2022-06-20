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

      predicate {:verify false} MapChildrenPreservesPre(f: Expr --> Expr, post: Expr -> bool)
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
      {
        (forall e, e' ::
           (&& Exprs.ConstructorsMatch(e, e')
            && f.requires(e)
            && Deep.AllChildren_Expr(e', post)) ==> f.requires(e'))
       }

      predicate {:verify false} TransformerMatchesPrePost(f: Expr --> Expr, post: Expr -> bool)
      // This predicate gives us the conditions for which, if we deeply apply `f` to an
      // expression, the resulting expression satisfies the postcondition we give for `f`.
      // 
      // Given `e`, if:
      // - all the children of `e` deeply satisfy the post of `f`
      // - `e` satisfies the pre of `f`
      // Then:
      // - `f(e)` deeply satisfies the post of `f`
      {
        forall e: Expr | Deep.AllChildren_Expr(e, post) && f.requires(e) ::
          Deep.All_Expr(f(e), post)
      }

      predicate {:verify false} TransformerShallowPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
      // `f` relates its input and its output with `rel`.
      {
        forall e | f.requires(e) :: rel(e, f(e))
      }

      predicate {:verify false} TransformerDeepPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
      // This predicate is quite general, but is to be used in the following setting:
      // if we apply `f` on all the children of `e`, leading to an expression `e'`, then we
      // can relate `e` and `f(e')` with `rel`.
      {
        (forall e, e' ::
           (&& Exprs.ConstructorsMatch(e, e')
            && f.requires(e')
            && All_Rel_Forall(rel, e.Children(), e'.Children()))
            ==> rel(e, f(e')))
      }
      
      predicate {:verify false} IsBottomUpTransformer(f: Expr --> Expr, post: Expr -> bool, rel: (Expr,Expr) -> bool)
      // Predicate for ``BottomUpTransformer``
      {
        && TransformerMatchesPrePost(f, post)
        && MapChildrenPreservesPre(f, post)
        && TransformerDeepPreservesRel(f, rel)
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
        ensures TransformerDeepPreservesRel(IdentityTransformer.f, IdentityTransformer.rel)
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

      predicate {:verify false} RelIsTransitive<T(!new)>(rel: (T, T) -> bool) {
        forall x0, x1, x2 | rel(x0, x1) && rel(x1, x2) :: rel(x0, x2)
      }

      // A bottom-up transformer, i.e.: a transformer we can recursively apply bottom-up to
      // an expression, and get the postcondition we expect on the resulting expression.
      type {:verify false} BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.post, tr.rel)
        witness (IdentityMatchesPrePost();
                 IdentityPreservesPre();
                 IdentityPreservesRel();
                 IdentityTransformer)

      function method {:verify false} MapChildren_Expr(e: Expr, tr: BottomUpTransformer) :
        (e': Expr)
        decreases e, 0
        requires Deep.AllChildren_Expr(e, tr.f.requires)
        ensures Deep.AllChildren_Expr(e', tr.post)
        ensures Exprs.ConstructorsMatch(e, e')
        ensures All_Rel_Forall(tr.rel, e.Children(), e'.Children())
      // Apply a transformer bottom-up on the children of an expression.
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

      function method {:verify false} Map_Expr_Transformer'(tr: BottomUpTransformer) :
        (tr': Transformer'<Expr,Expr>)
      // We can write aggregated statements only in lemmas.
      // This forced me to cut this definition into pieces...
      {
        TR(e requires Deep.All_Expr(e, tr.f.requires) => Map_Expr(e, tr),
           e' => Deep.All_Expr(e', tr.post),
           tr.rel)
      }

      lemma {:verify false} Map_Expr_Transformer'_Lem(tr: BottomUpTransformer)
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

      function method {:verify false} Map_Expr_Transformer(tr: BottomUpTransformer) :
        (tr': ExprTransformer)
      // Given a bottom-up transformer `tr`, return a transformer which applies `tr` in
      // a bottom-up manner.
      {
        var tr': Transformer'<Expr,Expr> := Map_Expr_Transformer'(tr);
        Map_Expr_Transformer'_Lem(tr);
        tr'
      }

      function method {:verify false} {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) :
        (m': Method)
        requires Deep.All_Method(m, tr.f.requires)
        ensures Deep.All_Method(m', tr.post)
        ensures tr.rel(m.methodBody, m'.methodBody)
      // Apply a transformer to a method, in a bottom-up manner.
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      function method {:verify false} {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) :
        (p': Program)
        requires Deep.All_Program(p, tr.f.requires)
        ensures Deep.All_Program(p', tr.post)
        ensures tr.rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
      // Apply a transformer to a program, in a bottom-up manner.
      {
        Shallow.Map_Program(p, Map_Expr_Transformer(tr))
      }
    }
  }

  module Equiv {
    // This module introduces the relations we use to describe values and expressions
    // as equivalent, and which we use to state that our compilation passes are sound.

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

    // TODO: use more
    datatype Equivs =
      EQ(eq_value: (WV, WV) -> bool, eq_state: (State, State) -> bool)

    // TODO: not sure it was worth making this opaque
    predicate {:verify false} {:opaque} GEqCtx(
      eq_value: (WV,WV) -> bool, ctx: Context, ctx': Context)
      requires WellFormedContext(ctx)
      requires WellFormedContext(ctx')
    {
      && ctx.Keys == ctx'.Keys
      && (forall x | x in ctx.Keys :: eq_value(ctx[x], ctx'[x])) 
    }

    predicate {:verify false} GEqState(
      eq_value: (WV,WV) -> bool, ctx: State, ctx': State)
    {
      GEqCtx(eq_value, ctx.locals, ctx'.locals)
    }

    function {:verify false} Mk_EqState(eq_value: (WV,WV) -> bool): (State,State) -> bool
    {
      (ctx, ctx') => GEqState(eq_value, ctx, ctx')
    }

    predicate {:verify false} GEqInterpResult<T(0)>(
      eq_ctx: (State,State) -> bool, eq_value: (T,T) -> bool, res: InterpResult<T>, res': InterpResult<T>)
    // Interpretation results are equivalent.
    // "G" stands for "generic".
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

    function method {:opaque} {:verify false} InterpCallFunctionBody(fn: WV, fuel: nat, argvs: seq<WV>)
      : (r: PureInterpResult<WV>)
      requires fn.Closure?
      requires |fn.vars| == |argvs|
    // Small utility, very similar to ``InterpFunctionCall``, which we use to factorize
    // the definitions. The opaque attribute is maybe not necessary anymore, but as the
    // proofs work with it, we might as well keep it (it is easier to remove an opaque
    // attribute, than to add one and fix the proofs by adding the proper calls to ``reveal``).
    {
        var ctx := BuildCallState(fn.ctx, fn.vars, argvs);
        var Return(val, ctx) :- InterpExpr(fn.body, fuel, ctx);
        Success(val)
    }

    predicate {:verify false} EqValue(v: WV, v': WV)
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
          && |m| == |m'| // We *do* need this
          && (forall x | x in m :: EqValue(m[x], m'[x]))
        case (Multiset(ms), Multiset(ms')) =>
          ms == ms'
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

    predicate {:verify false} {:opaque} EqValue_Closure(v: WV, v': WV)
      requires v.Closure?
      requires v'.Closure?
      decreases ValueTypeHeight(v) + ValueTypeHeight(v'), 0
    // Equivalence between values: closure case.
    //
    // See ``EqValue``.
    //
    // Rk.: contrary to ``EqValue``, it seems ok to make ``EqValue_Closure`` opaque.
    {
      var Closure(ctx, vars, body) := v;
      var Closure(ctx', vars', body') := v';
      && |vars| == |vars'|
      && (
      forall fuel:nat, argvs: seq<WV>, argvs': seq<WV> |
        && |argvs| == |argvs'| == |vars| // no partial applications are allowed in Dafny
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

    lemma {:verify false} EqValueHasEq_Lem(v: WV, v': WV)
      requires EqValue(v,v')
      requires HasEqValue(v)
      requires HasEqValue(v')
      ensures v == v'
    // If values are equivalent and have a decidable equality, they are necessarily equal.
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

    // TODO: move
    lemma {:verify false} EqInterp_Expr_EqState_Lem(e: Exprs.T, fuel: nat, ctx: State, ctx': State)
      requires SupportsInterp(e)
      ensures EqInterpResultValue(InterpExpr(e, fuel, ctx), InterpExpr(e, fuel, ctx'))
    {
      assume false; // TODO: prove
    }

    lemma {:verify false} EqValue_Refl_Lem(v: WV)
      ensures EqValue(v, v)
      decreases v, 1
    {
      match v {
        case Bool(_) => {}
        case Char(_) => {}
        case Int(_) => {}
        case Real(_) => {}
        case BigOrdinal(_) => {}
        case BitVector(_, _) => {}
        case Map(m) => {
          ValueTypeHeight_Children_Lem(v); // For termination
          forall x | x in m ensures EqValue(m[x], m[x]) {
            EqValue_Refl_Lem(m[x]);
          }
        }
        case Multiset(ms) => {}
        case Seq(sq) => {
          ValueTypeHeight_Children_Lem(v); // For termination
          forall i | 0 <= i < |sq| ensures EqValue(sq[i], sq[i]) {
            EqValue_Refl_Lem(sq[i]);
          }
        }
        case Set(st) => {}
        case Closure(ctx, vars, body) => {
          EqValue_Closure_Refl_Lem(v);
        }
      }
    }

    // TODO: prove
    lemma {:verify false} EqValue_Closure_Refl_Lem(v: WV)
      requires v.Closure?
      ensures EqValue_Closure(v, v)
      decreases v, 0
    {
      reveal EqValue_Closure();

      var Closure(ctx, vars, body) := v;

      forall fuel:nat, argvs: seq<WV>, argvs': seq<WV> |
        && |argvs| == |argvs'| == |vars|
        && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs[i]) < ValueTypeHeight(v))
        && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs'[i]) < ValueTypeHeight(v))
        && (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
        ensures
          var res := InterpCallFunctionBody(v, fuel, argvs);
          var res' := InterpCallFunctionBody(v, fuel, argvs');
          EqPureInterpResultValue(res, res')
      {
          var res := InterpCallFunctionBody(v, fuel, argvs);
          var res' := InterpCallFunctionBody(v, fuel, argvs');

          assert EqCtx(ctx, ctx) by {
            // It would be difficult to call a lemma like ``EqState_Refl_Lem`` here, because
            // of termination issues. However, we have that the values in the closure context
            // are smaller than the closure value itself, which allows us to recursively call
            // ``EqValue``.
            forall x | x in ctx ensures EqValue(ctx[x], ctx[x]) {
              EqValue_Refl_Lem(ctx[x]);
            }
            reveal GEqCtx();
          }

/*          var ctx1 := BuildCallState(cv.ctx, cv.vars, argvs);
          var ctx1' := BuildCallState(cv'.ctx, cv'.vars, argvs');
          BuildCallState_EqState_Lem(cv.ctx, cv'.ctx, cv.vars, argvs, argvs');
          assert EqState(ctx1, ctx1');*/

          reveal InterpCallFunctionBody();
          assume EqPureInterpResultValue(res, res'); // TODO: prove
      }
    }

    lemma {:verify false} EqState_Refl_Lem(ctx: State)
      ensures EqState(ctx, ctx)
    {
      reveal GEqCtx();
      EqValue_Refl_Forall_Lem();
    }

    lemma {:verify false} EqValue_Trans_Lem(v0: WV, v1: WV, v2: WV)
      requires EqValue(v0, v1)
      requires EqValue(v1, v2)
      ensures EqValue(v0, v2)
      decreases ValueTypeHeight(v0), 1
    {
      match v0 {
        case Bool(_) => {}
        case Char(_) => {}
        case Int(_) => {}
        case Real(_) => {}
        case BigOrdinal(_) => {}
        case BitVector(_, _) => {}
        case Map(m0) => {
          ValueTypeHeight_Children_Lem(v0); // For termination
          forall x | x in m0 ensures EqValue(v0.m[x], v2.m[x]) {
            EqValue_Trans_Lem(v0.m[x], v1.m[x], v2.m[x]);
          }
        }
        case Multiset(ms) => {}
        case Seq(sq) => {
          ValueTypeHeight_Children_Lem(v0); // For termination
          forall i | 0 <= i < |sq| ensures EqValue(v0.sq[i], v2.sq[i]) {
            EqValue_Trans_Lem(v0.sq[i], v1.sq[i], v2.sq[i]);
          }
        }
        case Set(st) => {}
        case Closure(ctx, vars, body) => {
          EqValue_Closure_Trans_Lem(v0, v1, v2);
        }
      }
    }

    lemma {:verify false} EqValue_Closure_Trans_Lem(v0: WV, v1: WV, v2: WV)
      requires v0.Closure?
      requires v1.Closure?
      requires v2.Closure?
      requires EqValue_Closure(v0, v1)
      requires EqValue_Closure(v1, v2)
      ensures EqValue_Closure(v0, v2)
      decreases ValueTypeHeight(v0), 0
    {
      reveal EqValue_Closure();

      var Closure(ctx0, vars0, body0) := v0;
      var Closure(ctx1, vars1, body1) := v1;
      var Closure(ctx2, vars2, body2) := v2;

      forall fuel:nat, argvs0: seq<WV>, argvs2: seq<WV> |
        && |argvs0| == |argvs2| == |vars0|
        && (forall i | 0 <= i < |vars0| :: ValueTypeHeight(argvs0[i]) < ValueTypeHeight(v0))
        && (forall i | 0 <= i < |vars0| :: ValueTypeHeight(argvs2[i]) < ValueTypeHeight(v2))
        && (forall i | 0 <= i < |vars0| :: EqValue(argvs0[i], argvs2[i]))
        ensures
          var res0 := InterpCallFunctionBody(v0, fuel, argvs0);
          var res2 := InterpCallFunctionBody(v2, fuel, argvs2);
          EqPureInterpResultValue(res0, res2)
      {
          var res0 := InterpCallFunctionBody(v0, fuel, argvs0);
          var res2 := InterpCallFunctionBody(v2, fuel, argvs2);

          // Termination issue: we need to assume that the arguments' types have the
          // proper height. In practice, if the program is properly type checked, we
          // have:
          // - `TypeOf(v0) == TypeOf(v1) == TypeOf(v2)`
          // - `forall i, TypeOf(argvs0[i]) == TypeOf(argvs2[i])1
          // so the assumption is trivially true.
          assume (forall i | 0 <= i < |vars0| :: ValueTypeHeight(argvs0[i]) < ValueTypeHeight(v1));

          forall i | 0 <= i < |vars0| ensures EqValue(argvs0[i], argvs0[i]) {
            EqValue_Refl_Lem(argvs0[i]);
          }

          var res1 := InterpCallFunctionBody(v1, fuel, argvs0);
          if res0.Success? {
            var ov0 := res0.value;
            var ov1 := res1.value;
            var ov2 := res2.value;

            // Termination - same as above: if the program is well-typed, this is
            // trivially true.
            assume ValueTypeHeight(ov0) < ValueTypeHeight(v0);

            EqValue_Trans_Lem(ov0, ov1, ov2);
            
            assert EqPureInterpResultValue(res0, res2);
          }
          else {
            assert res1.Failure?;
            assert res2.Failure?;
          }
      }
    }
    
    lemma {:verify false} {:induction v, v'} EqValue_HasEqValue_Lem(v: WV, v': WV)
      requires EqValue(v, v')
      ensures HasEqValue(v) == HasEqValue(v')
    {}

    lemma {:verify false} EqValue_HasEqValue_Forall_Lem()
      ensures forall v: WV, v': WV | EqValue(v, v') :: HasEqValue(v) == HasEqValue(v')
    {
      forall v: WV, v': WV | EqValue(v, v') ensures HasEqValue(v) == HasEqValue(v') {
        EqValue_HasEqValue_Lem(v, v');
      }
    }

    lemma {:verify false} EqValue_HasEqValue_Eq_Lem(v: WV, v': WV)
      requires EqValue(v, v')
      ensures HasEqValue(v) == HasEqValue(v')
      ensures HasEqValue(v) ==> v == v'
    {
      EqValue_HasEqValue_Lem(v, v');
      if HasEqValue(v) || HasEqValue(v') {
        EqValueHasEq_Lem(v, v');
      }
    }

    lemma {:verify false} EqValue_HasEqValue_Eq_Forall_Lem()
      ensures forall v:WV, v':WV | EqValue(v, v') ::
        && (HasEqValue(v) == HasEqValue(v'))
        && (HasEqValue(v) ==> v == v')
    // This is one of the important lemmas for the proofs of equivalence.
    // The reason is that the interpreter often checks that some values
    // have a decidable equality (for instance, before inserting a value in
    // a set). When doing equivalence proofs, for instance to prove that the
    // same instruction evaluated in equivalent contexts generates equivalent
    // results, we often want:
    // - to know that the check succeeds in both cases, or fails in both cases
    // - to know that if it succeeded, then the valuevs are equal
    {
      forall v:WV, v':WV | EqValue(v, v')
        ensures
        && (HasEqValue(v) == HasEqValue(v'))
        && (HasEqValue(v) ==> v == v') {
          EqValue_HasEqValue_Eq_Lem(v, v');
      }
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

    lemma {:verify false} EqState_Trans_Lem(ctx0: State, ctx1: State, ctx2: State)
      requires EqState(ctx0, ctx1)
      requires EqState(ctx1, ctx2)
      ensures EqState(ctx0, ctx2)
    {
      reveal GEqCtx();
      forall x | x in ctx0.locals.Keys ensures EqValue(ctx0.locals[x], ctx2.locals[x]) {
        EqValue_Trans_Lem(ctx0.locals[x], ctx1.locals[x], ctx2.locals[x]);
      }
    }

    predicate {:verify false} EqSeq<T(0)>(eq_values: (T,T) -> bool, vs: seq<T>, vs': seq<T>) {
      && |vs| == |vs'|
      && (forall i | 0 <= i < |vs| :: eq_values(vs[i], vs'[i]))
    }

    predicate {:verify false} EqMap<T(0,!new), U(0,!new)>(eq_values: (U,U) -> bool, vs: map<T, U>, vs': map<T, U>) {
      && vs.Keys == vs'.Keys
      && |vs| == |vs'|
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
      && m.Keys == m'.Keys
      && |m| == |m'|
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
    
    predicate {:verify false} EqInterpResultValue(res: InterpResult<WV>, res': InterpResult<WV>)
    {
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
          && |sv| == 1
          && EqValue(v, sv[0])
          && EqState(ctx, ctx')
        case (Failure(_), Failure(_)) =>
          true
        case _ =>
          false
      }
    }

    predicate {:verify false} EqInterpResultSeq1Value_Strong(res: InterpResult<WV>, res': InterpResult<seq<WV>>) {
      match (res, res') {
        case (Success(Return(v,ctx)), Success(Return(sv,ctx'))) =>
          && sv == [v]
          && ctx == ctx'
        case (Failure(err), Failure(err')) =>
          err == err'
        case _ =>
          false
      }
    }

    // TODO: make opaque?
    predicate {:verify false} GEqInterp(eq: Equivs, e: Exprs.T, e': Exprs.T)
    // This is the important, generic equivalence relation over expressions.
    {
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

    // TODO: make opaque?
    predicate {:verify false} EqInterp(e: Exprs.T, e': Exprs.T)
    // The important equivalence relation over expressions.
    {
      GEqInterp(EQ(EqValue, Mk_EqState(EqValue)), e, e')
    }

    lemma {:verify false} EqInterp_Refl_Lem(e: Exprs.T)
      ensures EqInterp(e, e)
    {
      if SupportsInterp(e) {
        forall fuel, ctx, ctx' | EqState(ctx, ctx')
          ensures
            EqInterpResultValue(
                         InterpExpr(e, fuel, ctx),
                         InterpExpr(e, fuel, ctx'))
        {
          EqInterp_Expr_EqState_Lem(e, fuel, ctx, ctx'); 
        }
      }
    }

    lemma {:verify false} EqInterp_Seq_Refl_Lem(es: seq<Exprs.T>)
      ensures All_Rel_Forall(EqInterp, es, es)
    {
      forall i | 0 <= i < |es| ensures EqInterp(es[i], es[i]) {
        EqInterp_Refl_Lem(es[i]);
      }
    }

    lemma {:verify false} EqInterp_Trans_Lem(e0: Exprs.T, e1: Exprs.T, e2: Exprs.T)
      requires EqInterp(e0, e1)
      requires EqInterp(e1, e2)
      ensures EqInterp(e0, e2)
    {
      if SupportsInterp(e0) {
        forall fuel, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e0, fuel, ctx), InterpExpr(e2, fuel, ctx')) {
          EqState_Refl_Lem(ctx);
          assert EqState(ctx, ctx);
          var res0 := InterpExpr(e0, fuel, ctx);
          var res1 := InterpExpr(e1, fuel, ctx);
          var res2 := InterpExpr(e2, fuel, ctx');
          assert EqInterpResultValue(res0, res1);
          assert EqInterpResultValue(res1, res2);

          if res0.Success? {
            EqValue_Trans_Lem(res0.value.ret, res1.value.ret, res2.value.ret);
            EqState_Trans_Lem(res0.value.ctx, res1.value.ctx, res2.value.ctx);
          }
          else {}
        }
      }
      else {}
    }

    lemma {:verify false} EqInterp_IsTransitive_Lem()
      ensures RelIsTransitive(EqInterp)
    {
      forall e0, e1, e2 | EqInterp(e0, e1) && EqInterp(e1, e2) ensures EqInterp(e0, e2) {
        EqInterp_Trans_Lem(e0, e1, e2);
      }
    }

    lemma {:verify false} InterpExprs1_Strong_Lem(e: Expr, fuel: nat, ctx: State)
      requires SupportsInterp(e)
      ensures forall e' | e' in [e] :: SupportsInterp(e')
      ensures EqInterpResultSeq1Value_Strong(InterpExpr(e, fuel, ctx), InterpExprs([e], fuel, ctx))
      // Auxiliary lemma: evaluating a sequence of one expression is equivalent to evaluating
      // the single expression.
    {
      reveal InterpExprs();
      var es := [e];
      var es' := es[1..];
      assert es' == [];

      var e_res := InterpExpr(e, fuel, ctx);
      var es_res := InterpExprs([e], fuel, ctx);

      if e_res.Success? {
        var Return(v, ctx1) := e_res.value;
        
        assert InterpExprs(es', fuel, ctx1) == Success(Return([], ctx1));
        assert es_res == Success(Return([v] + [], ctx1));
      }
      else {
        // Trivial
      }
    }

    lemma {:verify false} EqInterp_Lem(e: Exprs.T, e': Exprs.T, fuel: nat, ctx: State, ctx': State)
      requires SupportsInterp(e)
      requires EqInterp(e, e')
      requires EqState(ctx, ctx')
      ensures SupportsInterp(e')
      ensures EqInterpResultValue(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx'))
    // We use this lemma because sometimes quantifiers are are not triggered.
    {}

    lemma {:verify false}
      InterpExprs_GEqInterp_Lem(
      eq: Equivs, es: seq<Expr>, es': seq<Expr>, fuel: nat, ctx: State, ctx': State)
      requires forall e | e in es :: SupportsInterp(e)
      requires All_Rel_Forall(Mk_EqInterp(eq), es, es')
      requires eq.eq_state(ctx, ctx')
      ensures forall e | e in es' :: SupportsInterp(e)
      ensures GEqInterpResultSeq(eq, InterpExprs(es, fuel, ctx), InterpExprs(es', fuel, ctx'))
    // Auxiliary lemma: if two sequences contain equivalent expressions, evaluating those two
    // sequences in equivalent contexts leads to equivalent results.
    // This lemma is written generically over the equivalence relations over the states and
    // values. We don't do this because it seems elegant: we do this as a desperate attempt
    // to reduce the context size, while we are unable to use the `opaque` attribute on
    // some definitions (``EqValue`` in particular).
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
            InterpExprs_GEqInterp_Lem(eq, es[1..], es'[1..], fuel, ctx1, ctx1');

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

    lemma {:verify false}
    InterpExprs_EqInterp_Lem(es: seq<Expr>, es': seq<Expr>, fuel: nat, ctx: State, ctx': State)
      requires forall e | e in es :: SupportsInterp(e)
      requires All_Rel_Forall(EqInterp, es, es')
      requires EqState(ctx, ctx')
      ensures forall e | e in es' :: SupportsInterp(e)
      ensures EqInterpResultSeqValue(InterpExprs(es, fuel, ctx), InterpExprs(es', fuel, ctx'))
    // Auxiliary lemma: if two sequences contain equivalent expressions, evaluating those two
    // sequences in equivalent contexts leads to equivalent results.
    {
      InterpExprs_GEqInterp_Lem(EQ(EqValue, EqState), es, es', fuel, ctx, ctx');
    }

    lemma {:verify false} Map_PairOfMapDisplaySeq_Lem(e: Expr, e': Expr, argvs: seq<WV>, argvs': seq<WV>)
      requires EqSeqValue(argvs, argvs')
      ensures EqPureInterpResult(EqSeqPairEqValueValue,
                                 Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv)),
                                 Seq.MapResult(argvs', argv => PairOfMapDisplaySeq(e', argv)))
    {
      if argvs == [] {}
      else {
        var argv := argvs[0];
        var argv' := argvs'[0];
        assert EqValue(argv, argv');
        assert EqValue(argv, argv');

        var res0 := PairOfMapDisplaySeq(e, argv);
        var res0' := PairOfMapDisplaySeq(e', argv');

        EqValue_HasEqValue_Eq_Forall_Lem();
        if res0.Success? {
          assert res0'.Success?;
          assert EqPureInterpResult(EqPairEqValueValue, res0, res0'); 

          reveal Seq.MapResult();
          Map_PairOfMapDisplaySeq_Lem(e, e', argvs[1..], argvs'[1..]);
        }
        else {
          // Trivial
        }
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

    lemma {:verify false} InterpMapDisplay_EqArgs_Lem(e: Expr, e': Expr, argvs: seq<WV>, argvs': seq<WV>)
      requires EqSeqValue(argvs, argvs')
      ensures EqPureInterpResult(EqMapValue, InterpMapDisplay(e, argvs), InterpMapDisplay(e', argvs')) {
      var res0 := Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv));
      var res0' := Seq.MapResult(argvs', argv => PairOfMapDisplaySeq(e', argv));

      Map_PairOfMapDisplaySeq_Lem(e, e', argvs, argvs');
      EqValue_HasEqValue_Eq_Forall_Lem();

      match res0 {
        case Success(pairs) => {
          var pairs' := res0'.value;

          MapOfPairs_EqArgs_Lem(pairs, pairs');

          var m := MapOfPairs(pairs);
          var m' := MapOfPairs(pairs');
          assert EqMapValue(m, m');
        }
        case Failure(_) => {
          // Trivial
        }
      }
    }

    // TODO: maybe not necessary to make this opaque
    predicate {:verify false} {:opaque} EqInterp_CanBeMapLifted_Pre(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
    {
      && EqState(ctx, ctx')
      && Exprs.ConstructorsMatch(e, e')
      && All_Rel_Forall(EqInterp, e.Children(), e'.Children())
      && SupportsInterp(e)
      && SupportsInterp(e')
    }

    // TODO: maybe not necessary to make this opaque
    predicate {:verify false} {:opaque} EqInterp_CanBeMapLifted_Post(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      EqInterpResultValue(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx'))
    }

    lemma {:verify false} EqInterp_Expr_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 1
    {
      // Note that we don't need to reveal ``InterpExpr``: we just match on the first
      // expression and call the appropriate auxiliary lemma.

      // We need to retrieve some information from the pre:
      // - `SupportsInterp(e)` is necessary to prove that we can't get in the last branch
      //   of the match
      // - `Exprs.ConstructorsMatch(e, e')` is necessary for the lemma preconditions
      assert SupportsInterp(e) && Exprs.ConstructorsMatch(e, e') by {
        reveal EqInterp_CanBeMapLifted_Pre();
      }

      match e {
        case Var(_) => {
          EqInterp_Expr_Var_CanBeMapLifted_Lem(e, e', fuel, ctx, ctx');
        }
        case Literal(_) => {
          EqInterp_Expr_Literal_CanBeMapLifted_Lem(e, e', fuel, ctx, ctx');
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
          reveal SupportsInterp(); // We need this to see that some variants are not supported
          assert false;
        }
      }
    }

    lemma {:verify false}
    EqInterp_Expr_Var_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Var?
      requires e'.Var?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();
        
      reveal InterpExpr();
      reveal TryGetLocal();
      reveal GEqCtx();
    }

    lemma {:verify false}
    EqInterp_Expr_Literal_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Literal?
      requires e'.Literal?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal InterpLiteral();
    }

    lemma {:verify false}
    EqInterp_Expr_Abs_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Abs?
      requires e'.Abs?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

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

    lemma {:verify false}
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

    lemma {:verify false}
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
      reveal GEqCtx();
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
        EqCtx(m, m')
    {
      reveal GEqCtx();
      if pl == [] {}
      else {
        var lastidx := |pl| - 1;
        MapOfPairs_EqCtx_Lem(pl[..lastidx], pl'[..lastidx]);
      }
    }

    // I don't understand why I need to use vcs_split_on_every_assert on this one.
    // For some strange reason it takes ~20s to verify with this, and timeouts without.
    lemma {:verify false} {:vcs_split_on_every_assert}
    MapOfPairs_SeqZip_EqCtx_Lem(vars: seq<string>, argvs: seq<WV>, argvs': seq<WV>)
      requires |argvs| == |argvs'| == |vars|
      requires (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
      ensures
        var m := MapOfPairs(Seq.Zip(vars, argvs));
        var m' := MapOfPairs(Seq.Zip(vars, argvs'));
        EqCtx(m, m')
    {
      var pl := Seq.Zip(vars, argvs);
      var pl' := Seq.Zip(vars, argvs');

      assert |pl| == |pl'|;
      assert forall i | 0 <= i < |pl| :: pl[i].0 == pl'[i].0;
      assert forall i | 0 <= i < |pl| :: EqValue(pl[i].1, pl'[i].1);

      reveal GEqCtx();
      MapOfPairs_EqCtx_Lem(pl, pl');
    }

    lemma {:verify false} EqInterp_Expr_ApplyLazy_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Apply? && e.aop.Lazy?
      requires e'.Apply? && e'.aop.Lazy?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal InterpLazy();

      reveal SupportsInterp();
      
      var res := InterpExpr(e, fuel, ctx);
      var res' := InterpExpr(e', fuel, ctx');
      
      assert res == InterpLazy(e, fuel, ctx);
      assert res' == InterpLazy(e', fuel, ctx');

      // Both expressions should be booleans
      var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
      var op', e0', e1' := e'.aop.lOp, e'.args[0], e'.args[1];
      assert op == op';

      // Evaluate the first boolean
      EqInterp_Lem(e0, e0', fuel, ctx, ctx');
      var res0 := InterpExprWithType(e0, Type.Bool, fuel, ctx);
      var res0' := InterpExprWithType(e0', Type.Bool, fuel, ctx');
      assert EqInterpResultValue(res0, res0');

      match res0 {
        case Success(Return(v0, ctx0)) => {
          var Return(v0', ctx0') := res0'.value;

          EqInterp_Lem(e1, e1', fuel, ctx0, ctx0');
          // The proof fails if we don't introduce res1 and res1'
          var res1 := InterpExprWithType(e1, Type.Bool, fuel, ctx0);
          var res1' := InterpExprWithType(e1', Type.Bool, fuel, ctx0');
          assert EqInterpResultValue(res1, res1');
          assert EqInterpResultValue(res, res');
        }
        case Failure(_) => {
          assert res0'.Failure?;
          assert EqInterpResultValue(res, res');
        }
      }
    }

    lemma {:verify false} EqInterp_Expr_ApplyEager_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.Apply? && e.aop.Eager?
      requires e'.Apply? && e'.aop.Eager?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal SupportsInterp();

      var res := InterpExpr(e, fuel, ctx);
      var res' := InterpExpr(e', fuel, ctx');

      var Apply(Eager(op), args) := e;
      var Apply(Eager(op'), args') := e';

      // The arguments evaluate to similar results
      var res0 := InterpExprs(args, fuel, ctx);
      var res0' := InterpExprs(args', fuel, ctx');
      InterpExprs_EqInterp_Lem(args, args', fuel, ctx, ctx');
      assert EqInterpResult(EqSeqValue, res0, res0');

      match (res0, res0') {
        case (Success(res0), Success(res0')) => {
          // Dafny crashes if we try to deconstruct the `Return`s in the match.
          // See: https://github.com/dafny-lang/dafny/issues/2258
          var Return(argvs, ctx0) := res0;
          var Return(argvs', ctx0') := res0';

          match (op, op') {
            case (UnaryOp(op), UnaryOp(op')) => {
              assert op == op';
              EqInterp_Expr_UnaryOp_CanBeMapLifted_Lem(e, e', op, argvs[0], argvs'[0]);
              assert EqInterpResultValue(res, res');
            }
            case (BinaryOp(bop), BinaryOp(bop')) => {
              assert bop == bop';
              EqInterp_Expr_BinaryOp_CanBeMapLifted_Lem(e, e', bop, argvs[0], argvs[1], argvs'[0], argvs'[1]);
              assert EqInterpResultValue(res, res');
            }
            case (TernaryOp(top), TernaryOp(top')) => {
              assert top == top';
              EqInterp_Expr_TernaryOp_CanBeMapLifted_Lem(e, e', top, argvs[0], argvs[1], argvs[2], argvs'[0], argvs'[1], argvs'[2]);
              assert EqInterpResultValue(res, res');
            }
            case (Builtin(Display(ty)), Builtin(Display(ty'))) => {
              assert ty == ty';
              EqInterp_Expr_Display_CanBeMapLifted_Lem(e, e', ty.kind, argvs, argvs');
              assert EqInterpResultValue(res, res');
            }
            case (FunctionCall(), FunctionCall()) => {
              EqInterp_Expr_FunctionCall_CanBeMapLifted_Lem(e, e', fuel, argvs[0], argvs'[0], argvs[1..], argvs'[1..]);
              assert EqInterpResultValue(res, res');
            }
            case _ => {
              // Impossible branch
              assert false;
            }
          }
        }
        case (Failure(_), Failure(_)) => {
          assert res.Failure?;
          assert res'.Failure?;
          assert EqInterpResultValue(res, res');
        }
        case _ => {
          // Impossible branch
          assert false;
        }
      }
    }

    lemma {:verify false}
    EqInterp_Expr_UnaryOp_CanBeMapLifted_Lem(
      e: Expr, e': Expr, op: UnaryOp, v: WV, v': WV)
      requires !op.MemberSelect?
      requires EqValue(v, v')
      ensures EqPureInterpResultValue(InterpUnaryOp(e, op, v), InterpUnaryOp(e', op, v')) {
      reveal InterpUnaryOp();
      
      var res := InterpUnaryOp(e, op, v);
      var res' := InterpUnaryOp(e', op, v');

      // We make a case disjunction on the final result so as to get
      // information from the fact that the calls to ``Need`` succeeded.
      // The Failure case is trivial.
      if res.Success? {
        match op {
          case BVNot => {
            assert v.BitVector?;
            assert v'.BitVector?;
          }
          case BoolNot => {
            assert v.Bool?;
            assert v'.Bool?;
          }
          case SeqLength => {
            assert v.Seq?;
            assert v'.Seq?;
            assert |v.sq| == |v'.sq|;
          }
          case SetCard => {
            assert v.Set?;
            assert v'.Set?;
            assert |v.st| == |v'.st|;
          }
          case MultisetCard => {
            assert v.Multiset?;
            assert v'.Multiset?;
            assert |v.ms| == |v'.ms|;
          }
          case MapCard => {
            assert v.Map?;
            assert v'.Map?;
            assert |v.m| == |v'.m|;
          }
          case _ => {
            // Impossible branch
            assert false;
          }
        }
      }
      else {
        assert EqPureInterpResultValue(res, res');
      }
    }

    // TODO: we could split this lemma, whose proof is big (though straightforward),
    // but it is a bit annoying to do...
    lemma {:verify false}
    EqInterp_Expr_BinaryOp_CanBeMapLifted_Lem(
      e: Expr, e': Expr, bop: BinaryOp, v0: WV, v1: WV, v0': WV, v1': WV)
      requires !bop.BV? && !bop.Datatypes?
      requires EqValue(v0, v0')
      requires EqValue(v1, v1')
      ensures EqPureInterpResultValue(InterpBinaryOp(e, bop, v0, v1), InterpBinaryOp(e', bop, v0', v1')) {
      reveal InterpBinaryOp();
      
      var res := InterpBinaryOp(e, bop, v0, v1);
      var res' := InterpBinaryOp(e', bop, v0', v1');

      // Below: for the proofs about binary operations involving collections (Set, Map...),
      // see the Set case, which gives the general strategy.
      match bop {
        case Numeric(op) => {
          assert EqPureInterpResultValue(res, res');
        }
        case Logical(op) => {
          assert EqPureInterpResultValue(res, res');
        }
        case Eq(op) => {
          // The proof strategy is similar to the Set case.
          EqValue_HasEqValue_Eq_Lem(v0, v0');
          EqValue_HasEqValue_Eq_Lem(v1, v1');

          // If the evaluation succeeded, it means the calls to ``Need``
          // succeeded, from which we can derive information.
          if res.Success? {
            assert EqPureInterpResultValue(res, res');
          }
          else {
            // trivial
          }
        }
        case Char(op) => {
          assert EqPureInterpResultValue(res, res');
        }
        case Sets(op) => {
          // We make a case disjunction between the "trivial" operations,
          // and the others. We treat the "difficult" operations first.
          // In the case of sets, the trivial operations are those which
          // take two sets as parameters (they are trivial, because if
          // two set values are equivalent according to ``EqValue``, then
          // they are actually equal for ``==`).
          if op.InSet? || op.NotInSet? {
            // The trick is that:
            // - either v0 and v0' have a decidable equality, in which case
            //   the evaluation succeeds, and we actually have that v0 == v0'.
            // - or they don't, in which case the evaluation fails.
            // Of course, we need to prove that v0 has a decidable equality
            // iff v0' has one. The important results are given by the lemma below.
            EqValue_HasEqValue_Eq_Lem(v0, v0');

            if res.Success? {
              assert res'.Success?;

              // If the evaluation succeeded, it means the calls to ``Need``
              // succeeded, from which we can derive information, in particular
              // information about the equality between values, which allows us
              // to prove the goal.
              assert HasEqValue(v0);
              assert HasEqValue(v0');
              assert v0 == v0';

              assert v1.Set?;
              assert v1'.Set?;
              assert v1 == v1';

              assert EqPureInterpResultValue(res, res');
            }
            else {
              // This is trivial
            }
          }
          else {
            // All the remaining operations are performed between sets.
            // ``EqValue`` is true on sets iff they are equal, so
            // this proof is trivial.

            // We enumerate all the cases on purpose, so that this assertion fails
            // if we add more cases, making debugging easier.
            assert || op.SetEq? || op.SetNeq? || op.Subset? || op.Superset? || op.ProperSubset?
                   || op.ProperSuperset? || op.Disjoint? || op.Union? || op.Intersection?
                   || op.SetDifference?;
            assert EqPureInterpResultValue(res, res');
          }
        }
        case Multisets(op) => {
          // Rk.: this proof is similar to the one for Sets
          if op.InMultiset? || op.NotInMultiset? {
            EqValue_HasEqValue_Eq_Lem(v0, v0');
          }
          else if op.MultisetSelect? {
            // Rk.: this proof is similar to the one for Sets
            EqValue_HasEqValue_Eq_Lem(v1, v1');
          }
          else {
            // All the remaining operations are performed between multisets.
            // ``EqValue`` is true on sets iff they are equal, so
            // this proof is trivial.

            // Same as for Sets: we enumerate all the cases on purpose
            assert || op.MultisetEq? || op.MultisetNeq? || op.MultiSubset? || op.MultiSuperset?
                   || op.ProperMultiSubset? || op.ProperMultiSuperset? || op.MultisetDisjoint?
                   || op.MultisetUnion? || op.MultisetIntersection? || op.MultisetDifference?;

            assert EqPureInterpResultValue(res, res');
          }
        }
        case Sequences(op) => {
          // Rk.: the proof strategy is given by the Sets case
          EqValue_HasEqValue_Eq_Lem(v0, v0');
          EqValue_HasEqValue_Eq_Lem(v1, v1');

          if op.SeqDrop? || op.SeqTake? {
            if res.Success? {
              assert res'.Success?;

              var len := |v0.sq|;
              // Doesn't work without this assertion
              assert forall i | 0 <= i < len :: EqValue(v0.sq[i], v0'.sq[i]);
              assert EqPureInterpResultValue(res, res');
            }
            else {
              // Trivial
            }
          }
          else {
            // Same as for Sets: we enumerate all the cases on purpose
            assert || op.SeqEq? || op.SeqNeq? || op.Prefix? || op.ProperPrefix? || op.Concat?
                   || op.InSeq? || op.NotInSeq? || op.SeqSelect?;

            assert EqPureInterpResultValue(res, res');
          }
        }
        case Maps(op) => {
          // Rk.: the proof strategy is given by the Sets case
          EqValue_HasEqValue_Eq_Lem(v0, v0');
          EqValue_HasEqValue_Eq_Lem(v1, v1');

          if op.MapEq? || op.MapNeq? || op.InMap? || op.NotInMap? || op.MapSelect? {
            assert EqPureInterpResultValue(res, res');
          }
          else {
            assert op.MapMerge? || op.MapSubtraction?;

            // Z3 needs a bit of help to prove the equivalence between the maps

            if res.Success? {
              assert res'.Success?;

              // The evaluation succeeds, and returns a map
              var m1 := res.value.m;
              var m1' := res'.value.m;

              // Prove that: |m1| == |m1'|
              assert m1.Keys == m1'.Keys;
              assert |m1| == |m1.Keys|; // This is necessary
              assert |m1'| == |m1'.Keys|; // This is necessary

              assert EqPureInterpResultValue(res, res');
            }
            else {
              // Trivial
            }
          }
        }
      }
    }

    lemma {:verify false}
    EqInterp_Expr_TernaryOp_CanBeMapLifted_Lem(
      e: Expr, e': Expr, top: TernaryOp, v0: WV, v1: WV, v2: WV, v0': WV, v1': WV, v2': WV)
      requires EqValue(v0, v0')
      requires EqValue(v1, v1')
      requires EqValue(v2, v2')
      ensures EqPureInterpResultValue(InterpTernaryOp(e, top, v0, v1, v2), InterpTernaryOp(e', top, v0', v1', v2')) {
      reveal InterpTernaryOp();
      
      var res := InterpTernaryOp(e, top, v0, v1, v2);
      var res' := InterpTernaryOp(e', top, v0', v1', v2');

      match top {
        case Sequences(op) => {}
        case Multisets(op) => {
          EqValue_HasEqValue_Eq_Lem(v1, v1');
        }
        case Maps(op) => {
          EqValue_HasEqValue_Eq_Lem(v1, v1');
        }
      }
    }

    lemma {:verify false}
    EqInterp_Expr_Display_CanBeMapLifted_Lem(
      e: Expr, e': Expr, kind: Types.CollectionKind, vs: seq<WV>, vs': seq<WV>)
      requires EqSeqValue(vs, vs')
      ensures EqPureInterpResultValue(InterpDisplay(e, kind, vs), InterpDisplay(e', kind, vs')) {
      reveal InterpDisplay();
      
      var res := InterpDisplay(e, kind, vs);
      var res' := InterpDisplay(e', kind, vs');

      match kind {
        case Map(_) => {
          InterpMapDisplay_EqArgs_Lem(e, e', vs, vs');
          assert EqPureInterpResultValue(res, res');
        }
        case Multiset => {
          EqValue_HasEqValue_Eq_Forall_Lem();
          if res.Success? {
            assert res'.Success?;
            assert (forall i | 0 <= i < |vs| :: HasEqValue(vs[i]));
            assert (forall i | 0 <= i < |vs| :: HasEqValue(vs'[i]));
            assert (forall i | 0 <= i < |vs| :: EqValue(vs[i], vs'[i]));
            assert vs == vs';
            assert EqPureInterpResultValue(res, res');
          }
          else {}
        }
        case Seq => {
          assert EqPureInterpResultValue(res, res');
        }
        case Set => {
          EqValue_HasEqValue_Eq_Forall_Lem();
          assert EqPureInterpResultValue(res, res');
        }
      }
    }

    lemma {:verify false}
    EqInterp_Expr_FunctionCall_CanBeMapLifted_Lem(
      e: Expr, e': Expr, fuel: nat, f: WV, f': WV, argvs: seq<WV>, argvs': seq<WV>)
      requires EqValue(f, f')
      requires EqSeqValue(argvs, argvs')
      ensures EqPureInterpResultValue(InterpFunctionCall(e, fuel, f, argvs), InterpFunctionCall(e', fuel, f', argvs')) {      
      var res := InterpFunctionCall(e, fuel, f, argvs);
      var res' := InterpFunctionCall(e', fuel, f', argvs');

      if res.Success? || res'.Success? {
        reveal InterpFunctionCall();
        reveal InterpCallFunctionBody();
        reveal EqValue_Closure();

        var Closure(ctx, vars, body) := f;
        var Closure(ctx', vars', body') := f';
        assert |vars| == |vars'|;

        // We have restrictions on the arguments on which we can apply the equivalence relation
        // captured by ``EqValue_Closure``. We do the assumption that, if one of the calls succeedeed,
        // then the arguments are "not too big" and we can apply the equivalence. This would be true
        // if the program was successfully type-checked.
        assume (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs[i]) < ValueTypeHeight(f));
        assume (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs'[i]) < ValueTypeHeight(f'));

        var res0 := InterpCallFunctionBody(f, fuel - 1, argvs);
        var res0' := InterpCallFunctionBody(f', fuel - 1, argvs');
        // This comes from EqValue_Closure
        assert EqPureInterpResultValue(res0, res0');

        // By definition
        assert res0 == res;
        assert res0' == res';

        assert EqPureInterpResultValue(res, res');
      }
      else {
        assert res.Failure? && res'.Failure?;
      }
    }

    lemma {:verify false} EqInterp_Expr_If_CanBeMapLifted_Lem(e: Expr, e': Expr, fuel: nat, ctx: State, ctx': State)
      requires e.If?
      requires e'.If?
      requires EqInterp_CanBeMapLifted_Pre(e, e', fuel, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', fuel, ctx, ctx')
      decreases e, fuel, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal SupportsInterp();

      var res := InterpExpr(e, fuel, ctx);
      var res' := InterpExpr(e', fuel, ctx');

      var If(cond, thn, els) := e;
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

      var res0 := InterpExprWithType(cond, Type.Bool, fuel, ctx);
      var res0' := InterpExprWithType(cond', Type.Bool, fuel, ctx');

      EqInterp_Lem(cond, cond', fuel, ctx, ctx');
      assert EqInterpResultValue(res0, res0');

      if res0.Success? {
        var Return(condv, ctx0) := res0.value;
        var Return(condv', ctx0') := res0'.value;

        EqInterp_Lem(thn, thn', fuel, ctx0, ctx0'); // Proof fails without this
        EqInterp_Lem(els, els', fuel, ctx0, ctx0'); // Proof fails without this
      }
      else {
        // Trivial
      }
    }

    lemma {:verify false} EqInterp_CanBeMapLifted_Lem()
      ensures RelCanBeMapLifted(EqInterp)
    {
      forall e, e'
        ensures
           (&& Exprs.ConstructorsMatch(e, e')
            && All_Rel_Forall(EqInterp, e.Children(), e'.Children()))
            ==> EqInterp(e, e')
      {
        if && Exprs.ConstructorsMatch(e, e')
           && All_Rel_Forall(EqInterp, e.Children(), e'.Children()) {
          if SupportsInterp(e) {
            reveal SupportsInterp();
            assert SupportsInterp(e');

            forall fuel, ctx, ctx' | EqState(ctx, ctx') ensures
              EqInterpResultValue(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx')) {
              reveal EqInterp_CanBeMapLifted_Pre();
              reveal EqInterp_CanBeMapLifted_Post();
              EqInterp_Expr_CanBeMapLifted_Lem(e, e', fuel, ctx, ctx');
            }
          }
          else {}
        }
        else {}
      }
    }

  }

  abstract module Pass {
    // Abstract module describing a compiler pass.

    import opened DafnyCompilerCommon.AST
    import opened Equiv

    // The precondition of the transformation
    predicate Tr_Pre(p: Program)

    // The postcondition of the transformation
    predicate Tr_Post(p: Program)

    // The transformation itself.
    //
    // For now, we enforce the use of ``EqInterp`` as the binary relation between
    // the input and the output.
    function method Apply(p: Program) : (p': Program)
      requires Tr_Pre(p)
      ensures Tr_Post(p)
      ensures EqInterp(p.mainMethod.methodBody, p'.mainMethod.methodBody)
  }

  // TODO: I don't manage to make ``EliminateNegatedBinops`` refine ``Pass``
  module EliminateNegatedBinops {
    // This module implements a simple pass, by which we decompose the "negated" binops
    // into a negation of the "original" binop.
    //
    // Ex.:
    // ====
    // ```
    // x !in set    ~~>   !(x in set)
    // ```
    
    import DCC = DafnyCompilerCommon
    import Lib
    import Lib.Debug
    import opened Lib.Datatypes
    import opened Rewriter.BottomUp

    import opened DafnyCompilerCommon.AST
    import opened DCC.Predicates
    import opened Transformer
    import opened Interp
    import opened Values
    import opened Equiv

    function method {:verify false} FlipNegatedBinop_Aux(op: BinaryOps.BinaryOp) :
      (op': BinaryOps.BinaryOp)
    // Auxiliary function (no postcondition)
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

    function method {:verify false} FlipNegatedBinop(op: BinaryOps.BinaryOp) :
      (op': BinaryOps.BinaryOp)
      ensures !IsNegatedBinop(op')
    {
      FlipNegatedBinop_Aux(op)
    }

    predicate method {:verify false} IsNegatedBinop(op: BinaryOps.BinaryOp) {
      FlipNegatedBinop_Aux(op) != op
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

    predicate {:verify false} Tr_Expr_Post(e: Exprs.T) {
      NotANegatedBinopExpr(e)
    }

    predicate {:verify false} Tr_Expr_Rel(e: Exprs.T, e': Exprs.T) {
      EqInterp(e, e')
    }

    function method {:verify false} FlipNegatedBinop_Expr(op: BinaryOp, args: seq<Expr>) : (e':Exprs.T)
      requires IsNegatedBinop(op)
      requires EagerOpSupportsInterp(Exprs.BinaryOp(op))
      ensures (|args| == 2 && (forall i | 0 <= i < |args| :: SupportsInterp(args[i]))) ==> SupportsInterp(e')
    {
      reveal SupportsInterp();
      var si := (|args| == 2 && (forall i | 0 <= i < |args| :: SupportsInterp(args[i])));

      var bop' := Exprs.BinaryOp(FlipNegatedBinop(op));
      var flipped := Exprs.Apply(Exprs.Eager(bop'), args);
      
      assert si ==> SupportsInterp(flipped);
      
      var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [flipped]);
      
      assert SupportsInterp(flipped) ==> SupportsInterp(e');
      e'
    }

    lemma {:verify false} FlipNegatedBinop_Binop_Rel_Lem(
      e: Expr, e': Expr, op: BinaryOp, v0: WV, v1: WV, v0': WV, v1': WV)
      requires IsNegatedBinop(op)
      requires EagerOpSupportsInterp(Exprs.BinaryOp(op))
      requires EqValue(v0, v0')
      requires EqValue(v1, v1')
      ensures (
        match (InterpBinaryOp(e, op, v0, v1), InterpBinaryOp(e', FlipNegatedBinop(op), v0', v1'))
          case (Success(b), Success(b')) =>
            && b.Bool?
            && b'.Bool?
            && b.b == ! b'.b
          case (Failure(_), Failure(_)) =>
            true
          case _ =>
            false)
      {
        reveal InterpBinaryOp();
        EqValue_HasEqValue_Eq_Lem(v0, v0');
        EqValue_HasEqValue_Eq_Lem(v1, v1');
      }

    lemma {:verify false} FlipNegatedBinop_Expr_Rel_Lem(op: BinaryOp, args: seq<Expr>)
      requires IsNegatedBinop(op)
      ensures (
        var e := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(op)), args);
        var e' := FlipNegatedBinop_Expr(op, args);
        Tr_Expr_Rel(e, e')
      )
    {
      reveal InterpExpr();
      reveal InterpFunctionCall();
      reveal InterpBinaryOp();

      var bop := Exprs.BinaryOp(op);
      var bop' := Exprs.BinaryOp(FlipNegatedBinop(op));
      var e := Exprs.Apply(Exprs.Eager(bop), args);
      var e' := FlipNegatedBinop_Expr(op, args);
      reveal SupportsInterp(); // TODO: remove?

      if SupportsInterp(e) {
        assert SupportsInterp(e');

        // Prove that for every fuel and context, the interpreter returns the same result
        forall fuel, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, fuel, ctx), InterpExpr(e', fuel, ctx')) {
          var res := InterpExpr(e, fuel, ctx);
          var res' := InterpExpr(e', fuel, ctx');

          var args_res := InterpExprs(args, fuel, ctx);
          var args_res' := InterpExprs(args, fuel, ctx');
          EqInterp_Seq_Refl_Lem(args);
          InterpExprs_EqInterp_Lem(args, args, fuel, ctx, ctx');
          assert EqInterpResultSeqValue(args_res, args_res');

          var flipped := Exprs.Apply(Exprs.Eager(bop'), args);
          InterpExprs1_Strong_Lem(flipped, fuel, ctx');

          if args_res.Success? {
            assert args_res'.Success?;

            var Return(vs, ctx1) := args_res.value;
            var Return(vs', ctx1') := args_res'.value;

            var res1 := InterpBinaryOp(e, op, vs[0], vs[1]);
            var res1' := InterpBinaryOp(e', FlipNegatedBinop(op), vs'[0], vs'[1]);
            FlipNegatedBinop_Binop_Rel_Lem(e, e', op, vs[0], vs[1], vs'[0], vs'[1]);

            assert res1.Success? == res1'.Success?;
            if res1.Success? {
              var b := res1.value;
              var b' := res1'.value;

              assert b.Bool?;
              assert b'.Bool?;
              assert b.b == !b'.b;
              
              assert EqState(ctx1, ctx1');

              reveal InterpUnaryOp();
            }
            else {
              // Trivial
            }
          }
          else {
            // Trivial
          }
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
      EqInterp_Refl_Lem(e);
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

    lemma {:verify false} TransformationAndRel_Lift_Lem(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
      requires RelIsTransitive(rel)
      requires RelCanBeMapLifted(rel)
      requires TransformerShallowPreservesRel(f, rel)
      ensures TransformerDeepPreservesRel(f, rel)
    {}

    lemma {:verify false} TrPreservesRel()
      ensures TransformerDeepPreservesRel(Tr_Expr_Shallow, Tr_Expr_Rel)
    {
      var f := Tr_Expr_Shallow;
      var rel := Tr_Expr_Rel;

      EqInterp_IsTransitive_Lem();
      EqInterp_CanBeMapLifted_Lem();
      TransformationAndRel_Lift_Lem(f, rel);
    }

    const {:verify false} Tr_Expr : BottomUpTransformer :=
      ( TrMatchesPrePost();
        TrPreservesPre();
        TrPreservesRel();
        TR(Tr_Expr_Shallow,
           Tr_Expr_Post,
           Tr_Expr_Rel))


    predicate {:verify false} Tr_Pre(p: Program) {
      true
    }

    predicate {:verify false} Tr_Post(p: Program)
    {
      Deep.All_Program(p, Tr_Expr_Post)
    }

    lemma {:verify false} Tr_Pre_Expr_IsTrue(e: Expr)
      ensures Deep.All_Expr(e, Tr_Expr.f.requires)
      decreases e, 1
    // It is not obvious that `Deep.All_Expr(e, _ => true)` is true...
    // Also, because the functions encoding is not very precise, we can't
    // use the lemma ``Deep.All_Expr_true``.
    {
      Tr_Pre_ChildrenExpr_IsTrue(e);
    }

    lemma {:verify false} Tr_Pre_ChildrenExpr_IsTrue(e: Expr)
      ensures Deep.AllChildren_Expr(e, Tr_Expr.f.requires)
      decreases e, 0
    {
      forall e' | e' in e.Children() { Tr_Pre_Expr_IsTrue(e'); }
    }

    function method {:verify false} Apply(p: Program) : (p': Program)
      requires Tr_Pre(p)
      ensures Tr_Post(p')
      ensures Tr_Expr_Rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
    {
      Tr_Pre_Expr_IsTrue(p.mainMethod.methodBody);
      assert Deep.All_Program(p, Tr_Expr.f.requires);
      Map_Program(p, Tr_Expr)
    }
  }
}
