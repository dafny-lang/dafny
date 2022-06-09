include "CSharpDafnyASTModel.dfy"
include "CSharpInterop.dfy"
include "CSharpDafnyInterop.dfy"
include "CSharpDafnyASTInterop.dfy"
include "Library.dfy"
include "StrTree.dfy"
include "AST.dfy"
include "Translator.dfy"

module {:extern "DafnyInDafny"} DafnyCompilerCommon {
  import System
  import CSharpDafnyASTModel
  import opened CSharpInterop
  import opened CSharpDafnyInterop
  import opened Microsoft.Dafny
  import StrTree

  module Predicates {
    import opened AST

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

        //
        // Functions
        //

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

        //
        // Lemmas
        //

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

        //
        // Miscelleanous
        //

        function IsTrue(e:Expr): bool { true }
      }

      module Rec refines Base { // DISCUSS
        function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
          P(e) &&
          // BUG(https://github.com/dafny-lang/dafny/issues/2107)
          // BUG(https://github.com/dafny-lang/dafny/issues/2109)
          // Duplicated to avoid mutual recursion with AllChildren_Expr
          match e {
            case Var(_) => true
            case Literal(lit) => true
            case Abs(vars, body) => All_Expr(body, P)
            case Apply(_, exprs) =>
              Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
            case Block(exprs) =>
              Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
            case Bind(vars, vals, body) =>
              && Seq.All((e requires e in vals => All_Expr(e, P)), vals)
              && All_Expr(body, P)
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
            case Block(exprs) =>
              Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
            case Bind(vars, vals, body) =>
              && Seq.All((e requires e in vals => All_Expr(e, P)), vals)
              && All_Expr(body, P)
            case If(cond, thn, els) =>
              All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
          }
        }

        lemma All_Expr_true(e: Expr)
          ensures All_Expr(e, IsTrue)
          decreases e, 1
        {
          AllChildren_Expr_true(e);
        }

        lemma AllChildren_Expr_true(e: Expr)
          ensures AllChildren_Expr(e, IsTrue)
          decreases e, 0
        {
          forall e' | e' in e.Children() { All_Expr_true(e'); }
        }

        lemma AllImpliesChildren ... {}

        lemma All_Expr_weaken ... {
          AllChildren_Expr_weaken(e, P, Q);
        }

        lemma AllChildren_Expr_weaken ... { // NEAT
          forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
        }
      }

      module NonRec refines Base {
        // BUG(https://github.com/dafny-lang/dafny/issues/2107)
        // BUG(https://github.com/dafny-lang/dafny/issues/2109)
        function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
          P(e) && forall e' | e' in e.Children() :: All_Expr(e', P)
        }

        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
          forall e' | e' in e.Children() :: All_Expr(e', P)
        }

        lemma All_Expr_true(e: Expr)
          ensures All_Expr(e, IsTrue)
          decreases e, 1
        {
          AllChildren_Expr_true(e);
        }

        lemma AllChildren_Expr_true(e: Expr)
          ensures AllChildren_Expr(e, IsTrue)
          decreases e, 0
        {
          forall e' | e' in e.Children() { All_Expr_true(e'); }
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
    module Deep refines DeepImpl.NonRec {}
  }
}
