include "../CSharpDafnyASTModel.dfy"
include "../CSharpInterop.dfy"
include "../CSharpDafnyInterop.dfy"
include "../CompilerCommon.dfy"
include "../Library.dfy"
include "../StrTree.dfy"

module {:extern "DafnyInDafny.CSharp"} CSharpDafnyCompiler {
  import CSharpDafnyASTModel
  import opened CSharpDafnyInterop
  import opened Microsoft.Dafny
  import StrTree
  import DafnyCompilerCommon.Simplifier
  import DafnyCompilerCommon.Translator

  module Compiler {
    import opened StrTree_ = StrTree
    import opened CSharpDafnyInterop
    import opened DafnyCompilerCommon.AST
    import DafnyCompilerCommon.Predicates
    import DafnyCompilerCommon.Simplifier
    import opened Predicates.Deep

    function method CompileType(t: Type): StrTree {
      match t {
        case Bool() => Str("bool")
        case Char() => Str("char")
        case Int() => Str("BigInteger")
        case Real() => Str("BigRational")
        case Collection(true, collKind, eltType) =>
          var eltStr := CompileType(eltType);
          match collKind {
            case Map(domType) =>
              var domStr := CompileType(domType);
              Format("DafnyRuntime.Map<{},{}>", [domStr, eltStr])
            case Multiset() => Format("DafnyRuntime.Multiset<{}>", [eltStr])
            case Seq() => Format("DafnyRuntime.Sequence<{}>", [eltStr])
            case Set() => Format("DafnyRuntime.Set<{}>", [eltStr])
          }
        case BigOrdinal() => Unsupported
        case BitVector(_) => Unsupported
        case Collection(false, collKind_, eltType_) => Unsupported
        case Class(_) => Unsupported
        case Function(_, _) => Unsupported
        case Unit => Unsupported
      }
    }

    function method CompileInt(i: int) : StrTree {
      var istr := Lib.Str.of_int(i, 10);
      Call(Str("new BigInteger"), [Str(istr)])
    }

    function method CompileLiteralExpr(l: Exprs.Literal) : StrTree {
      match l {
        case LitBool(b: bool) => Str(if b then "true" else "false")
        case LitInt(i: int) => CompileInt(i)
        case LitReal(r: real) =>
          var n := TypeConv.Numerator(r);
          var d := TypeConv.Denominator(r);
          Call(Str("new BigRational"), [CompileInt(n), CompileInt(d)])
        case LitChar(c: char) => SingleQuote(c)
        case LitString(s: string, verbatim: bool) => DoubleQuote(s) // FIXME verbatim
      }
    }

    function method CompileDisplayExpr(ty: Type, exprs: seq<StrTree>): StrTree
    {
      var tyStr := CompileType(ty);
      Call(Format("{}.FromElements", [tyStr]), exprs)
    }

    function method CompileLazyExpr(op: Exprs.LazyOp, c0: StrTree, c1: StrTree) : StrTree
    {
      var fmt := str requires countFormat(str) == 2 =>
        Format(str, [c0, c1]);
      var bin := str =>
        Format("({} {} {})", [c0, Str(str), c1]);
      var rbin := str =>
        Format("({} {} {})", [c1, Str(str), c0]);
      match op {
        case Imp => fmt("(!{} || {})")
        case And => bin("&&")
        case Or => bin("||")
      }
    }

    function method CompileUnaryOpExpr(op: UnaryOp, c: StrTree) : StrTree {
      match op {
        case BoolNot() => Format("!{}", [c])
        case BVNot() => Format("!{}", [c])
        case SeqLength() => Unsupported
        case SetCard() => Unsupported
        case MultisetCard() => Unsupported
        case MapCard() => Unsupported
        case MemberSelect(_) => Unsupported
      }
    }

    function method CompileBinaryExpr(op: BinaryOp, c0: StrTree, c1: StrTree) : StrTree
      requires !Simplifier.IsNegatedBinop(op)
    {
      var fmt := str requires countFormat(str) == 2 =>
        Format(str, [c0, c1]); // Cute use of function precondition
      var bin := str =>
        Format("({} {} {})", [c0, Str(str), c1]);
      var rbin := str =>
        Format("({} {} {})", [c1, Str(str), c0]);
      match op {
        case Logical(Iff) => bin("==")

        case Eq(EqCommon) => Unsupported

        case Numeric(Lt) => bin("<")
        case Numeric(Le) => bin("<=")
        case Numeric(Ge) => bin(">=")
        case Numeric(Gt) => bin(">")
        case Numeric(Add) => bin("+")
        case Numeric(Sub) => bin("-")
        case Numeric(Mul) => bin("*")
        case Numeric(Div) => bin("/")
        case Numeric(Mod) => bin("%") // FIXME

        case BV(LeftShift) => bin("<<")
        case BV(RightShift) => bin(">>")
        case BV(BitwiseAnd) => bin("&")
        case BV(BitwiseOr) => bin("|")
        case BV(BitwiseXor) => bin("^")

        case Char(LtChar) => bin("<")
        case Char(LeChar) => bin("<=")
        case Char(GeChar) => bin(">=")
        case Char(GtChar) => bin(">")
        // FIXME: Why is there lt/le/gt/ge for chars?

        case Sequences(SeqEq) => fmt("{}.Equals({})")
        case Sequences(ProperPrefix) => Unsupported
        case Sequences(Prefix) => Unsupported
        case Sequences(Concat) => Unsupported
        case Sequences(InSeq) => Unsupported
        case Sequences(SeqSelect) => Unsupported
        case Sequences(SeqTake) => Unsupported
        case Sequences(SeqDrop) => Unsupported

        case Sets(SetEq) => fmt("{}.Equals({})")
        case Sets(ProperSubset) => Unsupported
        case Sets(Subset) => Unsupported
        case Sets(Superset) => Unsupported
        case Sets(ProperSuperset) => Unsupported
        case Sets(Disjoint) => Unsupported
        case Sets(InSet) => rbin("{}.Contains({})")
        case Sets(Union) => Unsupported
        case Sets(Intersection) => Unsupported
        case Sets(SetDifference) => Unsupported

        case Multisets(MultisetEq) => fmt("{}.Equals({})")
        case Multisets(MultiSubset) => Unsupported
        case Multisets(MultiSuperset) => Unsupported
        case Multisets(ProperMultiSubset) => Unsupported
        case Multisets(ProperMultiSuperset) => Unsupported
        case Multisets(MultisetDisjoint) => Unsupported
        case Multisets(InMultiset) => rbin("{}.Contains({})")
        case Multisets(MultisetUnion) => Unsupported
        case Multisets(MultisetIntersection) => Unsupported
        case Multisets(MultisetDifference) => Unsupported
        case Multisets(MultisetSelect) => Unsupported

        case Maps(MapEq) => fmt("{}.Equals({})")
        case Maps(InMap) => rbin("{}.Contains({})")
        case Maps(MapMerge) => Unsupported
        case Maps(MapSubtraction) => Unsupported
        case Maps(MapSelect) => Unsupported

        case Datatypes(RankLt) => Unsupported
        case Datatypes(RankGt) => Unsupported
      }
    }

    function method CompilePrint(e: Expr) : StrTree
      decreases e, 1
      requires All_Expr(e, Simplifier.NotANegatedBinopExpr)
      requires All_Expr(e, Exprs.WellFormed)
    {
      StrTree_.Seq([Call(Str("DafnyRuntime.Helpers.Print"), [CompileExpr(e)]), Str(";")])
    }

    function method CompileExpr(e: Expr) : StrTree
      requires Deep.All_Expr(e, Simplifier.NotANegatedBinopExpr)
      requires Deep.All_Expr(e, Exprs.WellFormed)
      decreases e, 0
    {
      Predicates.Deep.AllImpliesChildren(e, Simplifier.NotANegatedBinopExpr);
      Predicates.Deep.AllImpliesChildren(e, Exprs.WellFormed);
      match e {
        case Var(_) =>
          Unsupported
        case Literal(l) =>
          CompileLiteralExpr(l)
        case Abs(_, _) =>
          Unsupported
        case Apply(op, es) =>
          match op {
            case Lazy(op) =>
              var c0, c1 := CompileExpr(es[0]), CompileExpr(es[1]);
              CompileLazyExpr(op, c0, c1) // FIXME should be lazy
            case Eager(UnaryOp(op)) =>
              var c := CompileExpr(es[0]);
              CompileUnaryOpExpr(op, c)
            case Eager(BinaryOp(op)) =>
              var c0, c1 := CompileExpr(es[0]), CompileExpr(es[1]);
              CompileBinaryExpr(op, c0, c1)
            case Eager(TernaryOp(op)) => Unsupported
            case Eager(Builtin(Display(ty))) =>
              CompileDisplayExpr(ty, Lib.Seq.Map((e requires e in es => CompileExpr(e)), es))
            case Eager(Builtin(Print)) =>
              Concat("\n", Lib.Seq.Map(e requires e in es => CompilePrint(e), es))
            case Eager(DataConstructor(name, typeArgs)) => Unsupported
            case Eager(FunctionCall()) => Unsupported
          }
        case Block(exprs) =>
          Concat("\n", Lib.Seq.Map(e requires e in exprs => CompileExpr(e), exprs))
        case If(cond, thn, els) =>
          var cCond := CompileExpr(cond);
          var cThn := CompileExpr(thn);
          var cEls := CompileExpr(els);
          // FIXME block structure
          Concat("\n", [SepSeq(Lib.Datatypes.None, [Str("if ("), cCond, Str(") {")]),
                        SepSeq(Lib.Datatypes.None, [Str("  "), cThn]),
                        Str("} else {"),
                        SepSeq(Lib.Datatypes.None, [Str("  "), cEls]),
                        Str("}")])
      }
    }

    function method CompileMethod(m: Method) : StrTree
      requires Deep.All_Method(m, Simplifier.NotANegatedBinopExpr)
      requires Deep.All_Method(m, Exprs.WellFormed)
    {
      match m {
        case Method(nm, methodBody) => CompileExpr(methodBody)
      }
    }

    function method CompileProgram(p: Program) : StrTree
      requires Deep.All_Program(p, Simplifier.NotANegatedBinopExpr)
      requires Deep.All_Program(p, Exprs.WellFormed)
    {
      match p {
        case Program(mainMethod) => CompileMethod(mainMethod)
      }
    }

    method AlwaysCompileProgram(p: Program) returns (st: StrTree)
      requires Deep.All_Program(p, Simplifier.NotANegatedBinopExpr)
    {
      // TODO: this property is tedious to propagate so isn't complete yet
      if Deep.All_Program(p, Exprs.WellFormed) {
        st := CompileProgram(p);
      } else {
        st := StrTree.Str("// Invalid program.");
      }
    }
  }

  method WriteAST(wr: CSharpDafnyInterop.SyntaxTreeAdapter, ast: StrTree.StrTree) {
    match ast {
      case Str(s) =>
        wr.Write(s);
      case SepSeq(sep, asts) =>
        for i := 0 to |asts| {
          if i != 0 && sep.Some? {
            wr.Write(sep.value);
          }
          WriteAST(wr, asts[i]);
        }
      case Unsupported() =>
    }
  }

  class {:extern} DafnyCSharpCompiler {
    constructor() {
    }

    method Compile(dafnyProgram: CSharpDafnyASTModel.Program,
                   wr: ConcreteSyntaxTree) {
      var st := new CSharpDafnyInterop.SyntaxTreeAdapter(wr);
      match Translator.TranslateProgram(dafnyProgram) {
        case Success(translated) =>
          var lowered := Simplifier.EliminateNegatedBinops(translated);
          var compiled := Compiler.AlwaysCompileProgram(lowered);
          WriteAST(st, compiled);
        case Failure(err) => // FIXME return an error
          st.Write("!! Translation error: " + err.ToString());
      }
      st.Write("\n");
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
