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
    import opened DafnyCompilerCommon.AST
    import opened AST.Expr
    import opened StrTree_ = StrTree
    import opened CSharpDafnyInterop
    import DafnyCompilerCommon.Predicates
    import DafnyCompilerCommon.Simplifier
    import opened Predicates.Deep

    function method CompileType(t: Type.Type): StrTree {
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
            case Multiset() => Format("DafnyRuntime.MultiSet<{}>", [eltStr])
            case Seq() => Format("DafnyRuntime.Sequence<{}>", [eltStr])
            case Set() => Format("DafnyRuntime.Set<{}>", [eltStr])
          }
        case BigOrdinal() => Unsupported
        case BitVector(_) => Unsupported
        case Collection(false, collKind_, eltType_) => Unsupported
        case UnsupportedType(_) => Unsupported
      }
    }

    function method CompileInt(i: int) : StrTree {
      var istr := Lib.Str.of_int(i, 10);
      Call(Str("new BigInteger"), [Str(istr)])
    }

    function method CompileLiteralExpr(l: Expr.Literal) : StrTree {
      match l {
        case LitBool(b: bool) => Str(if b then "true" else "false")
        case LitInt(i: int) => CompileInt(i)
        case LitReal(r: real) =>
          var n := TypeConv.Numerator(r);
          var d := TypeConv.Denominator(r);
          Call(Str("new BigRational"), [CompileInt(n), CompileInt(d)])
        case LitChar(c: string) => SingleQuote(Str(c))
        case LitString(s: string, verbatim: bool) => DoubleQuote(Str(s)) // FIXME verbatim
      }
    }

    function method CompileDisplayExpr(ty: Type.Type, exprs: seq<StrTree>): StrTree
    {
      var tyStr := CompileType(ty);
      Call(Format("{}.FromElements", [tyStr]), exprs)
    }

    function method CompileUnaryOpExpr(op: UnaryOp.Op, c: StrTree) : StrTree {
      match op {
        case Not() => Format("!{}", [c]) // LATER use resolved op, which distinguishes between BV and boolean
        case Cardinality() => Unsupported
        case Fresh() => Unsupported
        case Allocated() => Unsupported
        case Lit() => Unsupported
      }
    }

    function method CompileBinaryExpr(op: BinaryOp.Op, c0: StrTree, c1: StrTree) : StrTree
      requires !Simplifier.IsNegatedBinop(op)
    {
      var fmt := str requires countFormat(str) == 2 =>
        Format(str, [c0, c1]); // Cute use of function precondition
      var bin := str =>
        Format("{} {} {}", [c0, Str(str), c1]);
      var rbin := str =>
        Format("{} {} {}", [c1, Str(str), c0]);
      match op {
        case Logical(Iff) => bin("==")
        case Logical(Imp) => fmt("!{} || {}")
        case Logical(And) => bin("&&")
        case Logical(Or) => bin("||")

        case Eq(EqCommon) => Unsupported

        case Numeric(Lt) => bin("<")
        case Numeric(Le) => bin("<=")
        case Numeric(Ge) => bin(">=")
        case Numeric(Gt) => bin(">")
        case Numeric(Add) => Unsupported
        case Numeric(Sub) => Unsupported
        case Numeric(Mul) => Unsupported
        case Numeric(Div) => Unsupported
        case Numeric(Mod) => Unsupported

        case BV(LeftShift) => Unsupported
        case BV(RightShift) => Unsupported
        case BV(BitwiseAnd) => bin("&")
        case BV(BitwiseOr) => bin("|")
        case BV(BitwiseXor) => bin("^")

        case Char(LtChar) => bin("<")
        case Char(LeChar) => bin("<=")
        case Char(GeChar) => bin(">=")
        case Char(GtChar) => bin(">")
        // FIXME: Why is there lt/le/gt/ge for chars trt not binops?

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

        case MultiSets(MultiSetEq) => fmt("{}.Equals({})")
        case MultiSets(MultiSubset) => Unsupported
        case MultiSets(MultiSuperset) => Unsupported
        case MultiSets(ProperMultiSubset) => Unsupported
        case MultiSets(ProperMultiSuperset) => Unsupported
        case MultiSets(MultiSetDisjoint) => Unsupported
        case MultiSets(InMultiSet) => rbin("{}.Contains({})")
        case MultiSets(MultiSetUnion) => Unsupported
        case MultiSets(MultiSetIntersection) => Unsupported
        case MultiSets(MultiSetDifference) => Unsupported

        case Sequences(SeqEq) => fmt("{}.Equals({})")
        case Sequences(ProperPrefix) => Unsupported
        case Sequences(Prefix) => Unsupported
        case Sequences(Concat) => Unsupported
        case Sequences(InSeq) => Unsupported

        case Maps(MapEq) => fmt("{}.Equals({})")
        case Maps(InMap) => rbin("{}.Contains({})")
        case Maps(MapMerge) => Unsupported
        case Maps(MapSubtraction) => Unsupported

        case Datatypes(RankLt) => Unsupported
        case Datatypes(RankGt) => Unsupported
      }
    }

    function method CompilePrint(e: Expr.t) : StrTree
      decreases e, 1
      requires All_Expr(e, Simplifier.NotANegatedBinopExpr)
      requires All_Expr(e, Expr.WellFormed)
    {
      StrTree_.Seq([Call(Str("DafnyRuntime.Helpers.Print"), [CompileExpr(e)]), Str(";")])
    }

    function method CompileExpr(e: Expr.t) : StrTree
      requires Deep.All_Expr(e, Simplifier.NotANegatedBinopExpr)
      requires Deep.All_Expr(e, Expr.WellFormed)
      decreases e, 0
    {
      Predicates.AllImpliesChildren(e, Simplifier.NotANegatedBinopExpr);
      Predicates.AllImpliesChildren(e, Expr.WellFormed);
      match e {
        case Literal(l) =>
          CompileLiteralExpr(l)
        case UnaryOp(op, e') =>
          var c := CompileExpr(e');
          CompileUnaryOpExpr(op, c)
        case Binary(op, e0, e1) =>
          var c0, c1 := CompileExpr(e0), CompileExpr(e1);
          CompileBinaryExpr(op, c0, c1)
        case Apply(UnaryOp(op), es) =>
          var c := CompileExpr(es[0]);
          CompileUnaryOpExpr(op, c)
        case Apply(BinaryOp(op), es) =>
          var c0, c1 := CompileExpr(es[0]), CompileExpr(es[1]);
          CompileBinaryExpr(op, c0, c1)
        case Apply(Function(e), es) => Unsupported
        case Apply(ClassConstructor(classType), es) => Unsupported
        case Apply(DataConstructor(name, typeArgs), es) => Unsupported
        case Apply(ClassMethod(receiver, name, typeArgs), es) => Unsupported
        case Display(ty, exprs) =>
          CompileDisplayExpr(ty, Lib.Seq.Map((e requires e in exprs => CompileExpr(e)), exprs))
        case Invalid(_) => Unsupported
        case UnsupportedExpr(_) => Unsupported

        case Block(exprs) =>
          Concat("\n", Lib.Seq.Map(e requires e in exprs => CompileExpr(e), exprs))
        case Print(exprs) =>
          Concat("\n", Lib.Seq.Map(e requires e in exprs => CompilePrint(e), exprs))
        case UnsupportedStmt(_) => Unsupported
      }
    }

    function method CompileMethod(m: Method) : StrTree
      requires Deep.All_Method(m, Simplifier.NotANegatedBinopExpr)
      requires Deep.All_Method(m, Expr.WellFormed)
    {
      match m {
        case Method(nm, methodBody) => CompileExpr(methodBody)
      }
    }

    function method CompileProgram(p: Program) : StrTree
      requires Deep.All_Program(p, Simplifier.NotANegatedBinopExpr)
      requires Deep.All_Program(p, Expr.WellFormed)
    {
      match p {
        case Program(mainMethod) => CompileMethod(mainMethod)
      }
    }

    method AlwaysCompileProgram(p: Program) returns (st: StrTree)
      requires Deep.All_Program(p, Simplifier.NotANegatedBinopExpr)
    {
      // TODO: this property is tedious to propagate so isn't complete yet
      if Deep.All_Program(p, WellFormed) {
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
            wr.Write(sep.t);
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
      var translated := Translator.TranslateProgram(dafnyProgram);
      var lowered := Simplifier.EliminateNegatedBinops(translated);
      var compiled := Compiler.AlwaysCompileProgram(lowered);
      WriteAST(st, compiled);
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
