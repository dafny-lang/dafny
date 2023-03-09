using Antlr4.Runtime;

// This is the C# frontend of a compiler for a simple arithmetic language.  Th// backend is written in Dafny, except for the final IO stage (printing program// to stdout).

namespace SimpleCompiler {

  // First we define a class hierarchy that models the abstract syntax trees of
  // our programs (see the Dafny side for more info on the language):

  namespace CSharpAST {
    public class AST { } // ANTLR roo
    public class Expr : AST { }

    public class Const : Expr {
      public int n;

      public Const(int n) {
        this.n = n;
      }
    }

    public class Var : Expr {
      public string v;

      public Var(string v) {
        this.v = v;
      }
    }

    public class Op : Expr {
      public enum BinOp { Add, Sub }

      public BinOp op;
      public Expr e1, e2;

      public Op(BinOp op, Expr e1, Expr e2) {
        this.e1 = e1;
        this.e2 = e2;
      }
    }

    public class Stmt : AST { }

    public class Print : Stmt {
      public Expr e;

      public Print(Expr e) {
        this.e = e;
      }
    }

    public class Assign : Stmt {
      public string v;
      public Expr e;

      public Assign(string v, Expr e) {
        this.v = v;
        this.e = e;
      }
    }

    public class Prog : AST {
      public List<Stmt> s;

      public Prog(List<Stmt> s) {
        this.s = s;
      }
    }
  }

  // Then we define a visitor to translate ANTLR's output into an AST:
  namespace AntlrVisitor {
    using CSharpAST;

    public class SimpleVisitor : SimpleCompiler.SimpleBaseVisitor<AST> {
      public override AST VisitProg(SimpleParser.ProgContext context) {
        return new Prog(context._s.Select((s, _) => (Stmt)Visit(s)).ToList());
      }

      public override AST VisitPrint(SimpleParser.PrintContext context) {
        return new Print((Expr)Visit(context.e));
      }

      public override AST VisitAssign(SimpleParser.AssignContext context) {
        return new Assign(context.v.Text, (Expr)Visit(context.e));
      }

      public override AST VisitAdd(SimpleParser.AddContext context) {
        return new Op(Op.BinOp.Add, (Expr)Visit(context.l), (Expr)Visit(context.r));
      }

      public override AST VisitSub(SimpleParser.SubContext context) {
        return new Op(Op.BinOp.Sub, (Expr)Visit(context.l), (Expr)Visit(context.r));
      }

      public override AST VisitConst(SimpleParser.ConstContext context) {
        return new Const(int.Parse(context.c.Text));
      }

      public override AST VisitVar(SimpleParser.VarContext context) {
        return new Var(context.v.Text);
      }
    }
  }

  // Then we define any C# methods that Dafny may need:

  namespace CSharpUtils {
    public partial class StringUtils {
      public static Dafny.ISequence<char> StringAsDafnyString(String s) {
        return Dafny.Sequence<char>.FromString(s);
      }
    }

    public partial class ListUtils {
      public static B FoldR<A, B>(Func<A, B, B> f, B b0, List<A> lA) {
        for (int i = lA.Count - 1; i >= 0; i--) {
          b0 = f(lA[i], b0);
        }
        return b0;
      }
    }
  }

  // Finally we define the driver that reads the input file, parses it using
  // ANTLR, compiles it using Dafny, and prints the result to stdout:

  class Program {
    private static CSharpAST.Prog parse(string fname) {
      using (var fstream = new StreamReader(fname)) {
        var lexer = new SimpleLexer(new AntlrInputStream(fstream));
        var parser = new SimpleParser(new CommonTokenStream(lexer));
        var visitor = new AntlrVisitor.SimpleVisitor();
        return (CSharpAST.Prog)visitor.Visit(parser.prog());
      }
    }

    public static void Main(string[] args) {
      Console.Out.NewLine = "\n";

      Console.WriteLine("# Step 1: Parse");
      var ast = parse(args[0]);
      Console.WriteLine($"cAST =\n  {ast}");

      Console.WriteLine("\n# Step 2: Compile (using Dafny)");
      var pp = SimpleCompiler.DafnyCompiler.CompileAndExport(ast);

      Console.WriteLine("\n# Step 3: Print (using C#)");
      pp.ForEach(s => Console.WriteLine($"  {s}"));
    }
  }
}
