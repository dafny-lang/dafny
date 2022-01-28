// RUN: %dafny /compile:0 /spillTargetCode:3 "%s"
// RUN: dotnet run --project %S/SimpleCompiler.csproj -- %S/example_input.calc > "%t"
// RUN: %diff "%s.expect" "%t"

/// A simple compiler pipeline
/// ==========================
///
/// This file implements and verifies the Dafny part of the compiler pipeline
/// documented in README.md.
///
/// Source language
/// ---------------

module DafnyAST {

/// We have two kinds of AST nodes:
///
/// 1. Expressions:
///    Either constants or binary operations

  datatype BinOp =
    | Add
    | Sub

  datatype Expr =
    | Const(n: int)
    | Op(op: BinOp, e1: Expr, e2: Expr)

/// 2. Statements:
///     Either no-ops or print statements (or a sequence of two statements)

  datatype Stmt =
    | Skip
    | Print(e: Expr)
    | Seq(s1: Stmt, s2: Stmt)

/// The semantics of expressions and statements can be defined using recursive interpreters:

  function method interpExpr(e: Expr): int {
    match e {
      case Const(n) => n
      case Op(Add, e1, e2) => interpExpr(e1) + interpExpr(e2)
      case Op(Sub, e1, e2) => interpExpr(e1) - interpExpr(e2)
    }
  }

  function method interpStmt(s: Stmt): seq<int> {
    match s {
      case Skip => []
      case Print(e) => [interpExpr(e)]
      case Seq(s1, s2) => interpStmt(s1) + interpStmt(s2)
    }
  }
}

/// Transforming Dafny ASTs
/// -----------------------
///
/// Before compiling, here is a simple rewriting pass that eliminates unnecessary operations (`0 + x → x`, etc.), along with its (fully automated) proofs.

module Rewriter {
  import opened DafnyAST

  function method simplifyExpr(e: Expr) : Expr
    ensures DafnyAST.interpExpr(simplifyExpr(e)) == DafnyAST.interpExpr(e)
  {
    match e {
      case Const(n) => e
      case Op(op, e1, e2) =>
        match (op, simplifyExpr(e1), simplifyExpr(e2)) {
          case (_, Const(0), Const(0)) => Const(0)
          case (Add, Const(0), e2) => e2
          case (Add, e1, Const(0)) => e1
          case (Sub, e1, Const(0)) => e1
          case (_, e1, e2) => Op(op, e1, e2)
        }
    }
  }

  function method simplifyStmt(s: Stmt) : Stmt
    ensures DafnyAST.interpStmt(simplifyStmt(s)) == DafnyAST.interpStmt(s)
  {
    match s {
      case Skip => Skip
      case Print(e) => Print(simplifyExpr(e))
      case Seq(s1, s2) =>
        match (simplifyStmt(s1), simplifyStmt(s2)) {
          case (s1, Skip) => s1
          case (Skip, s2) => s2
          case (s1, s2) => Seq(s1, s2)
        }
    }
  }
}

/// Target language
/// ---------------
///
/// Our target language targets a very simple stack machine.  The machine reads and executes instructions sequentially and modifies its state by pushing or popping from a data stack and writing to an output channel.
///
/// For convenient, programs are represented using a simple linked-list type:

module LinkedList {
  datatype List<T> =
    | Cons(hd: T, tl: List<T>)
    | Nil

  function method Concat<T>(l1: List<T>, l2: List<T>) : List<T> {
    match l1 {
      case Nil => l2
      case Cons(h, t) => Cons(h, Concat<T>(t, l2))
    }
  }
}

module StackMachine {
  import opened LinkedList

/// The machine has 4 instructions:
///
/// 1. `PushConst(n)` adds `n` to the machine's stack.
/// 2. `PopAdd` removes the top two elements of stack, sums them, and pushes the result.
/// 3. `PopSub` removes the top two elements of stack, subtract the first one from the second one, and pushes the result.
/// 4. `PopPrint` removes the top element of the stack and writes it to the output channel.

  datatype Instr =
    | PushConst(n: int)
    | PopAdd
    | PopSub
    | PopPrint

/// Programs are modeled using a linked list:

  type Prog = List<Instr>

/// And semantics are given using an interpreter whose state combines a stack of values and a list of outputs.

  datatype State = State(stack: List<int>, output: seq<int>)

  function method interpInstr(instr: Instr, st: State) : State {
    match (instr, st.stack) {
      case (PushConst(n), tl) =>
        State(Cons(n, tl), st.output)
      case (PopAdd, Cons(n2, Cons(n1, tl))) =>
        State(Cons(n1 + n2, tl), st.output)
      case (PopSub, Cons(n2, Cons(n1, tl))) =>
        State(Cons(n1 - n2, tl), st.output)
      case (PopPrint, Cons(n, tl)) =>
        State(tl, st.output + [n])
      // Error cases
      case (PopAdd, _) => st
      case (PopSub, _) => st
      case (PopPrint, _) => st
    }
  }

  function method interpProg'(p: Prog, st: State) : State {
    match p {
      case Nil => st
      case Cons(instr, p) => interpInstr(instr, interpProg'(p, st))
    }
  }

  const EmptyState := State(Nil, []);

  function method interpProg(p: Prog) : seq<int> {
    interpProg'(p, EmptyState).output
  }
}

module Compiler {
  import opened LinkedList

  import DafnyAST
  import opened StackMachine

  function method compileExpr(e: DafnyAST.Expr): Prog {
    match e {
      case Const(n) => Cons(PushConst(n), Nil)
      case Op(Add, e1, e2) => Cons(PopAdd, Concat(compileExpr(e2), compileExpr(e1)))
      case Op(Sub, e1, e2) => Cons(PopSub, Concat(compileExpr(e2), compileExpr(e1)))
    }
  }

  function method compileStmt(s: DafnyAST.Stmt): Prog {
    match s {
      case Skip => Nil
      case Print(e) => Cons(PopPrint, compileExpr(e))
      case Seq(s1, s2) => Concat(compileStmt(s2), compileStmt(s1))
    }
  }

  lemma interpProg'_Concat(p1: Prog, p2: Prog, st: State)
    ensures interpProg'(LinkedList.Concat(p1, p2), st) ==
            interpProg'(p1, interpProg'(p2, st))
  {}

  lemma compileExprCorrect'(e: DafnyAST.Expr, st: State)
    ensures interpProg'(compileExpr(e), st) ==
            State(Cons(DafnyAST.interpExpr(e), st.stack), st.output)
  {
    match e {
      case Const(n) =>
      case Op(op, e1, e2) =>
        interpProg'_Concat(compileExpr(e2), compileExpr(e1), st);
      // case Op(Sub, e1, e2) => // Here's the expanded version of the same proof
      //   calc {
      //     interpProg'(compileExpr(e), st);
      //     interpProg'(Cons(PopSub, Concat(compileExpr(e2), compileExpr(e1))), st);
      //     interpInstr(PopSub, interpProg'(Concat(compileExpr(e2), compileExpr(e1)), st));
      //     { interpProg'_Concat(compileExpr(e2), compileExpr(e1), st); }
      //   }
    }
  }

  lemma compileStmtCorrect'(s: DafnyAST.Stmt, st: State)
    ensures interpProg'(compileStmt(s), st) ==
            State(st.stack, st.output + DafnyAST.interpStmt(s))
  {
    match s {
      case Skip =>
      case Print(e) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(DafnyAST.Print(e)), st);
          interpProg'(Cons(PopPrint, compileExpr(e)), st);
          interpInstr(PopPrint, interpProg'(compileExpr(e), st));
          { compileExprCorrect'(e, st); }
          interpInstr(PopPrint, State(Cons(DafnyAST.interpExpr(e), st.stack), st.output));
        }
      case Seq(s1, s2) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(DafnyAST.Seq(s1, s2)), st);
          interpProg'(Concat(compileStmt(s2), compileStmt(s1)), st);
          { interpProg'_Concat(compileStmt(s2), compileStmt(s1), st); }
          interpProg'(compileStmt(s2), interpProg'(compileStmt(s1), st));
        }
    }
  }

  lemma compileStmtCorrect(s: DafnyAST.Stmt)
    ensures interpProg(compileStmt(s)) == DafnyAST.interpStmt(s)
  {
    compileStmtCorrect'(s, EmptyState);
  }
}

/// Connecting C# to Dafny
/// ----------------------
///
/// Our Dafny ASTs are defined in terms of Dafny ``datatype`` values, but the AST produced using ANTLR on the C# side is defined through a class hierarchy (see ``Main.cs``).  To connect the two we need a translation function.  Here we write it in Dafny, which allows us to depend on fewer specifics of the compilation process.
///
/// To write the translator in Dafny we need a Dafny model of the C# class hierarchy.  Below we use traits, annotated with `{:extern}` to specify their C# names and `{:compile false}` to indicate that they should not be compiled: they act as shims that we can write the Dafny code against.  Then, once compiled to C#, our Dafny code can be linked against the real C# class hierarchy.
///
/// The model does not have to be completely faithful: for example we won't capture the fact that Expression and Statement share a base class on the C# side.
///
/// There are a few interesting difficulties: native C# types, nested types, enums:
///
/// 1. The C# side uses native C# types like `List<T>`.
/// 2. C# types are commonly nested, but Dafny doesn't support nesting types.
/// 3. Dafny datatypes don't compile to C# enums, so we cannot use them to model those.

/// Modeling C# types in Dafny
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// Native types
/// ^^^^^^^^^^^^
///
/// In this example the only native C# type that we use is `List<T>`.  We add a model of the no-arguments `List<T>` constructor and of the `Add` method to build new lists.  For iterating over existing lists (passed from C#) the ``Aggregate`` method would be enough, but to make this example more informative we define a custom method `FoldL` instead, which is implemented in ``Main.cs``.

module {:extern "System.Collections.Generic"} {:compile false} System.Collections.Generic {
  class {:extern} {:compile false} List<T> {
    constructor {:extern} ()

    method {:extern} Add(t: T)
      modifies this
  }
}

module {:extern "SimpleCompiler.CSharpUtils"} CSharpUtils {
  import LinkedList
  import opened System.Collections.Generic

  class ListUtils {
    static function method {:extern}
      FoldR<A, B>(f: (A, B) -> B, b0: B, l: List<A>) : B

    static method LinkedListToCList<T>(ll: LinkedList.List<T>) returns (l: List<T>) {
      l := new List<T>();
      var it := ll;
      while it.Cons?
        decreases it
      {
        l.Add(it.hd);
        it := it.tl;
      }
    }
  }
}

/// User-defined types
/// ^^^^^^^^^^^^^^^^^^
///
/// This part follows the structure of the ASTs defined in ``Main.cs``.  Note, however, that:
///
/// 1. ``Op.BinOp`` has been renamed to `Op__BinOp`; this is because Dafny does not support nested types.  We ensure that things line back up when we compile to C# by adding an `extern` name to `Op__BinOp`.
///
/// 2. Fields of the ``Op.Binop`` enum are now `static const` fields of the `Op__BinOp` class.
///
/// 3. The AST types do not line up exactly: C# has ``Prog`` as a separate type of AST node, whereas the Dafny datatype AST `Stmt` has a `Seq` constructor instead.

module {:extern "SimpleCompiler.CSharpAST"} CSharpAST {
  import System

  class {:extern "Op.BinOp"} Op__BinOp {
    static const {:extern} Add: Op__BinOp
    static const {:extern} Sub: Op__BinOp
    function method {:extern} Equals(other: Op__BinOp): bool
  }

  trait {:compile false} {:extern} Expr {}

  trait {:compile false} {:extern} Const extends Expr {
    var n: int
  }

  trait {:compile false} {:extern} Op extends Expr {
    var op: Op__BinOp
    var e1: Expr
    var e2: Expr
  }

  trait {:compile false} {:extern} Stmt {}

  trait {:compile false} {:extern} Print extends Stmt {
    var e: Expr
  }

  trait {:compile false} {:extern} Prog {
    var s: System.Collections.Generic.List<Stmt>
  }
}

/// Translating C# inputs
/// ~~~~~~~~~~~~~~~~~~~~~
///
/// With these definitions in place the translation is straightforward.  The translation functions are marked `{:verify false}` because:
///
/// 1. We cannot statically guarantee that the C# types that get passed in are not cyclic, so they could in fact loop forever; and
/// 2. The C# class hierarchy is not sealed, so we cannot statically guarantee that we cover all cases (for simplicity the functions below just enter an infinite loop when they encounter an unexpected case).

module Translator {
  import CSharpAST
  import DafnyAST
  import CSharpUtils
  import opened LinkedList

  function method {:verify false} translateOp(op: CSharpAST.Op__BinOp)
    : DafnyAST.BinOp
  {
    if op.Equals(CSharpAST.Op__BinOp.Add) then DafnyAST.Add
    else if op.Equals(CSharpAST.Op__BinOp.Sub) then DafnyAST.Sub
    else translateOp(op)
  }

  function method {:verify false} translateExpr(c: CSharpAST.Expr)
    : DafnyAST.Expr
    reads *
  {
    if c is CSharpAST.Const then
      var c := c as CSharpAST.Const;
      DafnyAST.Const(c.n)
    else if c is CSharpAST.Op then
      var c := c as CSharpAST.Op;
      DafnyAST.Op(translateOp(c.op), translateExpr(c.e1), translateExpr(c.e2))
    else
      translateExpr(c)
  }

  function method {:verify false} translateStmt(c: CSharpAST.Stmt)
    : DafnyAST.Stmt
    reads *
  {
    if c is CSharpAST.Print then
      var c := c as CSharpAST.Print;
      DafnyAST.Print(translateExpr(c.e))
    else
      translateStmt(c)
  }

  function method {:verify false} translateProg(c: CSharpAST.Prog)
    : DafnyAST.Stmt
    reads *
  {
    CSharpUtils.ListUtils.FoldR(
      (c, ds) => DafnyAST.Seq(translateStmt(c), ds),
      DafnyAST.Skip,
      c.s
    )
  }
}

/// Pretty-printing Dafny's outputs
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///
/// In general passing complex types between Dafny and C# requires some efforts (e.g. the modeling above), so for the final part of this pipeline (returning the data to C#) we'll use a very simple type: a list of strings (one per instruction).  Conveniently, the `ToString` method of Dafny strings provides a trivial conversion to C# strings, so we leave that conversion to the C# side.
///
/// Alternatively, we could have chosen to expose the stack machine types to C# directly and do the pretty-printing from there.

module PrettyPrint {
  import opened LinkedList
  import opened StackMachine

  function method prettyPrintNum(n: int, zero: string) : string
    decreases n < 0, if n < 0 then -n else n
  {
    if n == 0 then zero
    else if n < 0 then prettyPrintNum(-n, zero)
    else if n < 10 then ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"][n]
    else if n >= 10 then prettyPrintNum(n / 10, "") + prettyPrintNum(n % 10, "0")
    else assert false; prettyPrintNum(n, zero)
  }

  function method prettyPrintInstr(instr: Instr) : string {
    match instr {
      case PushConst(n) => "PushConst(" + prettyPrintNum(n, "0") + ")"
      case PopAdd => "PopAdd"
      case PopSub => "PopSub"
      case Print => "Print"
    }
  }

  function method prettyPrint(p: Prog) : List<string> {
    match p {
      case Nil => Nil
      case Cons(instr, p) => Cons(prettyPrintInstr(instr), prettyPrint(p))
    }
  }
}

/// 5. Exposing Dafny to C#
/// ~~~~~~~~~~~~~~~~~~~~~~~
///
/// Finally, we define a single Dafny function that serves as our interface to C#.  It takes a C# AST, translates it to Dafny, runs rewriting passes, compiles it to a stack machine program, pretty-prints it to a string, and returns it to C#.
///
/// Note that the `Interop` module below has an `extern` annotation but no `{:compile false}` annotation: this is because we want to implement it in Dafny, but give it a predictable name in the generated C# code.

module {:extern "SimpleCompiler"} Interop {
  import LinkedList
  import CSharpAST
  import DafnyAST
  import Rewriter
  import StackMachine
  import Translator
  import Compiler
  import PrettyPrint
  import CSharpUtils
  import Generics = System.Collections.Generic

  class DafnyCompiler {
    static method Compile(dAST: DafnyAST.Stmt) returns (dSM: StackMachine.Prog)
      ensures DafnyAST.interpStmt(dAST) == StackMachine.interpProg(dSM)
    {
      print "translated = \n  "; print dAST; print "\n";
      print "interp(translated) = \n  "; print DafnyAST.interpStmt(dAST); print "\n";
      print "\n";

      var optimized: DafnyAST.Stmt := Rewriter.simplifyStmt(dAST);
      print "optimized = \n  "; print optimized; print "\n";
      print "interp(optimized) = \n  "; print DafnyAST.interpStmt(optimized); print "\n";
      print "\n";

      dSM := Compiler.compileStmt(optimized);
      print "compiled = \n  "; print dSM; print "\n";
      print "interp(compiled) = \n  "; print StackMachine.interpProg(dSM); print "\n";
      print "\n";

      // Proof:
      calc {
        DafnyAST.interpStmt(dAST);
        // No lemma needed here since simplifyStmt has the right postcondition
        DafnyAST.interpStmt(optimized);
        { Compiler.compileStmtCorrect(optimized); }
        StackMachine.interpProg(dSM);
      }
    }

    static method CompileAndExport(cAST: CSharpAST.Prog)
      returns (output: Generics.List<string>)
    {
      var translated: DafnyAST.Stmt := Translator.translateProg(cAST);
      var compiled: StackMachine.Prog := Compile(translated);
      var prettyPrinted: LinkedList.List<string> := PrettyPrint.prettyPrint(compiled);
      output := CSharpUtils.ListUtils.LinkedListToCList(prettyPrinted);
    }
  }
}
