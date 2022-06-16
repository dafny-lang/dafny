using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Declaration = Microsoft.Boogie.Declaration;
using Formal = Microsoft.Boogie.Formal;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LocalVariable = Microsoft.Boogie.LocalVariable;
using Parser = Microsoft.Boogie.Parser;
using Program = Microsoft.Boogie.Program;
using Type = Microsoft.Boogie.Type;

namespace DafnyTestGeneration {

  /// <summary>
  /// Contains functionality that allows to generate various modifications
  /// of a Boogie program with assertions that fail when a particular
  /// condition is met (such as when a block is visited or a path is taken)
  /// </summary>
  public abstract class ProgramModifier : ReadOnlyVisitor {

    // name of the procedure to modify.
    // If null, all procedure will be modified.
    // If not null, other procedures can be inlined.
    protected string? ProcedureName;
    // set of implementations to be modified. This can include inlined impls
    private HashSet<string> toModify = new();

    /// <summary>
    /// Create tests and return the list of bpl test files
    /// </summary>
    public IEnumerable<ProgramModification> GetModifications(IEnumerable<Program> programs) {
      var program = MergeBoogiePrograms(programs);
      program = new FunctionToMethodCallRewriter().VisitProgram(program);
      program = new AddImplementationsForCalls().VisitProgram(program);
      var annotator = new AnnotationVisitor();
      program = annotator.VisitProgram(program);
      ProcedureName = annotator.ProcedureName;
      var callGraphVisitor = new CallGraphVisitor();
      callGraphVisitor.VisitProgram(program);
      toModify = callGraphVisitor.GetCallees(ProcedureName);
      AddAxioms(program);
      return GetModifications(program);
    }

    protected abstract IEnumerable<ProgramModification> GetModifications(Program p);

    protected bool ProcedureIsToBeTested(string procName) =>
      (ProcedureName == null || toModify.Contains(procName)) &&
      procName.StartsWith("Impl$$") && !procName.EndsWith("__ctor");

    /// <summary>
    /// Add axioms necessary for counterexample generation to work efficiently
    /// </summary>
    private static void AddAxioms(Program program) {
      Axiom axiom;
      if (DafnyOptions.O.TestGenOptions.SeqLengthLimit != null) {
        var limit = (uint)DafnyOptions.O.TestGenOptions.SeqLengthLimit;
        axiom = GetAxiom($"axiom (forall<T> y: Seq T :: " +
                         $"{{ Seq#Length(y) }} Seq#Length(y) <= {limit});");
        program.AddTopLevelDeclaration(axiom);
      }
      // Restricting character codes to those valid in Dafny
      axiom = GetAxiom("axiom (forall c: char :: { char#ToInt(c) } " +
                       "(char#ToInt(c) >= 33) && (char#ToInt(c) <= 126));");
      program.AddTopLevelDeclaration(axiom);
    }

    /// <summary>
    /// Merge Boogie Programs by removing any duplicate top level declarations
    /// (these typically come from DafnyPrelude.bpl)
    /// </summary>
    private static Program MergeBoogiePrograms(IEnumerable<Program> programs) {
      // Merge all programs into one first:
      var program = new Program();
      foreach (var p in programs) {
        program.AddTopLevelDeclarations(p.TopLevelDeclarations);
      }
      // Remove duplicates afterwards:
      var declarations = new Dictionary<string, HashSet<string?>>();
      var toRemove = new List<Declaration>();
      foreach (var declaration in program.TopLevelDeclarations) {
        var typeName = declaration.GetType().Name;
        if (typeName.Equals("Axiom")) {
          continue;
        }
        if (!declarations.ContainsKey(typeName)) {
          declarations[typeName] = new();
        }
        if (declarations[typeName].Contains(declaration.ToString())) {
          toRemove.Add(declaration);
        } else {
          declarations[typeName].Add(declaration.ToString());
        }
      }
      toRemove.ForEach(x => program.RemoveTopLevelDeclaration(x));
      program.Resolve(DafnyOptions.O);
      return program;
    }

    /// <summary>
    /// Get a parsed boogie command
    /// </summary>
    /// <param name="source">the body of the procedure with the command</param>
    /// <param name="args">the arguments to this procedure</param>
    /// <param name="returns">the return values of this procedure</param>
    /// <returns></returns>
    protected static Cmd GetCmd(string source, string args = "",
      string returns = "") {
      Parser.Parse($"procedure a({args}) returns ({returns}) {{ {source} }}",
        "", out var program);
      return program.Implementations.ToList()[0].Blocks[0].cmds[0];
    }

    private static AssumeCmd GetAssumeCmd(List<string> toPrint) {
      return (AssumeCmd)GetCmd($"assume {{:print " +
                                $"{string.Join(", \" | \", ", toPrint)}}} true;");
    }

    private static QKeyValue GetQKeyValue(string source) {
      Parser.Parse($"procedure {{{source}}} a() {{}}", "", out var program);
      return program.Implementations.ToList()[0].Attributes;
    }

    private static Axiom GetAxiom(string source) {
      Parser.Parse(source, "", out var program);
      return (Axiom)program.TopLevelDeclarations.ToList()[0];
    }

    /// <summary>
    /// Add a new local variable to the implementation currently processed
    /// </summary>
    private static LocalVariable GetNewLocalVariable(Implementation impl, Type type) {
      const string baseName = "tmp#";
      int id = 0;
      while (impl.LocVars.Exists(v => v.Name == baseName + id)) {
        id++;
      }
      var newLocalVar = new LocalVariable(new Token(),
        new TypedIdent(new Token(), baseName + id, type));
      impl.LocVars.Add(newLocalVar);
      return newLocalVar;
    }


    /// <summary>
    /// Create implementations for all "Call$$" procedures by making them
    /// call the respective "Impl$$ implementations. This allows to implement
    /// inlining of Dafny methods further down the road.
    /// </summary>
    private class AddImplementationsForCalls : ReadOnlyVisitor {

      private List<Implementation> implsToAdd = new();
      private Program? program;

      public override Procedure? VisitProcedure(Procedure? node) {
        if (node == null || !node.Name.StartsWith("Call$$")) {
          return node;
        }

        var callerName = node.Name;
        var calleName = $"Impl$${node.Name.Split("$").Last()}";
        var calleeProc = program?.FindProcedure(calleName);
        if (calleeProc == null) {
          return node; // Can happen if included modules are not verified
        }

        // consruct the call to the "Impl$$" implementation:
        Cmd cmd = new CallCmd(new Token(), calleName,
          node.InParams
            .ConvertAll(v => (Expr)new IdentifierExpr(new Token(), v))
            .ToList(),
          calleeProc.OutParams
            .ConvertAll(v => new IdentifierExpr(new Token(), v))
            .ToList());
        // create a block for this call:
        var block = new Block(new Token(), "anon_0", new List<Cmd> { cmd },
          new ReturnCmd(new Token()));
        // define local variables to hold unused return values:
        var vars = calleeProc.OutParams
          .Where(p1 => !node.OutParams
            .Exists(p2 => p2.Name == p1.Name)).ToList()
          .ConvertAll(p1 =>
            (Variable)new LocalVariable(new Token(), p1.TypedIdent)).ToList();
        // you cannot directly reuse node.InParams and node.OutParams
        // because they might contain where clauses which have to be removed
        var inParams = node.InParams.ConvertAll(v =>
          (Variable)new Formal(new Token(),
            new TypedIdent(new Token(), v.Name, v.TypedIdent.Type), true)).ToList();
        var outParams = node.OutParams.ConvertAll(v =>
          (Variable)new Formal(new Token(),
            new TypedIdent(new Token(), v.Name, v.TypedIdent.Type), false)).ToList();
        // construct the new implementation:
        var callerImpl = new Implementation(new Token(), callerName,
          node.TypeParameters, inParams, outParams, vars,
          new List<Block> { block });
        implsToAdd.Add(callerImpl);
        return node;
      }

      public override Program VisitProgram(Program node) {
        program = node;
        implsToAdd = new();
        node = base.VisitProgram(node);
        node.AddTopLevelDeclarations(implsToAdd);
        node.Resolve(DafnyOptions.O);
        return node;
      }
    }

    /// <summary>
    /// Construct the call graph to the indicate the set of all methods that
    /// might have to be inlined into the procedure of interest
    /// </summary>
    private class CallGraphVisitor : ReadOnlyVisitor {

      // maps name of an implementation to those implementations that it calls
      private readonly Dictionary<string, List<string>> calls = new();
      private string? impl;

      public override Implementation VisitImplementation(Implementation node) {
        impl = node.Name;
        calls[impl] = new List<string>();
        node.Blocks.ForEach(block => VisitBlock(block));
        return node;
      }

      public override Cmd VisitCallCmd(CallCmd node) {
        if (impl != null) {
          calls[impl].Add(node.callee);
        }
        return base.VisitCallCmd(node);
      }

      /// <summary>
      /// Return the set of implementations that might be called as a result
      /// of calling the given implementation
      /// </summary>
      public HashSet<string> GetCallees(string? caller) {
        var result = new HashSet<string>();
        if (caller == null) {
          return result;
        }
        GetCalleesRecursively(caller, result);
        return result;
      }

      private void GetCalleesRecursively(string caller, ISet<string> recorded) {
        recorded.Add(caller);
        foreach (var callee in calls.GetValueOrDefault(caller,
          new List<string>())) {
          if (!recorded.Contains(callee)) {
            GetCalleesRecursively(callee, recorded);
          }
        }
      }

      public override Program VisitProgram(Program node) {
        node = base.VisitProgram(node);
        node.Resolve(DafnyOptions.O);
        return node;
      }
    }

    /// <summary>
    /// Annotate the AST with assume true statements inserted at:
    /// (1)     the beginning of each implementation, to get the parameter types
    ///         and values leading to assertion or post-condition violation.
    /// (2)     the end of each block, to get execution trace.
    /// </summary>
    private class AnnotationVisitor : StandardVisitor {

      private string? implName;
      public string? ProcedureName;

      public override Block VisitBlock(Block node) {
        if (node.cmds.Count == 0) {
          return base.VisitBlock(node); // ignore blocks with zero commands
        }
        var data = new List<string>
          {"\"Block\"", $"\"{implName}\"", $"\"{node.UniqueId}\""};
        node.cmds.Add(GetAssumeCmd(data));
        return base.VisitBlock(node);
      }

      public override Implementation VisitImplementation(Implementation node) {

        implName = node.Name;
        // print parameter types:
        var types = new List<string> { "\"Types\"" };
        types.AddRange(node.InParams.Select(var =>
          $"\"{var.TypedIdent.Type}\""));
        node.Blocks[0].cmds.Insert(0, GetAssumeCmd(types));

        // record parameter values:
        var values = new List<string> { "\"Impl\"", $"\"{implName}\"" };
        values.AddRange(node.InParams.Select(var => var.Name));

        var toTest = DafnyOptions.O.TestGenOptions.TargetMethod;
        var depth = DafnyOptions.O.TestGenOptions.TestInlineDepth;
        if (toTest == null) {
          // All methods are tested/modified
          node.Blocks[0].cmds.Insert(0, GetAssumeCmd(values));
        } else if (implName.StartsWith("Impl$$")
                   && Utils.GetDafnyMethodName(implName).Equals(toTest)) {
          // This method is tested/modified
          node.Blocks[0].cmds.Insert(0, GetAssumeCmd(values));
          ProcedureName = implName;
        } else if (depth != 0) {
          // This method is inlined
          var attribute = GetQKeyValue($":inline {depth}");
          attribute.Next = node.Attributes;
          node.Attributes = attribute;
        }
        VisitBlockList(node.Blocks);
        return node;
      }

      public override Program VisitProgram(Program node) {
        node = base.VisitProgram(node);
        node.Resolve(DafnyOptions.O);
        return node;
      }
    }

    /// <summary>
    /// Replaces all function calls with method calls, whenever possible
    /// </summary>
    private class FunctionToMethodCallRewriter : StandardVisitor {

      private Implementation? currImpl;
      private Program? currProgram;
      private Block? currBlock;
      private AssignCmd? currAssignCmd;

      // This list is populated while traversing a block and then the respective
      // commands are inserted in that block at specified positions
      private List<(Cmd cmd, Cmd before)>? commandsToInsert;

      /// <summary>
      /// Attempt to convert a function call expression to a method call
      /// statement, where the two are related via the function-by-method
      /// construct. 
      /// </summary>
      /// <returns>The identifier for the temporary variable that
      /// stores the result of the method call</returns>
      private IdentifierExpr? TryConvertFunctionCall(NAryExpr call) {
        var proc = currProgram?.FindProcedure("Impl$$" + call.Fun.FunctionName);
        if (proc == null) {
          return null; // this function is not a function-by-method
        }
        // The corresponding method may have more than one return parameter.
        // To find out the name of the return parameter that is associated
        // with the function's return value, search for a postcondition that 
        // equates the two:
        var returnName = proc.Ensures
          .Select(e => e.Condition)
          .OfType<NAryExpr>()
          .Where(c =>
            (c.Fun as BinaryOperator)?.Op is
            BinaryOperator.Opcode.Eq or
            BinaryOperator.Opcode.Iff)
          .Where(c => (c.Args[0] is IdentifierExpr) &&
                      ((c.Args[1] as NAryExpr)!.Fun!.FunctionName ==
                       call.Fun.FunctionName))
          .Select(c => (c.Args[0] as IdentifierExpr)?.Name)
          .Where(n => proc.OutParams.Exists(p => p.Name == n)).ToList();
        if (returnName.Count != 1) {
          return null;
        }
        var returnPosition = proc.OutParams
          .FindIndex(i => i.Name == returnName.First());

        // Create temporary local variables to store all the return values:
        var outs = new List<IdentifierExpr>();
        foreach (var param in proc.OutParams) {
          var newVar = GetNewLocalVariable(currImpl!, param.TypedIdent.Type);
          outs.Add(new IdentifierExpr(new Token(), newVar.Name));
        }

        // Create a call command:
        var newCmd = new CallCmd(
          new Token(),
          proc.Name,
          call.Args.ToList(),
          outs);
        // The call will precede the assignment command being processed
        commandsToInsert?.Insert(0, (newCmd, currAssignCmd)!);
        return outs[returnPosition];
      }

      public override Expr VisitNAryExpr(NAryExpr node) {
        if (currAssignCmd == null) {
          return base.VisitNAryExpr(node);
        }
        var args = node.Args.ToList();
        // iterating in the reverse order because
        // the call commands are added in the LIFO order
        for (int i = args.Count - 1; i >= 0; i--) {
          var arg = args[i];
          if ((arg != null) && (arg is NAryExpr funcCall)) {
            var id = TryConvertFunctionCall(funcCall);
            if (id != null) {
              int index = node.Args.IndexOf(arg);
              node.Args.RemoveAt(index);
              node.Args.Insert(index, id);
            }
          }
        }
        return base.VisitNAryExpr(node);
      }

      public override Cmd VisitAssignCmd(AssignCmd node) {
        currAssignCmd = node;
        var newRhss = new List<Expr>();
        // iterating in the reverse order because
        // the call commands are added in the LIFO order
        for (int index = node.Rhss.Count - 1; index >= 0; index--) {
          var rhs = node.Rhss[index];
          if (rhs is NAryExpr funcCall) {
            var id = TryConvertFunctionCall(funcCall);
            if (id != null) {
              newRhss.Insert(0, id);
              continue;
            }
          }
          newRhss.Insert(0, rhs);
        }
        node.Rhss = newRhss;
        node = (AssignCmd)base.VisitAssignCmd(node);
        currAssignCmd = null;
        return node;
      }

      public override Block VisitBlock(Block node) {
        currBlock = node;
        commandsToInsert = new();
        node = base.VisitBlock(node); // this populates commandsToInsert list
        foreach (var toInsert in commandsToInsert) {
          int index = currBlock.cmds.IndexOf(toInsert.before);
          node.cmds.Insert(index, toInsert.cmd);
        }
        return node;
      }

      public override Implementation VisitImplementation(Implementation node) {
        if (!node.Name.StartsWith("Impl$$") ||
            currProgram?.FindFunction(node.Name[6..]) == null) {
          return node; // this implementation is potentially side-effecting
        }
        currImpl = node;
        return base.VisitImplementation(node);
      }

      public override Program VisitProgram(Program node) {
        node = new RemoveFunctionsFromShortCircuitRewriter().VisitProgram(node);
        currProgram = node;
        VisitDeclarationList(node.TopLevelDeclarations.ToList<Declaration>());
        node.Resolve(DafnyOptions.O);
        return node;
      }

    }

    /// <summary>
    /// Remove function calls from short-circuiting expressions so that
    /// function appear in assign commands only when the preconditions are met.
    /// This operation is only performed on non-side effecting implementations
    /// </summary>
    private class RemoveFunctionsFromShortCircuitRewriter : StandardVisitor {

      private AssignCmd? currAssignCmd;
      private Implementation? currImpl;
      private Program? currProgram;
      // maps the string representation of a function call to a local variable
      // that stores the result
      private Dictionary<string, LocalVariable>? funcCallToResult;
      // suffix added to all canCall functions:
      private const string CanCallSuffix = "#canCall";
      // new commands to insert in the currently traversed block
      private List<(Cmd cmd, Cmd after)>? commandsToInsert;

      /// <summary>
      /// Replace a function call with a variable identifier that points to
      /// the result of that function call
      /// </summary>
      public override Expr VisitNAryExpr(NAryExpr node) {
        if (currAssignCmd == null ||
            currProgram?.FindFunction(
              node.Fun.FunctionName + CanCallSuffix) == null) {
          return base.VisitNAryExpr(node);
        }
        var functionCallToString = node.ToString();
        if (!funcCallToResult!.ContainsKey(functionCallToString)) {
          funcCallToResult.Add(functionCallToString,
            GetNewLocalVariable(currImpl!, node.Type));
        }

        return new IdentifierExpr(new Token(),
          funcCallToResult[functionCallToString]);
      }

      public override Cmd VisitAssignCmd(AssignCmd node) {
        currAssignCmd = node;
        node = (AssignCmd)base.VisitAssignCmd(node);
        currAssignCmd = null;
        return node;
      }

      /// <summary>
      /// Whenever an assume statement states that a certain function can be
      /// called with certain parameters without violating any preconditions,
      /// call this function and store the result.
      /// </summary>
      public override Cmd VisitAssumeCmd(AssumeCmd node) {
        if ((node.Expr is not NAryExpr expr) ||
            (!expr.Fun.FunctionName.EndsWith(CanCallSuffix))) {
          return node;
        }

        var func = currProgram?.FindFunction(expr.Fun.FunctionName[..^8]);
        if (func == null) {
          return node;
        }

        // funcCallToResult[funcCallToString] stores the variables that the
        // result of the function call will be assigned to:
        var returnType = func.OutParams.First().TypedIdent.Type;
        var funcCall = new NAryExpr(new Token(),
          new FunctionCall(func), expr.Args);
        var funcCallToString = funcCall.ToString();
        if (!funcCallToResult!.ContainsKey(funcCallToString)) {
          funcCallToResult.Add(funcCallToString,
            GetNewLocalVariable(currImpl!, returnType));
        }

        // the command will be added to the block at VisitBlock call
        var toBeAssigned = new SimpleAssignLhs(new Token(),
          new IdentifierExpr(new Token(), funcCallToResult[funcCallToString]));
        commandsToInsert?.Add((new AssignCmd(new Token(),
          new List<AssignLhs> { toBeAssigned },
          new List<Expr> { funcCall }), node));
        return node;
      }

      public override Block VisitBlock(Block node) {
        commandsToInsert = new();
        node = base.VisitBlock(node); // this populates commandsToInsert list
        foreach (var toInsert in commandsToInsert) {
          int index = node.cmds.IndexOf(toInsert.after);
          node.cmds.Insert(index + 1, toInsert.cmd);
        }
        return node;
      }

      public override Implementation VisitImplementation(Implementation node) {
        if (!node.Name.StartsWith("Impl$$") ||
            currProgram?.FindFunction(node.Name[6..]) == null) {
          return node; // this implementation is potentially side-effecting
        }
        currImpl = node;
        funcCallToResult = new();
        return base.VisitImplementation(node);
      }

      public override Program VisitProgram(Program node) {
        currProgram = node;
        VisitDeclarationList(node.TopLevelDeclarations.ToList<Declaration>());
        node.Resolve(DafnyOptions.O);
        return node;
      }

    }
  }
}
