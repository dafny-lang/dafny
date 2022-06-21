using System.Collections.Generic;
using System.IO;
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

    // The implementation to test.
    // If null, all implementations will be tested.
    // If not null, other implementations can be inlined.
    protected Implementation? ImplementationToTarget;
    // Boogie names of implementations to be tested or inlined
    private HashSet<string> toModify = new();
    private DafnyInfo dafnyInfo;

    /// <summary>
    /// Create tests and return the list of bpl test files
    /// </summary>
    public IEnumerable<ProgramModification> GetModifications(IEnumerable<Program> programs, DafnyInfo dafnyInfo) {
      this.dafnyInfo = dafnyInfo;
      var program = MergeBoogiePrograms(programs);
      program = new FunctionToMethodCallRewriter(this).VisitProgram(program);
      program = new AddImplementationsForCalls().VisitProgram(program);
      program = new RemoveChecks().VisitProgram(program);
      var annotator = new AnnotationVisitor();
      program = annotator.VisitProgram(program);
      ImplementationToTarget = annotator.ImplementationToTarget;
      var callGraphVisitor = new CallGraphVisitor();
      callGraphVisitor.VisitProgram(program);
      toModify = callGraphVisitor.GetCallees(ImplementationToTarget?.Name);
      AddAxioms(program);
      if (DafnyOptions.O.TestGenOptions.PrintBpl != null) {
        File.WriteAllText(DafnyOptions.O.TestGenOptions.PrintBpl, 
          GetStringRepresentation(program));
      }
      return GetModifications(program);
    }

    private static string GetStringRepresentation(Program program) {
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      var oldPrintFile = DafnyOptions.O.PrintFile;
      DafnyOptions.O.PrintInstrumented = true;
      DafnyOptions.O.PrintFile = "-";
      var output = new StringWriter();
      program.Emit(new TokenTextWriter(output, DafnyOptions.O));
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;
      DafnyOptions.O.PrintFile = oldPrintFile;
      return output.ToString();
    }

    protected abstract IEnumerable<ProgramModification> GetModifications(Program p);

    protected bool ImplementationIsToBeTested(Implementation impl) =>
      (ImplementationToTarget == null || toModify.Contains(impl.Name)) &&
      impl.Name.StartsWith("Impl$$") && !impl.Name.EndsWith("__ctor") && 
      !dafnyInfo.IsGhost(impl.VerboseName.Split(" ").First());

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
      program = Utils.DeepCloneProgram(program);
      program.Resolve(DafnyOptions.O);
      program.Typecheck(DafnyOptions.O);
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
        if (node == null || !node.Name.StartsWith("Call$$") ||
            node.Name.EndsWith("__ctor")) {
          return node;
        }

        var callerName = node.Name;
        var calleName = $"Impl$${node.Name.Split("$").Last()}";
        Procedure? calleeProc = program?.Procedures
          .Where(f => f.Name == calleName)
          .FirstOrDefault((Procedure) null);
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
        node = Utils.DeepCloneProgram(node);
        node.Resolve(DafnyOptions.O);
        node.Typecheck(DafnyOptions.O);
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
      public Implementation? ImplementationToTarget;

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
        var values = new List<string> { "\"Impl\"", $"\"{node.VerboseName.Split(" ")[0]}\"" };
        values.AddRange(node.InParams.Select(var => var.Name));

        var toTest = DafnyOptions.O.TestGenOptions.TargetMethod;
        var depth = DafnyOptions.O.TestGenOptions.TestInlineDepth;
        if (toTest == null) {
          // All methods are tested/modified
          node.Blocks[0].cmds.Insert(0, GetAssumeCmd(values));
        } else if (implName.StartsWith("Impl$$")
                   && node.VerboseName.StartsWith(toTest)) {
          // This method is tested/modified
          node.Blocks[0].cmds.Insert(0, GetAssumeCmd(values));
          ImplementationToTarget = node;
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
      private readonly ProgramModifier modifier;

      /// <summary>
      /// Attempt to convert a function call expression to a method call
      /// statement, where the two are related via the function-by-method
      /// construct. 
      /// </summary>
      /// <returns>The identifier for the temporary variable that
      /// stores the result of the method call</returns>
      private IdentifierExpr? TryConvertFunctionCall(NAryExpr call) {
        Procedure? proc = currProgram?.Procedures
          .Where(f => f.Name == "Impl$$" + call.Fun.FunctionName)
          .FirstOrDefault((Procedure) null);
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
          .Where(c => (c.Args.Count == 2) &&
                      (c.Args[0] is IdentifierExpr) &&
                      ((c.Args[1] as NAryExpr)?.Fun?.FunctionName ==
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
          call.Args.Where(e => (e.Type as CtorType)?.Decl?.Name is not "LayerType" &&
                               (e.Type as TypeSynonymAnnotation)?.Decl?.Name is not "Heap").ToList(),
          outs);
        // The call will precede the assignment command being processed
        commandsToInsert?.Insert(0, (newCmd, currAssignCmd)!);
        return outs[returnPosition];
      }

      public override Expr VisitNAryExpr(NAryExpr node) {
        var newNode = base.VisitNAryExpr(node);
        if ((currAssignCmd == null) || newNode is not NAryExpr funcCall) {
          return newNode;
        }
        var identifierExpr = TryConvertFunctionCall(funcCall);
        return identifierExpr ?? newNode;
      }

      public override Cmd VisitAssignCmd(AssignCmd node) {
        currAssignCmd = node;
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
        if (!modifier.ImplementationIsToBeTested(node)) {
          return node;
        }
        Microsoft.Boogie.Function? findFunction = currProgram.Functions
          .Where(f => f.Name == node.Name[6..])
          .FirstOrDefault((Microsoft.Boogie.Function) null);
        if (!node.Name.StartsWith("Impl$$") ||
            findFunction == null) {
          return node; // this implementation is potentially side-effecting
        }
        currImpl = node;
        return base.VisitImplementation(node);
      }

      public override Program VisitProgram(Program node) {
        node = new RemoveFunctionsFromShortCircuitRewriter(modifier).VisitProgram(node);
        currProgram = node;
        node.Implementations.Iter(i => VisitImplementation(i));
        node = Utils.DeepCloneProgram(node);
        node.Resolve(DafnyOptions.O);
        node.Typecheck(DafnyOptions.O);
        return node;
      }

      public FunctionToMethodCallRewriter(ProgramModifier modifier) {
        this.modifier = modifier;
      }

    }

    /// <summary>
    /// Remove function calls from short-circuiting expressions so that
    /// function appear in assign commands only when the preconditions are met.
    /// This operation is only performed on non-side effecting implementations.
    /// IMPORTANT: This should only be used in conjunction with
    /// FunctionToMethodCallRewriter because there are corner cases in which
    /// this pass will otherwise introduce a program that does not typecheck
    /// (due to LayerType). 
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
      private readonly ProgramModifier modifier;

      /// <summary>
      /// Replace a function call with a variable identifier that points to
      /// the result of that function call
      /// </summary>
      public override Expr VisitNAryExpr(NAryExpr node) {
        Microsoft.Boogie.Function? findFunction = currProgram.Functions
          .Where(f => f.Name == node.Fun.FunctionName + CanCallSuffix)
          .FirstOrDefault((Microsoft.Boogie.Function) null);
        Procedure? findProcedure = currProgram.Procedures
          .Where(f => f.Name == "Impl$$" + node.Fun.FunctionName)
          .FirstOrDefault((Procedure) null);
        if (currAssignCmd == null || 
            findFunction == null || 
            findProcedure == null) {
          return base.VisitNAryExpr(node);
        }

        // LayerType arguments should be removed in preparation of this 
        // function call being replaced with a method call
        var funcCall = new NAryExpr(new Token(), node.Fun,
          node.Args.Where(e => (e.Type as CtorType)?.Decl?.Name != "LayerType").ToList());
        var functionCallToString = funcCall.ToString();
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
        if (node.Expr is not NAryExpr expr || (!expr.Fun.FunctionName.EndsWith(CanCallSuffix))) {
          return node;
        }
        Implementation? findImplementation = currProgram?.Implementations
          .Where(f => f.Name == "Impl$$" + expr.Fun.FunctionName[..^CanCallSuffix.Length])
          .FirstOrDefault((Implementation) null);
        if (findImplementation == null) {
          return node;
        }

        Microsoft.Boogie.Function? func = currProgram.Functions
          .Where(f => f.Name == expr.Fun.FunctionName[..^CanCallSuffix.Length])
          .FirstOrDefault((Microsoft.Boogie.Function) null);
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
        var cmd = new AssignCmd(new Token(),
          new List<AssignLhs> { toBeAssigned },
          new List<Expr> { funcCall });
        currAssignCmd = cmd;
        funcCall.Args.Iter(e => VisitExpr(e));
        currAssignCmd = null;
        commandsToInsert?.Add((cmd, node));
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
        if (!modifier.ImplementationIsToBeTested(node)) {
          return node;
        }
        var findFunction = currProgram.Functions
          .Where(f => f.Name == node.Name[6..])
          .FirstOrDefault((Microsoft.Boogie.Function) null);
        if (!node.Name.StartsWith("Impl$$") || findFunction == null) {
          return node; // this implementation is potentially side-effecting
        }
        currImpl = node;
        funcCallToResult = new();
        return base.VisitImplementation(node);
      }

      public override Program VisitProgram(Program node) {
        currProgram = node;
        node.Implementations.Iter(i => VisitImplementation(i));
        node.Resolve(DafnyOptions.O);
        return node;
      }

      public RemoveFunctionsFromShortCircuitRewriter(ProgramModifier modifier) {
        this.modifier = modifier;
      }

    }
    
    private class RemoveChecks : StandardVisitor {

      public override Block VisitBlock(Block node) {
        var toRemove = node.cmds.OfType<AssertCmd>().ToList();
        foreach (var cmd in toRemove) {
          var newCmd = new AssumeCmd(new Token(), cmd.Expr, cmd.Attributes);
          node.cmds.Insert(node.cmds.IndexOf(cmd), newCmd);
          node.cmds.Remove(cmd);
        }
        return base.VisitBlock(node);
      }

      public override Procedure VisitProcedure(Procedure node) {
        List<Ensures> newEnsures = new();
        List<Requires> newRequires = new();
        foreach (var e in node.Ensures) {
          newEnsures.Add(new Ensures(new Token(), true, e.Condition, e.Comment, e.Attributes));
        }
        foreach (var r in node.Requires) {
          newRequires.Add(new Requires(new Token(), true, r.Condition, r.Comment, r.Attributes));
        }
        node.Ensures = newEnsures;
        node.Requires = newRequires;
        return base.VisitProcedure(node);
      }
      
      public override Program VisitProgram(Program node) {
        VisitDeclarationList(node.TopLevelDeclarations.ToList<Declaration>());
        node = Utils.DeepCloneProgram(node);
        node.Resolve(DafnyOptions.O);
        node.Typecheck(DafnyOptions.O);
        return node;
      }
    }
  }
}
