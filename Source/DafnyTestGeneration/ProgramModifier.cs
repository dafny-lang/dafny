#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Token = Microsoft.Dafny.Token;
using Declaration = Microsoft.Boogie.Declaration;
using Formal = Microsoft.Boogie.Formal;
using Function = Microsoft.Boogie.Function;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using LocalVariable = Microsoft.Boogie.LocalVariable;
using Parser = Microsoft.Boogie.Parser;
using Program = Microsoft.Boogie.Program;
using QuantifierExpr = Microsoft.Boogie.QuantifierExpr;
using Type = Microsoft.Boogie.Type;

namespace DafnyTestGeneration {

  /// <summary>
  /// Contains functionality that allows to generate various modifications
  /// of a Boogie program with assertions that fail when a particular
  /// condition is met (such as when a block is visited or a path is taken)
  /// </summary>
  public abstract class ProgramModifier {
    private static readonly string ImplPrefix = "Impl$$";
    private static readonly string CallPrefix = "Call$$";
    private static readonly string CtorPostfix = "__ctor";
    // The implementation to test.
    protected string TargetImplementationVerboseName = null;
    // Boogie names of implementations to be tested or inlined
    private Dictionary<string, uint> timesToInline = new();
    protected DafnyInfo DafnyInfo;

    /// <summary>
    /// Create tests and return the list of bpl test files
    /// </summary>
    public IEnumerable<ProgramModification> GetModifications(
      IEnumerable<Program> programs,
      DafnyInfo dafnyInfo) {
      DafnyInfo = dafnyInfo;
      var options = dafnyInfo.Options;
      var program = MergeBoogiePrograms(options, programs);
      string targetImplementationName = null;
      if (options.TestGenOptions.TargetMethod != null) {
        // cannot use the implementation object directly because it changes
        // after various transformations are applied
        var targetImplementation = program.Implementations.FirstOrDefault(i =>
          i.Name.StartsWith(ImplPrefix)
          && i.VerboseName.Split(" ")[0]
          == options.TestGenOptions.TargetMethod);
        targetImplementationName = targetImplementation?.Name;
        TargetImplementationVerboseName = targetImplementation?.VerboseName;
      }
      var callGraphVisitor = new CallGraph(dafnyInfo, program);
      timesToInline = callGraphVisitor.GetCallees(targetImplementationName);
      program = new FunctionToMethodCallRewriter(this, options).VisitProgram(program);
      program = new AddImplementationsForCalls(options).VisitProgram(program);
      program = new RemoveChecks(options).VisitProgram(program);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      engine.CoalesceBlocks(program); // removes redundant basic blocks
      var annotator = new AnnotationVisitor(this, options);
      program = annotator.VisitProgram(program);
      AddAxioms(options, program);
      if (options.TestGenOptions.PrintBpl != null) {
        File.WriteAllText(options.TestGenOptions.PrintBpl,
          Utils.GetStringRepresentation(options, program));
      }
      if (options.TestGenOptions.PrintCfg != null &&
          options.TestGenOptions.TargetMethod != null) {
        Utils.PrintCfg(options, program);
      }
      return GetModifications(program);
    }

    protected abstract IEnumerable<ProgramModification> GetModifications(Program p);

    protected bool ImplementationIsToBeTested(Implementation impl) =>
      (TargetImplementationVerboseName == null ||
       timesToInline.GetValueOrDefault<string, uint>(impl.Name, 0) > 0) &&
      impl.Name.StartsWith(ImplPrefix) && !impl.Name.EndsWith(CtorPostfix) &&
      !DafnyInfo.IsGhost(impl.VerboseName.Split(" ").First());

    /// <summary>
    /// Add axioms necessary for counterexample generation to work efficiently
    /// </summary>
    private static void AddAxioms(DafnyOptions options, Program program) {
      if (options.TestGenOptions.SeqLengthLimit == 0) {
        return;
      }
      var limit = (uint)options.TestGenOptions.SeqLengthLimit;
      Parser.Parse($"axiom (forall<T> y: Seq T :: " +
                   $"{{ Seq#Length(y) }} Seq#Length(y) <= {limit});",
        "", out var tmpProgram);
      program.AddTopLevelDeclaration(
        (Axiom)tmpProgram.TopLevelDeclarations.ToList()[0]);
    }

    /// <summary>
    /// Merge Boogie Programs by removing any duplicate top level declarations
    /// </summary>
    private static Program MergeBoogiePrograms(DafnyOptions options, IEnumerable<Program> programs) {
      // Merge all programs into one first:
      var program = new Program();
      foreach (var p in programs) {
        program.AddTopLevelDeclarations(p.TopLevelDeclarations);
      }
      // Remove duplicates afterwards:
      var declarations = new Dictionary<string, HashSet<string/*?*/>>();
      var toRemove = new List<Declaration>();
      foreach (var declaration in program.TopLevelDeclarations) {
        var typeName = declaration.GetType().Name;
        if (!declarations.ContainsKey(typeName)) {
          declarations[typeName] = new();
        }
        var declarationAsString = declaration.ToString();
        if (declarationAsString != null &&
            declarations[typeName].Contains(declarationAsString)) {
          toRemove.Add(declaration);
        } else {
          declarations[typeName].Add(declarationAsString);
        }
      }
      toRemove.ForEach(x => program.RemoveTopLevelDeclaration(x));
      return Utils.DeepCloneResolvedProgram(program, options);
    }

    /// <summary>
    /// Create an assume command that prints objects in the
    /// <param name="data">list</param> as part of error trace.
    /// </summary>
    private static AssumeCmd GetAssumePrintCmd(
      List<object> data,
      string separator = " | ") {
      // first insert separators between the things being printed
      var toPrint = new List<object>();
      data.Iter(obj => toPrint.AddRange(new List<object> { obj, separator }));
      if (toPrint.Count() != 0) {
        toPrint.RemoveAt(toPrint.Count() - 1);
      }
      // now create the assume command
      var annotation = new QKeyValue(new Token(), "print", toPrint, null);
      return new AssumeCmd(new Token(),
        new LiteralExpr(new Token(), true), annotation);
    }

    /// <summary>
    /// Create a new local variable with a name that has not been reserved
    /// </summary>
    protected static LocalVariable GetNewLocalVariable(
      Implementation impl,
      Type type,
      string baseName = "tmp") {
      string name = baseName;
      if (impl.LocVars.Exists(v => v.Name == name)) {
        int id = 0;
        while (impl.LocVars.Exists(v => v.Name == baseName + id)) {
          id++;
        }
        name = baseName + id;
      }
      var newLocalVar = new LocalVariable(new Token(),
        new TypedIdent(new Token(), name, type));
      impl.LocVars.Add(newLocalVar);
      return newLocalVar;
    }


    /// <summary>
    /// Create implementations for all "Call$$" procedures by making them
    /// call the respective "Impl$$ implementations. This allows to implement
    /// inlining of Dafny methods further down the road.
    /// </summary>
    private class AddImplementationsForCalls : ReadOnlyVisitor {
      private DafnyOptions options;
      private List<Implementation> implsToAdd = new();
      private Program/*?*/ program;

      public AddImplementationsForCalls(DafnyOptions options) {
        this.options = options;
      }

      public override Procedure/*?*/ VisitProcedure(Procedure/*?*/ node) {
        if (node == null || !node.Name.StartsWith(CallPrefix) ||
            node.Name.EndsWith(CtorPostfix)) {
          return node;
        }

        var callerName = node.Name;
        var calleeName = $"{ImplPrefix}{node.Name.Split("$").Last()}";
        var calleeProc = program?.Procedures
          .Where(f => f.Name == calleeName)
          .FirstOrDefault((Procedure)null);
        if (calleeProc == null) {
          return node; // Can happen if included modules are not verified
        }

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
        var returnVars = outParams.Concat(vars);
        // construct the call to the "Impl$$" implementation:
        var cmd = new CallCmd(new Token(), calleeName,
          inParams
            .ConvertAll(v => (Expr)new IdentifierExpr(new Token(), v))
            .ToList(),
          calleeProc.OutParams
            .ConvertAll(v => new IdentifierExpr(new Token(), returnVars.First(rv => rv.Name == v.Name)))
            .ToList());
        cmd.Proc = calleeProc;
        // create a block for this call:
        var block = new Block(new Token(), "anon_0", new List<Cmd> { cmd },
          new ReturnCmd(new Token()));
        // construct the new implementation:
        var verboseNameAttr = new QKeyValue(new Token(), "verboseName",
          new List<object> { node.VerboseName }, null);
        var callerImpl = new Implementation(new Token(), callerName,
          node.TypeParameters, inParams, outParams, vars,
          new List<Block> { block }, verboseNameAttr);
        callerImpl.Proc = node;
        implsToAdd.Add(callerImpl);
        return node;
      }

      public override Program VisitProgram(Program node) {
        program = node;
        implsToAdd = new();
        node = base.VisitProgram(node);
        node.AddTopLevelDeclarations(implsToAdd);
        return Utils.DeepCloneResolvedProgram(node, options);
      }
    }

    /// <summary>
    /// A call graph object to determine which procedures to inline
    /// </summary>
    private class CallGraph : ReadOnlyVisitor {

      // maps name of an implementation to those implementations that it calls
      private readonly Dictionary<string, HashSet<string>> calls = new();
      private string/*?*/ implementation; // implementation currently traversed
      private readonly DafnyInfo info;
      private readonly Dictionary<string, uint> timesToInline = new();
      private bool insideAssignCommand = false;
      private HashSet<string> procedureNames = new();

      public CallGraph(DafnyInfo info, Program program) {
        this.info = info;
        procedureNames = new();
        program.Procedures.Iter(p => procedureNames.Add(p.Name));
        VisitProgram(program);
      }

      public override Procedure VisitProcedure(Procedure node) {
        var procedure = node.Name;
        if (!calls.ContainsKey(procedure)) {
          calls[procedure] = new();
        }
        if (procedure.StartsWith(CallPrefix)) {
          calls[procedure].Add(ImplPrefix + procedure[CallPrefix.Length..]);
        }
        timesToInline[node.Name] = info.TimesToInline(node.VerboseName.Split(" ").First());
        return node;
      }

      public override Implementation VisitImplementation(Implementation node) {
        implementation = node.Name;
        if (!calls.ContainsKey(implementation)) {
          calls[implementation] = new();
        }
        node.Blocks.ForEach(block => VisitBlock(block));
        return node;
      }

      public override Cmd VisitCallCmd(CallCmd node) {
        if (implementation != null) {
          calls[implementation].Add(node.callee);
        }
        return base.VisitCallCmd(node);
      }

      public override Expr VisitNAryExpr(NAryExpr node) {
        if (!insideAssignCommand) {
          return node;
        }
        var procedure = ImplPrefix + node.Fun.FunctionName;
        if (procedureNames.Contains(procedure)) {
          calls[implementation].Add(procedure);
        }
        return base.VisitNAryExpr(node);
      }

      public override Cmd VisitAssignCmd(AssignCmd node) {
        insideAssignCommand = true;
        var result = base.VisitAssignCmd(node);
        insideAssignCommand = false;
        return result;
      }

      public sealed override Program VisitProgram(Program node) {
        node = base.VisitProgram(node);
        return node;
      }

      /// <summary>
      /// For each callee implementation, return the number of times it has
      /// to be inlined 
      /// </summary>
      public Dictionary<string, uint> GetCallees(string/*?*/ caller) {
        var result = new Dictionary<string, uint>();
        if (caller == null) {
          return result;
        }
        GetCalleesRecursively(caller, result);
        if (result.GetValueOrDefault<string, uint>(caller, 0) == 0) {
          result[caller] = 1; // "inline" the method actually being tested
        }
        return result;
      }

      private void GetCalleesRecursively(string caller, Dictionary<string, uint> recorded) {
        foreach (var callee in calls.GetValueOrDefault(caller,
                   new HashSet<string>())) {
          if (recorded.ContainsKey(callee)) {
            continue;
          }
          uint toInline = timesToInline.GetValueOrDefault<string, uint>(callee, 0);
          if (toInline == 0) {
            continue;
          }
          recorded[callee] = toInline;
          if (info.Options.TestGenOptions.Verbose) {
            Console.Out.WriteLine($"// Will inline calls to {callee} with recursion unrolling depth set to {toInline}.");
          }
          GetCalleesRecursively(callee, recorded);
        }
      }
    }

    /// <summary>
    /// Annotate the AST with "assume true" print statements inserted at:
    /// (1)     the beginning of each implementation, to get the parameter types
    ///         and values leading to assertion or post-condition violation.
    /// (2)     the end of each block, to get execution trace.
    /// </summary>
    private class AnnotationVisitor : StandardVisitor {
      private DafnyOptions options;
      private Implementation/*?*/ implementation;
      private readonly ProgramModifier modifier;

      public AnnotationVisitor(ProgramModifier modifier, DafnyOptions options) {
        this.modifier = modifier;
        this.options = options;
      }

      public override Block VisitBlock(Block node) {
        if (node.cmds.Count == 0) {
          return base.VisitBlock(node); // ignore blocks with zero commands
        }
        var data = new List<object>
          { "Block", implementation.Name, node.UniqueId.ToString() };
        node.cmds.Add(GetAssumePrintCmd(data));
        return node;
      }

      public override Implementation VisitImplementation(Implementation node) {
        implementation = node;
        // print parameter types:
        var data = new List<object> { "Types" };
        data.AddRange(node.InParams.Select(var =>
          var.TypedIdent.Type.ToString()));
        node.Blocks[0].cmds.Insert(0, GetAssumePrintCmd(data));

        // record parameter values:
        data = new List<object> { "Impl", node.VerboseName.Split(" ")[0] };
        data.AddRange(node.InParams.Select(var => new IdentifierExpr(new Token(), var)));

        var toTest = options.TestGenOptions.TargetMethod;
        if (toTest == null) {
          // All methods are tested/modified
          node.Blocks[0].cmds.Insert(0, GetAssumePrintCmd(data));
        } else if (node.VerboseName != null &&
                   node.VerboseName == modifier.TargetImplementationVerboseName) {
          // This method is tested/modified
          node.Blocks[0].cmds.Insert(0, GetAssumePrintCmd(data));
        } else if (modifier.timesToInline.ContainsKey(node.Name)) {
          // This method is inlined (and hence tested)
          var depthExpression =
            new LiteralExpr(new Token(), BigNum.FromUInt(modifier.timesToInline[node.Name]));
          var attribute = new QKeyValue(new Token(), "inline",
            new List<object>() { depthExpression }, null);
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
    /// Replaces a function call with a procedure call, whenever there are two
    /// equivalent representations of the same functionality as a result of
    /// translating a Dafny function-by-method to Boogie
    /// </summary>
    private class FunctionToMethodCallRewriter : StandardVisitor {
      private DafnyOptions options;
      private Implementation/*?*/ currImpl;
      private Program/*?*/ currProgram;
      private Block/*?*/ currBlock;
      private AssignCmd/*?*/ currAssignCmd;

      // This list is populated while traversing a block and then the respective
      // commands are inserted in that block at specified positions
      private List<(Cmd cmd, Cmd before)>/*?*/ commandsToInsert;
      private readonly ProgramModifier modifier;
      private Dictionary<string, Function> functionMap;

      /// <summary>
      /// Attempt to convert a function call expression to a method call
      /// statement, where the two are related via the function-by-method
      /// construct. 
      /// </summary>
      /// <returns>The identifier for the temporary variable that
      /// stores the result of the method call</returns>
      private IdentifierExpr/*?*/ TryConvertFunctionCall(NAryExpr call) {
        Procedure/*?*/ proc = currProgram?.Procedures
          .Where(f => f.Name == ImplPrefix + call.Fun.FunctionName)
          .FirstOrDefault((Procedure)null);
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
          var identifierExpr = new IdentifierExpr(new Token(), newVar);
          outs.Add(identifierExpr);
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

      public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node) {
        return node;
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
        if (!node.Name.StartsWith(ImplPrefix)) {
          return node;
        }
        currImpl = node;
        return base.VisitImplementation(node);
      }

      public override Program VisitProgram(Program node) {
        node = new RemoveFunctionsFromShortCircuitRewriter(modifier, options).VisitProgram(node);
        currProgram = node;
        functionMap = new();
        node.Functions.Iter(i => functionMap[i.Name] = i);
        node.TopLevelDeclarations
          .OfType<Implementation>()
          .Where(i => modifier.ImplementationIsToBeTested(i))
          .Iter(i => VisitImplementation(i));
        return Utils.DeepCloneResolvedProgram(node, options);
      }

      public FunctionToMethodCallRewriter(ProgramModifier modifier, DafnyOptions options) {
        this.modifier = modifier;
        this.options = options;
        functionMap = new();
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
      private DafnyOptions options;
      private AssignCmd/*?*/ currAssignCmd;
      private Implementation/*?*/ currImpl;
      private Program/*?*/ currProgram;
      // maps the string representation of a function call to a local variable
      // that stores the result
      private Dictionary<string, LocalVariable>/*?*/ funcCallToResult;
      // suffix added to all canCall functions:
      private const string CanCallSuffix = "#canCall";
      // new commands to insert in the currently traversed block
      private List<(Cmd cmd, Cmd after)>/*?*/ commandsToInsert;
      private readonly ProgramModifier modifier;
      private Dictionary<string, Function> functionMap;
      private Dictionary<string, Procedure> procedureMap;
      private Dictionary<string, Implementation> implementationMap;

      public RemoveFunctionsFromShortCircuitRewriter(ProgramModifier modifier, DafnyOptions options) {
        this.modifier = modifier;
        this.options = options;
        functionMap = new();
        procedureMap = new();
        implementationMap = new();
      }

      /// <summary>
      /// Replace a function call with a variable identifier that points to
      /// the result of that function call
      /// </summary>
      public override Expr VisitNAryExpr(NAryExpr node) {
        Function/*?*/ findFunction =
          functionMap.GetValueOrDefault(node.Fun.FunctionName + CanCallSuffix, null);
        Procedure/*?*/ findProcedure =
          procedureMap.GetValueOrDefault(ImplPrefix + node.Fun.FunctionName,
            null);
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

      public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node) {
        return node;
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

        Implementation/*?*/ findImplementation =
          implementationMap.GetValueOrDefault(
            ImplPrefix + expr.Fun.FunctionName[..^CanCallSuffix.Length], null);
        if (findImplementation == null) {
          return node;
        }

        Function/*?*/ func = currProgram.Functions
          .Where(f => f.Name == expr.Fun.FunctionName[..^CanCallSuffix.Length])
          .FirstOrDefault((Function)null);
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
        var findFunction = functionMap.GetValueOrDefault(node.Name[6..], null);
        if (!node.Name.StartsWith(ImplPrefix) || findFunction == null) {
          return node; // this implementation is potentially side-effecting
        }
        currImpl = node;
        funcCallToResult = new();
        return base.VisitImplementation(node);
      }

      public override Program VisitProgram(Program node) {
        currProgram = node;
        functionMap = new();
        procedureMap = new();
        implementationMap = new();
        node.Implementations.Iter(i => implementationMap[i.Name] = i);
        node.Functions.Iter(i => functionMap[i.Name] = i);
        node.Procedures.Iter(i => procedureMap[i.Name] = i);
        node.TopLevelDeclarations
          .OfType<Implementation>()
          .Where(i => modifier.ImplementationIsToBeTested(i))
          .Iter(i => VisitImplementation(i));
        node.Resolve(options);
        return node;
      }

    }

    /// <summary>
    /// Replace assertions with assumptions and ensures with free ensures to
    /// alleviate the verification burden. Return a reresolved copy of the AST.
    /// </summary>
    private class RemoveChecks : StandardVisitor {
      private DafnyOptions options;

      public RemoveChecks(DafnyOptions options) {
        this.options = options;
      }

      public override Block VisitBlock(Block node) {
        var toRemove = node.cmds.OfType<AssertCmd>().ToList();
        foreach (var cmd in toRemove) {
          var newCmd = new AssumeCmd(new Token(), cmd.Expr, cmd.Attributes);
          node.cmds.Insert(node.cmds.IndexOf(cmd), newCmd);
          node.cmds.Remove(cmd);
        }
        return node;
      }

      public override Procedure VisitProcedure(Procedure node) {
        List<Ensures> newEnsures = new();
        foreach (var e in node.Ensures) {
          newEnsures.Add(new Ensures(
            new Token(),
            true,
            e.Condition,
            e.Comment,
            e.Attributes));
        }
        node.Ensures = newEnsures;
        return node;
      }

      public override Program VisitProgram(Program node) {
        VisitDeclarationList(node.TopLevelDeclarations.ToList());
        return Utils.DeepCloneResolvedProgram(node, options);
      }
    }
  }
}
