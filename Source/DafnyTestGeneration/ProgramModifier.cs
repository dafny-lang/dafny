#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Token = Microsoft.Dafny.Token;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
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
  public abstract class ProgramModifier {
    internal static readonly string ImplPrefix = "Impl$$";
    internal static readonly string WellFormedPrefix = "CheckWellformed$$";
    internal static readonly string CallPrefix = "Call$$";
    internal static readonly string CtorPostfix = "__ctor";
    internal static readonly string ResultVar = "#result#0";
    // The implementation to test.
    protected string TargetImplementationVerboseName = null;
    // Boogie names of implementations to be tested or inlined
    private Dictionary<string, uint> timesToInline = new();
    protected DafnyInfo DafnyInfo;

    /// <summary>
    /// Create tests and return the list of bpl test files
    /// </summary>
    public IEnumerable<ProgramModification> GetModifications(
      Program program,
      DafnyInfo dafnyInfo) {
      DafnyInfo = dafnyInfo;
      var options = dafnyInfo.Options;
      program = new RemoveChecks(options).VisitProgram(program);
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
    /// A call graph object to determine which procedures to inline
    /// </summary>
    private class CallGraph : ReadOnlyVisitor {

      // maps name of an implementation to those implementations that it calls
      private readonly Dictionary<string, Dictionary<string, int>> calls = new();
      private readonly Dictionary<string, string> toVerbose = new();
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

      public override Implementation VisitImplementation(Implementation node) {
        implementation = node.Name;
        toVerbose[implementation] = node.VerboseName;
        if (implementation.StartsWith(WellFormedPrefix)) {
          implementation = null;
          return node;
        }
        timesToInline[implementation] = info.TimesToInline(node.VerboseName.Split(" ").First());
        if (!calls.ContainsKey(implementation)) {
          calls[implementation] = new();
        }
        node.Blocks.ForEach(block => VisitBlock(block));
        implementation = null;
        return node;
      }

      public override Cmd VisitCallCmd(CallCmd node) {
        if (implementation != null) {
          if (!calls[implementation].ContainsKey(node.callee)) {
            calls[implementation][node.callee] = 0;
          }
          calls[implementation][node.callee] += 1;
        }
        return node;
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
        // PrintCallGraph(caller);
        GetCalleesRecursively(caller, result);
        if (result.GetValueOrDefault<string, uint>(caller, 0) == 0) {
          result[caller] = 1; // "inline" the method actually being tested
        }
        return result;
      }
      
      private void GetCalleesRecursively(string caller, Dictionary<string, uint> recorded) {
        foreach (var callee in calls.GetValueOrDefault(caller,
                   new Dictionary<string, int>()).Keys) {
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

      /*private void PrintCallGraph(string caller) {
        if (caller == null) {
          return;
        }
        string FILENAME = "simple.dot";
        HashSet<string> nodes = new HashSet<string>();
        var edges = new List<(string, string, int)>();
        List<string> toVisit = new List<string>() { caller };
        while (toVisit.Count > 0) {
          string next = toVisit.First();
          toVisit.RemoveAt(0);
          if (nodes.Contains(next)) {
            continue;
          }
          nodes.Add(next);
          foreach (var callee in calls.GetValueOrDefault(next, new Dictionary<string, int>())) {
            edges.Add(new(next, callee.Key, callee.Value));
            toVisit.Add(callee.Key);
          }
        }

        var pathsToNode = new Dictionary<string, int>();
        var nodeToProcess = nodes.FirstOrDefault(
          node => edges.Where(edge => edge.Item2 == node).All(edge => pathsToNode.ContainsKey(edge.Item1)), null);
        while (nodeToProcess != null) {
          if (edges.All(edge => edge.Item2 != nodeToProcess)) {
            pathsToNode[nodeToProcess] = 1;
          } else {
            pathsToNode[nodeToProcess] = edges.Where(edge => edge.Item2 == nodeToProcess)
              .Select(edge => edge.Item3 * pathsToNode[edge.Item1]).Sum();
          }
          nodeToProcess = nodes.Where(node => !pathsToNode.ContainsKey(node)).FirstOrDefault(
            node => edges.Where(edge => edge.Item2 == node).All(edge => pathsToNode.ContainsKey(edge.Item1)), null);
        }
        using (StreamWriter writer = new StreamWriter(FILENAME))
        {
          writer.WriteLine("digraph G {");
          nodes = nodes.Select(node => nodeName(node, pathsToNode)).ToHashSet();
          foreach (var node in nodes) {
            writer.WriteLine("\"" + node + "\";");
          }
          foreach (var edge in edges) {
            if (edge.Item1.StartsWith(ImplPrefix)) {
              writer.WriteLine("\"" + nodeName(edge.Item1, pathsToNode) + "\" -> \"" +
                               nodeName(edge.Item2, pathsToNode) + "\" [label=\"" + edge.Item3 + "\" decorate=true];");
            }
          }
          writer.WriteLine("}");
        }
      }

      private string nodeName(string node, Dictionary<string, int> pathsToNode) {
        if (!pathsToNode.ContainsKey(node)) {
         return toVerbose[node].Split(" ").First() + " [recurse]";
        }
        return toVerbose[node].Split(" ").First() + " [" + pathsToNode[node] + "]";
      }*/
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
        } else if (modifier.timesToInline.TryGetValue(node.Name, out var value)) {
          // This method is inlined (and hence tested)
          var depthExpression =
            new LiteralExpr(new Token(), BigNum.FromUInt(value));
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
