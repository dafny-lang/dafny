using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Declaration = Microsoft.Boogie.Declaration;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LocalVariable = Microsoft.Boogie.LocalVariable;
using Parser = Microsoft.Boogie.Parser;
using Program = Microsoft.Boogie.Program;

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

    /// <summary>
    /// Create tests and return the list of bpl test files
    /// </summary>
    public IEnumerable<ProgramModification> GetModifications(IEnumerable<Program> programs) {
      var program = MergeBoogiePrograms(programs);
      program = new AddImplementationsForCalls().VisitProgram(program);
      var annotator = new AnnotationVisitor();
      program = annotator.VisitProgram(program);
      ImplementationToTarget = annotator.ImplementationToTarget;
      var callGraphVisitor = new CallGraphVisitor();
      callGraphVisitor.VisitProgram(program);
      toModify = callGraphVisitor.GetCallees(ImplementationToTarget?.Name);
      AddAxioms(program);
      return GetModifications(program);
    }

    protected abstract IEnumerable<ProgramModification> GetModifications(Program p);

    protected bool ImplementationIsToBeTested(Implementation impl) =>
      (ImplementationToTarget == null || toModify.Contains(impl.Name)) &&
      impl.Name.StartsWith("Impl$$") && !impl.Name.EndsWith("__ctor");

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
    /// Create implementations for all "Call$$" procedures by making them
    /// call the respective "Impl$$ implementations. This allows to implement
    /// inlining of Dafny methods further down the road.
    /// </summary>
    private class AddImplementationsForCalls : ReadOnlyVisitor {

      private List<Implementation> implsToAdd = new();
      private Program? program;

      public override Procedure? VisitProcedure(Procedure? node) {
        if (program == null || node == null ||
            !node.Name.StartsWith("Call$$")) {
          return node;
        }

        var callerName = node.Name;
        var calleName = $"Impl$${node.Name.Split("$").Last()}";
        var calleeProc = program.FindProcedure(calleName);
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
          (Variable)new LocalVariable(new Token(),
            new TypedIdent(new Token(), v.Name, v.TypedIdent.Type))).ToList();
        var outParams = node.OutParams.ConvertAll(v =>
          (Variable)new LocalVariable(new Token(),
            new TypedIdent(new Token(), v.Name, v.TypedIdent.Type))).ToList();
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
    }
  }
}
