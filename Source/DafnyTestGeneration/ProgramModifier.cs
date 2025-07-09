// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
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
    internal const string ImplPrefix = "Impl$$";
    internal const string CtorPostfix = "__ctor";
    protected DafnyInfo DafnyInfo;
    protected HashSet<string> TestEntries;

    /// <summary>
    /// Create tests and return the list of bpl test files
    /// </summary>
    public IEnumerable<ProgramModification> GetModifications(
      Program program,
      DafnyInfo dafnyInfo) {
      DafnyInfo = dafnyInfo;
      var options = dafnyInfo.Options;
      BlockCoalescer.CoalesceBlocks(program);
      foreach (var implementation in program.Implementations.Where(i => Utils.DeclarationHasAttribute(i, TestGenerationOptions.TestInlineAttribute))) {
        var depthExpression = Utils.GetAttributeValue(implementation, TestGenerationOptions.TestInlineAttribute)
          .FirstOrDefault(new LiteralExpr(Microsoft.Boogie.Token.NoToken, BigNum.ONE));
        var attribute = new QKeyValue(new Token(), "inline",
          new List<object>() { depthExpression }, null);
        attribute.Next = implementation.Attributes;
        implementation.Attributes = attribute;
      }
      if (options.TestGenOptions.Mode is TestGenerationOptions.Modes.Block or TestGenerationOptions.Modes.Path) {
        program = new AnnotationVisitor(options).VisitProgram(program);
      }
      AddAxioms(options, program);
      program.Resolve(options);
      program.Typecheck(options);
      using (var engine = ExecutionEngine.CreateWithoutSharedCache(options)) {
        engine.EliminateDeadVariables(program);
        engine.CollectModSets(program);
        engine.Inline(program);
      }
      program.RemoveTopLevelDeclarations(declaration => declaration is Implementation or Procedure && Utils.DeclarationHasAttribute(declaration, "inline"));
      program = new RemoveChecks(options).VisitProgram(program);
      if (options.TestGenOptions.Mode is TestGenerationOptions.Modes.InlinedBlock) {
        program = new AnnotationVisitor(options).VisitProgram(program);
      }
      program = Utils.DeepCloneResolvedProgram(program, options); // need to make sure the program is resolved and typed
      TestEntries = program.Implementations
        .Where(implementation =>
          Utils.DeclarationHasAttribute(implementation, TestGenerationOptions.TestEntryAttribute) &&
          implementation.Name.StartsWith(ImplPrefix)).Select(implementation => implementation.VerboseName).ToHashSet();
      if (options.TestGenOptions.PrintBpl != null) {
        File.WriteAllText(options.TestGenOptions.PrintBpl,
          Utils.GetStringRepresentation(options, program));
      }
      return GetModifications(program);
    }

    protected abstract IEnumerable<ProgramModification> GetModifications(Program p);

    protected bool ImplementationIsToBeTested(Implementation impl) =>
      Utils.DeclarationHasAttribute(impl, TestGenerationOptions.TestEntryAttribute) &&
    impl.Name.StartsWith(ImplPrefix) && !impl.Name.EndsWith(CtorPostfix);

    /// <summary>
    /// Add axioms necessary for counterexample generation to work efficiently
    /// </summary>
    private static void AddAxioms(DafnyOptions options, Program program) {
      if (options.TestGenOptions.SeqLengthLimit == 0) {
        return;
      }
      var limit = (uint)options.TestGenOptions.SeqLengthLimit;
      Parser.Parse($"axiom (forall y: Seq :: " +
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
      data.ForEach(obj => toPrint.AddRange(new List<object> { obj, separator }));
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
    /// Annotate the AST with "assume true" print statements inserted at:
    /// (1)     the beginning of each implementation, to get the parameter types
    ///         and values leading to assertion or post-condition violation.
    /// (2)     the end of each block, to get execution trace.
    /// </summary>
    private class AnnotationVisitor : StandardVisitor {
      private Implementation/*?*/ implementation;
      private DafnyOptions options;

      public AnnotationVisitor(DafnyOptions options) {
        this.options = options;
      }

      public override Block VisitBlock(Block node) {
        int afterPartition = node.Cmds.FindIndex(cmd =>
          cmd is not AssumeCmd assumeCmd || assumeCmd.Attributes == null || assumeCmd.Attributes.Key != "partition");
        afterPartition = afterPartition > -1 ? afterPartition : 0;
        foreach (var state in Utils.AllBlockIds(node, options)) {
          var data = new List<object>
            { "Block", implementation.Name, state };
          node.Cmds.Insert(afterPartition, GetAssumePrintCmd(data));
        }
        return base.VisitBlock(node);
      }

      public override Implementation VisitImplementation(Implementation node) {
        implementation = node;
        // print parameter types:
        var data = new List<object> { "Types" };
        data.AddRange(node.InParams.Select(var =>
          var.TypedIdent.Type.ToString()));
        node.Blocks[0].Cmds.Insert(0, GetAssumePrintCmd(data));

        // record parameter values:
        data = ["Impl", node.VerboseName.Split(" ")[0]];
        data.AddRange(node.InParams.Select(var => new IdentifierExpr(new Token(), var)));
        node.Blocks[0].Cmds.Insert(0, GetAssumePrintCmd(data));
        if (Utils.DeclarationHasAttribute(node, TestGenerationOptions.TestEntryAttribute) || Utils.DeclarationHasAttribute(node, TestGenerationOptions.TestInlineAttribute)) {
          VisitBlockList(node.Blocks);
        }
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
    internal class RemoveChecks : StandardVisitor {
      private readonly DafnyOptions options;

      public RemoveChecks(DafnyOptions options) {
        this.options = options;
      }

      public override Block VisitBlock(Block node) {
        var toRemove = node.Cmds.OfType<AssertCmd>().ToList();
        foreach (var cmd in toRemove) {
          var newCmd = new AssumeCmd(new Token(), cmd.Expr, cmd.Attributes);
          node.Cmds.Insert(node.Cmds.IndexOf(cmd), newCmd);
          node.Cmds.Remove(cmd);
        }
        return node;
      }

      public override Procedure VisitProcedure(Procedure node) {
        List<Ensures> newEnsures = [];
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
