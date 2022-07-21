using System.Collections.Generic;
using Microsoft.Boogie;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail when a particular basic block is visited
  /// </summary>
  public class BlockBasedModifier : ProgramModifier {
    
    private Implementation? implementation; // the implementation currently traversed
    private Program? program; // the original program

    protected override IAsyncEnumerable<ProgramModification> GetModifications(Program p) {
      return VisitProgram(p);
    }

    private ProgramModification? VisitBlock(Block node) {
      if (program == null || implementation == null) {
        return null;
      }
      base.VisitBlock(node);
      if (node.cmds.Count == 0) { // ignore blocks with zero commands
        return null;
      }
      node.cmds.Add(new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));
      var record = new BlockBasedModification(program,
          ImplementationToTarget?.VerboseName ?? implementation.VerboseName,
          node.UniqueId, ExtractCapturedStates(node));

      node.cmds.RemoveAt(node.cmds.Count - 1);
      return record;
    }

    private async IAsyncEnumerable<ProgramModification> VisitImplementation(Implementation node) {
      implementation = node;
      if (ImplementationIsToBeTested(node) && 
          dafnyInfo.IsAccessible(node.VerboseName.Split(" ")[0])) {
        for (int i = node.Blocks.Count - 1; i >= 0; i--) {
          var modification = VisitBlock(node.Blocks[i]);
          if (modification != null) {
            yield return modification;
          }
        }
      }
    }

    private async IAsyncEnumerable<ProgramModification> VisitProgram(Program node) {
      program = node;
      foreach (var implementation in node.Implementations) {
        await foreach (var modification in VisitImplementation(implementation)) {
          yield return modification;
        }
      }
    }

    /// <summary>
    /// Return the list of all states covered by the block.
    /// A state is represented by the string recorded via :captureState
    /// </summary>
    private static ISet<string> ExtractCapturedStates(Block node) {
      HashSet<string> result = new();
      foreach (var cmd in node.cmds) {
        if (!(cmd is AssumeCmd assumeCmd)) {
          continue;
        }
        if (assumeCmd.Attributes?.Key == "captureState") {
          result.Add(assumeCmd.Attributes?.Params?[0]?.ToString() ?? "");
        }
      }
      return result;
    }
  }
}