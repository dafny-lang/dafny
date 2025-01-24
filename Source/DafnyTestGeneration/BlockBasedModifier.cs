// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using Program = Microsoft.Boogie.Program;
using Token = Microsoft.Boogie.Token;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail when a particular basic block is visited
  /// </summary>
  public class BlockBasedModifier : ProgramModifier {
    private readonly Modifications modifications;
    private Implementation/*?*/ implementation; // the implementation currently traversed
    private Program/*?*/ program; // the original program

    public BlockBasedModifier(Modifications modifications) {
      this.modifications = modifications;
    }

    protected override IEnumerable<ProgramModification> GetModifications(Program p) {
      return VisitProgram(p);
    }

    /// <summary>
    /// After inlining, several basic blocks might correspond to the same program state, i.e. location in the Dafny code
    /// This method creates a mapping from such a state to all blocks that represent it
    /// </summary>
    private void PopulateStateToBlocksMap(Block block, Dictionary<string, HashSet<Block>> stateToBlocks) {
      if (program == null || implementation == null) {
        return;
      }
      var state = Utils.GetBlockId(block, DafnyInfo.Options);
      if (state == null) {
        return;
      }
      if (!stateToBlocks.ContainsKey(state)) {
        stateToBlocks[state] = [];
      }
      stateToBlocks[state].Add(block);
    }

    private IEnumerable<ProgramModification> VisitImplementation(
      Implementation node) {
      implementation = node;
      if (!ImplementationIsToBeTested(node) ||
          !DafnyInfo.IsAccessible(node.VerboseName.Split(" ")[0])) {
        yield break;
      }
      var testEntryNames = Utils.DeclarationHasAttribute(implementation, TestGenerationOptions.TestInlineAttribute)
        ? TestEntries
        : [implementation.VerboseName];
      var blocks = node.Blocks.ToList();
      blocks.Reverse();
      var stateToBlocksMap = new Dictionary<string, HashSet<Block>>();
      foreach (var block in node.Blocks) {
        PopulateStateToBlocksMap(block, stateToBlocksMap);
      }
      foreach (var block in blocks) {
        var state = Utils.GetBlockId(block, DafnyInfo.Options);
        if (state == null) {
          continue;
        }
        foreach (var twinBlock in stateToBlocksMap[state]) {
          twinBlock.Cmds.Add(new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));
        }
        var record = modifications.GetProgramModification(program, implementation,
          Utils.AllBlockIds(block, DafnyInfo.Options).ToHashSet(),
          testEntryNames, $"{implementation.VerboseName.Split(" ")[0]} ({state})");
        if (record.IsCovered(modifications)) {
          foreach (var twinBlock in stateToBlocksMap[state]) {
            twinBlock.Cmds.RemoveAt(twinBlock.Cmds.Count - 1);
          }
          continue;
        }
        yield return record;
        foreach (var twinBlock in stateToBlocksMap[state]) {
          twinBlock.Cmds.RemoveAt(twinBlock.Cmds.Count - 1);
        }
      }

    }

    private IEnumerable<ProgramModification> VisitProgram(Program node) {
      program = node;
      var implementations = node.Implementations.ToList();
      foreach (var implementation in implementations) {
        foreach (var modification in VisitImplementation(implementation)) {
          yield return modification;
        }
      }
    }
  }
}