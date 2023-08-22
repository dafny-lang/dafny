// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
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
    private ProgramModification/*?*/ ModificationForBlock(Block node, Dictionary<string, HashSet<Block>> stateToBlocks) {

      if (program == null || implementation == null) {
        return null;
      }
      var state = Utils.GetBlockId(node, DafnyInfo.Options);
      if (state == null) {
        return null;
      }

      var testEntryNames = Utils.DeclarationHasAttribute(implementation, TestGenerationOptions.TestInlineAttribute)
        ? TestEntries
        : new() { implementation.VerboseName };
      foreach (var block in stateToBlocks[state]) {
        block.cmds.Add(new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));
      }
      var record = modifications.GetProgramModification(program, implementation,
        new HashSet<string>() { state },
          testEntryNames, $"{implementation.VerboseName.Split(" ")[0]} ({state})");
      foreach (var block in stateToBlocks[state]) {
        block.cmds.RemoveAt(block.cmds.Count - 1);
      }
      if (record.IsCovered(modifications)) {
        return null;
      }
      return record;
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
        stateToBlocks[state] = new();
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
      var stateToBlocksMap = new Dictionary<string, HashSet<Block>>();
      foreach (var block in node.Blocks) {
        PopulateStateToBlocksMap(block, stateToBlocksMap);
      }
      for (int i = node.Blocks.Count - 1; i >= 0; i--) {
        var modification = ModificationForBlock(node.Blocks[i], stateToBlocksMap);
        if (modification != null) {
          yield return modification;
        }
      }

    }

    private IEnumerable<ProgramModification> VisitProgram(Program node) {
      program = node;
      foreach (var implementation in node.Implementations) {
        foreach (var modification in VisitImplementation(implementation)) {
          yield return modification;
        }
      }
    }
  }
}