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
    private ProgramModification/*?*/ VisitBlock(Block node) {

      if (program == null || implementation == null) {
        return null;
      }

      var state = Utils.GetBlockId(node);
      if (state == null) {
        return null;
      }

      var testEntryNames = Utils.DeclarationHasAttribute(implementation, TestGenerationOptions.TestInlineAttribute)
        ? TestEntries
        : new() { implementation.VerboseName };
      node.cmds.Add(new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));
      var record = modifications.GetProgramModification(program, implementation,
        new HashSet<string>() { state },
          testEntryNames, $"{implementation.VerboseName.Split(" ")[0]} ({state})");

      node.cmds.RemoveAt(node.cmds.Count - 1);
      if (record.IsCovered(modifications)) {
        return null;
      }
      return record;
    }

    private IEnumerable<ProgramModification> VisitImplementation(
      Implementation node) {
      implementation = node;
      if (!ImplementationIsToBeTested(node) ||
          !DafnyInfo.IsAccessible(node.VerboseName.Split(" ")[0])) {
        yield break;
      }
      for (int i = node.Blocks.Count - 1; i >= 0; i--) {
        var modification = VisitBlock(node.Blocks[i]);
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