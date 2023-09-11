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

    private IEnumerable<ProgramModification> VisitImplementation(
      Implementation node) {
      implementation = node;
      if (!ImplementationIsToBeTested(node) ||
          !DafnyInfo.IsAccessible(node.VerboseName.Split(" ")[0])) {
        yield break;
      }
      var testEntryNames = Utils.DeclarationHasAttribute(implementation, TestGenerationOptions.TestInlineAttribute)
        ? TestEntries
        : new() { implementation.VerboseName };
      var blocks = node.Blocks.ToList();
      foreach (var block in blocks) {
        var state = Utils.GetBlockId(block, DafnyInfo.Options);
        if (state == null) {
          continue;
        }
        block.cmds.Add(new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));
        var record = modifications.GetProgramModification(program, implementation,
          new HashSet<string>() { state },
          testEntryNames, $"{implementation.VerboseName.Split(" ")[0]} ({state})");
        if (record.IsCovered(modifications)) {
          block.cmds.RemoveAt(block.cmds.Count - 1);
          continue;
        }
        yield return record;
        block.cmds.RemoveAt(block.cmds.Count - 1);
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