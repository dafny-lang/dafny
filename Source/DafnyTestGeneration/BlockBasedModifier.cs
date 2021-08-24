using System.Collections.Generic;
using Microsoft.Boogie;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail when a particular basic block is visited
  /// </summary>
  public class BlockBasedModifier : ProgramModifier {

    private string? implName; // name of the implementation currently traversed
    private Program? program; // the original program
    private List<ProgramModification> modifications = new();

    protected override List<ProgramModification> Modify(Program p) {
      modifications = new List<ProgramModification>();
      VisitProgram(p);
      return modifications;
    }

    public override Block VisitBlock(Block node) {
      if (program == null || implName == null) {
        return node;
      }
      base.VisitBlock(node);
      if (node.cmds.Count == 0) { // ignore blocks with zero commands
        return node;
      }
      node.cmds.Add(GetCmd("assert false;"));
      var record = new BlockBasedModification(program,
        ProcedureName ?? implName,
        node.UniqueId);
      modifications.Add(record);
      node.cmds.RemoveAt(node.cmds.Count - 1);
      return node;
    }

    public override Implementation VisitImplementation(Implementation node) {
      implName = node.Name;
      if (ProcedureIsToBeTested(node.Name)) {
        VisitBlockList(node.Blocks);
      }
      return node;
    }

    public override Program VisitProgram(Program node) {
      program = node;
      return base.VisitProgram(node);
    }
  }
}