using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  internal class BoogieStmtListBuilder {
    public DafnyOptions Options { get; }
    public StmtListBuilder builder;
    public Translator tran;

    public BoogieStmtListBuilder(Translator tran, DafnyOptions options) {
      builder = new Boogie.StmtListBuilder();
      this.tran = tran;
      this.Options = options;
    }

    public void Add(Cmd cmd) {
      builder.Add(cmd);
      if (cmd is Boogie.AssertCmd) {
        tran.assertionCount++;
      } else if (cmd is Boogie.CallCmd call) {
        // A call command may involve a precondition, but we can't tell for sure until the callee
        // procedure has been generated. Therefore, to be on the same side, we count this call
        // as a possible assertion, unless it's a procedure that's part of the translation and
        // known not to have any preconditions.
        if (call.callee == "$IterHavoc0" || call.callee == "$IterHavoc1" || call.callee == "$YieldHavoc") {
          // known not to have any preconditions
        } else {
          tran.assertionCount++;
        }
      }
    }

    public void Add(StructuredCmd scmd) {
      builder.Add(scmd);
      if (scmd is Boogie.WhileCmd whyle && whyle.Invariants.Any(inv => inv is Boogie.AssertCmd)) {
        tran.assertionCount++;
      }
    }

    public void Add(TransferCmd tcmd) { builder.Add(tcmd); }
    public void AddLabelCmd(string label) { builder.AddLabelCmd(label); }
    public void AddLocalVariable(string name) { builder.AddLocalVariable(name); }

    public StmtList Collect(Boogie.IToken tok) {
      return builder.Collect(tok);
    }
  }
}