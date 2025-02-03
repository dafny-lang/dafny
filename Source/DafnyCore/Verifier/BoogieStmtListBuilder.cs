using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class BoogieStmtListBuilder {
    public DafnyOptions Options { get; }
    public BodyTranslationContext Context { get; set; }
    public StmtListBuilder builder;
    public readonly List<object> Commands;
    public BoogieGenerator tran;

    public BoogieStmtListBuilder WithContext(BodyTranslationContext context) {
      if (context == Context) {
        return this;
      }
      return new BoogieStmtListBuilder(Commands, builder, tran, Options, context);
    }

    private BoogieStmtListBuilder(List<object> commands, StmtListBuilder builder, BoogieGenerator tran, DafnyOptions options, BodyTranslationContext context) {
      Commands = commands;
      this.builder = builder;
      this.tran = tran;
      Options = options;
      Context = context;
    }

    public BoogieStmtListBuilder(BoogieGenerator tran, DafnyOptions options, BodyTranslationContext context) {
      builder = new StmtListBuilder();
      this.tran = tran;
      Options = options;
      Commands = [];
      Context = context;
    }

    public void Add(Cmd cmd) {
      Commands.Add(cmd);
      builder.Add(cmd);
      if (cmd is AssertCmd) {
        tran.assertionCount++;
      } else if (cmd is CallCmd call) {
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
      Commands.Add(scmd);
      builder.Add(scmd);
      if (scmd is Boogie.WhileCmd whyle && whyle.Invariants.Any(inv => inv is Boogie.AssertCmd)) {
        tran.assertionCount++;
      }
    }

    public void Add(TransferCmd tcmd) {
      Commands.Add(tcmd);
      builder.Add(tcmd);
    }

    public void AddLabelCmd(IOrigin token, string label) {
      Commands.Add(label);
      builder.AddLabelCmd(token, label);
    }
    public void AddLocalVariable(string name) { builder.AddLocalVariable(name); }

    public StmtList Collect(Boogie.IToken tok) {
      return builder.Collect(tok);
    }
  }
}