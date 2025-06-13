#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public abstract class OneBodyLoopStmt : LoopStmt {
  public BlockStmt? Body;

  [FilledInDuringResolution]
  public WhileStmt.LoopBodySurrogate? BodySurrogate;  // set by Resolver; remains null unless Body==null

  protected OneBodyLoopStmt(Cloner cloner, OneBodyLoopStmt original) : base(cloner, original) {
    Body = (BlockStmt)cloner.CloneStmt(original.Body, false);
    if (cloner.CloneResolvedFields) {
      if (original.BodySurrogate != null) {
        BodySurrogate = new WhileStmt.LoopBodySurrogate(
          original.BodySurrogate.LocalLoopTargets.Select(v => cloner.CloneIVariable(v, true)).ToList(),
          original.BodySurrogate.UsesHeap);
      }
    }
  }

  [SyntaxConstructor]
  protected OneBodyLoopStmt(IOrigin origin,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt? body, List<Label> labels, Attributes? attributes)
    : base(origin, invariants, decreases, mod, labels, attributes) {
    Body = body;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Body != null) {
        yield return Body;
      }
    }
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    if (Body is null) {
      yield return new Assumption(decl, Origin, AssumptionDescription.LoopWithoutBody);
    }
  }

  public void ComputeBodySurrogate(ErrorReporter reporter) {
    if (Body != null) {
      // the loop already has a body
      return;
    }

    var fvs = new HashSet<IVariable>();
    var usesHeap = false;

    if (this is WhileStmt { Guard: { } whileGuard }) {
      FreeVariablesUtil.ComputeFreeVariables(reporter.Options, whileGuard, fvs, ref usesHeap);

    } else if (this is ForLoopStmt forS) {
      var loopIndex = forS.LoopIndex;
      fvs.Add(loopIndex);

      FreeVariablesUtil.ComputeFreeVariables(reporter.Options, forS.Start, fvs, ref usesHeap);
      if (forS.End != null) {
        FreeVariablesUtil.ComputeFreeVariables(reporter.Options, forS.End, fvs, ref usesHeap);
      }
    }

    foreach (AttributedExpression inv in Invariants) {
      FreeVariablesUtil.ComputeFreeVariables(reporter.Options, inv.E, fvs, ref usesHeap);
    }
    foreach (Expression e in Decreases.Expressions!) {
      FreeVariablesUtil.ComputeFreeVariables(reporter.Options, e, fvs, ref usesHeap);
    }
    if (Mod.Expressions != null) {
      usesHeap = true;  // bearing a modifies clause counts as using the heap
    }

    Contract.Assert(BodySurrogate == null); // .BodySurrogate is set only once
    var loopFrame = new List<IVariable>();
    if (this is ForLoopStmt forLoopStmt) {
      loopFrame.Add(forLoopStmt.LoopIndex);
    }
    loopFrame.AddRange(fvs.Where(fv => fv.IsMutable));
    BodySurrogate = new WhileStmt.LoopBodySurrogate(loopFrame, usesHeap);
    var text = BodySurrogate.LocalLoopTargets.Comma(fv => fv.Name);
    if (BodySurrogate.UsesHeap) {
      text += text.Length == 0 ? "$Heap" : ", $Heap";
    }
    text = $"this loop has no body{(text.Length == 0 ? "" : " (loop frame: " + text + ")")}";
    reporter.Warning(MessageSource.Resolver, "", Origin, text);
  }

}