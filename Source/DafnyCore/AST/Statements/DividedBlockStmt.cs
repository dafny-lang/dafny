using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/**
   * Used by two phase constructors: https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#13323-two-phase-constructors
   */
public class DividedBlockStmt : BlockStmt, ICloneable<DividedBlockStmt> {
  public List<Statement> BodyInit;  // first part of Body's statements
  public IOrigin SeparatorTok;  // token that separates the two parts, if any
  public List<Statement> BodyProper;  // second part of Body's statements

  public new DividedBlockStmt Clone(Cloner cloner) {
    return new DividedBlockStmt(cloner, this);
  }

  public DividedBlockStmt(Cloner cloner, DividedBlockStmt original) : base(cloner, original) {
    BodyInit = Body.Take(original.BodyInit.Count).ToList();
    BodyProper = Body.Skip(original.BodyInit.Count).ToList();
    SeparatorTok = original.SeparatorTok;
  }

  public DividedBlockStmt(IOrigin origin, List<Statement> bodyInit, IOrigin/*?*/ separatorTok, List<Statement> bodyProper)
    : base(origin, Util.Concat(bodyInit, bodyProper)) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(bodyInit));
    Contract.Requires(cce.NonNullElements(bodyProper));
    this.BodyInit = bodyInit;
    this.SeparatorTok = separatorTok;
    this.BodyProper = bodyProper;
  }
  public override void AppendStmt(Statement s) {
    BodyProper.Add(s);
    base.AppendStmt(s);
  }
}