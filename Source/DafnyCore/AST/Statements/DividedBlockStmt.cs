#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/**
   * Used by two phase constructors: https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#13323-two-phase-constructors
   */
public class DividedBlockStmt : BlockLikeStmt, ICloneable<DividedBlockStmt> {
  public List<Statement> BodyInit;  // first part of Body's statements
  public IOrigin? SeparatorTok;  // token that separates the two parts, if any
  public List<Statement> BodyProper;  // second part of Body's statements

  public DividedBlockStmt(Cloner cloner, DividedBlockStmt original) : base(cloner, original) {
    BodyInit = original.BodyInit.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    BodyProper = original.BodyProper.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    SeparatorTok = cloner.Origin(original.SeparatorTok);
  }

  [SyntaxConstructor]
  public DividedBlockStmt(IOrigin origin, List<Statement> bodyInit,
    IOrigin? separatorTok, List<Statement> bodyProper, List<Label> labels, Attributes? attributes = null)
    : base(origin, labels, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(bodyInit));
    Contract.Requires(cce.NonNullElements(bodyProper));
    this.BodyInit = bodyInit;
    this.SeparatorTok = separatorTok;
    this.BodyProper = bodyProper;
  }

  public override IReadOnlyList<Statement> Body => BodyInit.Concat(BodyProper);

  public override void AppendStmt(Statement s) {
    BodyProper.Add(s);
  }

  public override void Prepend(Statement s) {
    BodyProper.Insert(0, s);
  }

  public new DividedBlockStmt Clone(Cloner cloner) {
    return new DividedBlockStmt(cloner, this);
  }
}