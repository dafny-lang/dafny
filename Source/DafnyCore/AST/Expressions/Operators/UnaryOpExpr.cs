using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class UnaryOpExpr : UnaryExpr, ICloneable<UnaryOpExpr> {
  public enum Opcode {
    Not,  // boolean negation or bitwise negation
    Cardinality,
    Fresh, // fresh also has a(n optional) second argument, namely the @-label
    Allocated,
    Lit,  // there is no syntax for this operator, but it is sometimes introduced during translation
    Assigned,
    Negate,  // replaced by 0 - x during resolution in most cases (preserves IEEE 754 semantics for -0.0)
  }
  public Opcode Op;

  public enum ResolvedOpcode {
    YetUndetermined,
    BVNot,
    BoolNot,
    SeqLength,
    SetCard,
    MultiSetCard,
    MapCard,
    Fresh,
    Allocated,
    Lit,
    Assigned,
    FloatNegate,
  }

  private ResolvedOpcode _ResolvedOp = ResolvedOpcode.YetUndetermined;
  public ResolvedOpcode ResolvedOp => ResolveOp();

  public ResolvedOpcode ResolveOp() {
    if (_ResolvedOp == ResolvedOpcode.YetUndetermined) {
      Contract.Assert(Type != null);
      Contract.Assert(Type is not TypeProxy);
      _ResolvedOp = (Op, E.Type.NormalizeToAncestorType()) switch {
        (Opcode.Not, BoolType _) => ResolvedOpcode.BoolNot,
        (Opcode.Not, BitvectorType _) => ResolvedOpcode.BVNot,
        (Opcode.Cardinality, SeqType _) => ResolvedOpcode.SeqLength,
        (Opcode.Cardinality, SetType _) => ResolvedOpcode.SetCard,
        (Opcode.Cardinality, MultiSetType _) => ResolvedOpcode.MultiSetCard,
        (Opcode.Cardinality, MapType _) => ResolvedOpcode.MapCard,
        (Opcode.Fresh, _) => ResolvedOpcode.Fresh,
        (Opcode.Allocated, _) => ResolvedOpcode.Allocated,
        (Opcode.Lit, _) => ResolvedOpcode.Lit,
        (Opcode.Assigned, _) => ResolvedOpcode.Assigned,
        (Opcode.Negate, Fp32Type _) => ResolvedOpcode.FloatNegate,
        (Opcode.Negate, Fp64Type _) => ResolvedOpcode.FloatNegate,
        _ => ResolvedOpcode.YetUndetermined // Unreachable
      };
      Contract.Assert(_ResolvedOp != ResolvedOpcode.YetUndetermined);
    }

    return _ResolvedOp;
  }

  public void SetResolveOp(ResolvedOpcode resolvedOpcode) {
    Contract.Assert(resolvedOpcode != ResolvedOpcode.YetUndetermined);
    Contract.Assert(_ResolvedOp == ResolvedOpcode.YetUndetermined || _ResolvedOp == resolvedOpcode);
    _ResolvedOp = resolvedOpcode;
  }

  [SyntaxConstructor]
  public UnaryOpExpr(IOrigin origin, Opcode op, Expression e)
    : base(origin, e) {
    Contract.Requires(origin != null);
    Contract.Requires(e != null);
    Contract.Requires(op != Opcode.Fresh || this is FreshExpr);
    this.Op = op;
  }

  public UnaryOpExpr(Cloner cloner, UnaryOpExpr original) : base(cloner, original) {
    Op = original.Op;
  }

  public override bool IsImplicit => Op == Opcode.Lit;
  public UnaryOpExpr Clone(Cloner cloner) {
    return new UnaryOpExpr(cloner, this);
  }
}