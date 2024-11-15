using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class Specialization {
  public readonly List<Formal/*!*/> Formals;
  public readonly List<Expression/*!*/> ReplacementExprs;
  public readonly List<BoundVar/*!*/> ReplacementFormals;
  public readonly Dictionary<IVariable, Expression> SubstMap;
  readonly BoogieGenerator boogieGenerator;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Formals));
    Contract.Invariant(cce.NonNullElements(ReplacementExprs));
    Contract.Invariant(Formals.Count == ReplacementExprs.Count);
    Contract.Invariant(cce.NonNullElements(ReplacementFormals));
    Contract.Invariant(SubstMap != null);
  }

  public Specialization(IVariable formal, MatchCase mc, Specialization prev, BoogieGenerator boogieGenerator) {
    Contract.Requires(formal is Formal || formal is BoundVar);
    Contract.Requires(mc != null);
    Contract.Requires(prev == null || formal is BoundVar || !prev.Formals.Contains((Formal)formal));
    Contract.Requires(boogieGenerator != null);

    this.boogieGenerator = boogieGenerator;

    List<Expression> rArgs = new List<Expression>();
    foreach (BoundVar p in mc.Arguments) {
      IdentifierExpr ie = new IdentifierExpr(p.tok, p.AssignUniqueName(boogieGenerator.CurrentDeclaration.IdGenerator));
      ie.Var = p; ie.Type = ie.Var.Type;  // resolve it here
      rArgs.Add(ie);
    }
    // create and resolve datatype value
    var r = new DatatypeValue(mc.tok, mc.Ctor.EnclosingDatatype.Name, mc.Ctor.Name, rArgs);
    r.Ctor = mc.Ctor;
    r.Type = new UserDefinedType(mc.tok, mc.Ctor.EnclosingDatatype.Name, new List<Type>()/*this is not right, but it seems like it won't matter here*/);

    Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
    substMap.Add(formal, r);

    // Fill in the fields
    Formals = new List<Formal>();
    ReplacementExprs = new List<Expression>();
    ReplacementFormals = new List<BoundVar>();
    SubstMap = new Dictionary<IVariable, Expression>();
    if (prev != null) {
      Formals.AddRange(prev.Formals);
      foreach (var e in prev.ReplacementExprs) {
        ReplacementExprs.Add(BoogieGenerator.Substitute(e, null, substMap));
      }
      foreach (var rf in prev.ReplacementFormals) {
        if (rf != formal) {
          ReplacementFormals.Add(rf);
        }
      }
      foreach (var entry in prev.SubstMap) {
        SubstMap.Add(entry.Key, BoogieGenerator.Substitute(entry.Value, null, substMap));
      }
    }
    if (formal is Formal) {
      Formals.Add((Formal)formal);
      ReplacementExprs.Add(r);
    }
    ReplacementFormals.AddRange(mc.Arguments);
    SubstMap.Add(formal, r);
  }
}