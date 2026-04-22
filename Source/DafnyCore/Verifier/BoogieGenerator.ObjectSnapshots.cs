using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  public class ObjectFieldSnapshotState {
    readonly BoogieGenerator boogieGenerator;
    readonly Dictionary<Field, Bpl.Function> fieldSnapshots;
    Bpl.Function allocationSnapshot;

    public ObjectFieldSnapshotState(BoogieGenerator boogieGenerator, Bpl.Expr legacyHeap)
      : this(boogieGenerator, legacyHeap, new Dictionary<Field, Bpl.Function>(), null) {
    }

    ObjectFieldSnapshotState(BoogieGenerator boogieGenerator, Bpl.Expr legacyHeap,
      Dictionary<Field, Bpl.Function> fieldSnapshots, Bpl.Function allocationSnapshot) {
      this.boogieGenerator = boogieGenerator;
      LegacyHeap = legacyHeap;
      this.fieldSnapshots = fieldSnapshots;
      this.allocationSnapshot = allocationSnapshot;
    }

    public Bpl.Expr LegacyHeap { get; }

    public ObjectFieldSnapshotState Clone(Bpl.Expr legacyHeap) {
      return new ObjectFieldSnapshotState(boogieGenerator, legacyHeap, new Dictionary<Field, Bpl.Function>(fieldSnapshots), allocationSnapshot);
    }

    public Bpl.Expr ReadField(IOrigin tok, Field field, Bpl.Expr receiver) {
      Contract.Requires(field != null);
      Contract.Requires(field.IsMutable);
      Contract.Requires(receiver != null);
      return boogieGenerator.ApplyUnarySnapshot(tok, GetFieldSnapshot(tok, field), receiver);
    }

    public Bpl.Expr ReadAlloc(IOrigin tok, Bpl.Expr receiver) {
      Contract.Requires(receiver != null);
      return boogieGenerator.ApplyUnarySnapshot(tok, GetAllocationSnapshot(tok), receiver);
    }

    public void UpdateField(IOrigin tok, Field field, Bpl.Expr receiver, Bpl.Expr boxedValue) {
      Contract.Requires(field != null);
      Contract.Requires(field.IsMutable);
      Contract.Requires(receiver != null);
      Contract.Requires(boxedValue != null);

      var previous = GetFieldSnapshot(tok, field);
      var next = boogieGenerator.CreateUnarySnapshotFunction(tok, $"$FieldSnapshot${field.FullSanitizedName}$");
      boogieGenerator.EmitUnarySnapshotUpdateAxioms(tok, next, previous, receiver, boxedValue);
      fieldSnapshots[field] = next;
    }

    public void MarkAllocated(IOrigin tok, Bpl.Expr receiver) {
      Contract.Requires(receiver != null);

      var previous = GetAllocationSnapshot(tok);
      var next = boogieGenerator.CreateUnarySnapshotFunction(tok, "$AllocSnapshot$");
      boogieGenerator.EmitUnarySnapshotUpdateAxioms(tok, next, previous, receiver, boogieGenerator.ApplyBox(tok, Bpl.Expr.True));
      allocationSnapshot = next;
    }

    Bpl.Function GetFieldSnapshot(IOrigin tok, Field field) {
      if (!fieldSnapshots.TryGetValue(field, out var snapshot)) {
        snapshot = boogieGenerator.CreateUnarySnapshotFunction(tok, $"$FieldSnapshot${field.FullSanitizedName}$base$");
        var fieldId = new Bpl.IdentifierExpr(tok, boogieGenerator.GetField(field));
        boogieGenerator.EmitUnarySnapshotSeedAxiom(tok, snapshot, arg => boogieGenerator.ReadHeap(tok, LegacyHeap, arg, fieldId));
        fieldSnapshots[field] = snapshot;
      }
      return snapshot;
    }

    Bpl.Function GetAllocationSnapshot(IOrigin tok) {
      if (allocationSnapshot == null) {
        allocationSnapshot = boogieGenerator.CreateUnarySnapshotFunction(tok, "$AllocSnapshot$base$");
        var allocField = boogieGenerator.Predef.Alloc(tok);
        boogieGenerator.EmitUnarySnapshotSeedAxiom(tok, allocationSnapshot, arg => boogieGenerator.ReadHeap(tok, LegacyHeap, arg, allocField));
      }
      return allocationSnapshot;
    }
  }

  public ObjectFieldSnapshotState CreateObjectFieldSnapshotState(Bpl.Expr legacyHeap) {
    return legacyHeap == null ? null : new ObjectFieldSnapshotState(this, legacyHeap);
  }

  Bpl.Function CreateUnarySnapshotFunction(IOrigin tok, string prefix) {
    var name = CurrentIdGenerator.FreshId(prefix);
    var formals = new List<Bpl.Variable> {
      new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "arg", Predef.RefType), true)
    };
    var result = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, Bpl.TypedIdent.NoName, Predef.BoxType), false);
    var function = new Bpl.Function(tok, name, [], formals, result, null, null);
    sink.AddTopLevelDeclaration(function);
    return function;
  }

  Bpl.Expr ApplyUnarySnapshot(IOrigin tok, Bpl.Function function, Bpl.Expr argument) {
    return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(function),
      new List<Bpl.Expr> { argument }) {
      Type = Predef.BoxType
    };
  }

  void EmitUnarySnapshotSeedAxiom(IOrigin tok, Bpl.Function snapshot, System.Func<Bpl.Expr, Bpl.Expr> rhsFactory) {
    var argVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "arg", Predef.RefType));
    var arg = new Bpl.IdentifierExpr(tok, argVar);
    var lhs = ApplyUnarySnapshot(tok, snapshot, arg);
    var body = Bpl.Expr.Eq(lhs, rhsFactory(arg));
    var trigger = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { lhs });
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok,
      new Bpl.ForallExpr(tok, [], new List<Variable> { argVar }, null, trigger, body)));
  }

  void EmitUnarySnapshotUpdateAxioms(IOrigin tok, Bpl.Function next, Bpl.Function previous, Bpl.Expr receiver, Bpl.Expr boxedValue) {
    var argVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "arg", Predef.RefType));
    var arg = new Bpl.IdentifierExpr(tok, argVar);
    var lhs = ApplyUnarySnapshot(tok, next, arg);
    var previousValue = ApplyUnarySnapshot(tok, previous, arg);
    var trigger = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { lhs });

    var equalCase = BplImp(Bpl.Expr.Eq(arg, receiver), Bpl.Expr.Eq(lhs, boxedValue));
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok,
      new Bpl.ForallExpr(tok, [], new List<Variable> { argVar }, null, trigger, equalCase)));

    var distinctCase = BplImp(Bpl.Expr.Neq(arg, receiver), Bpl.Expr.Eq(lhs, previousValue));
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok,
      new Bpl.ForallExpr(tok, [], new List<Variable> { argVar }, null, trigger, distinctCase)));
  }
}
