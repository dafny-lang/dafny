// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

public class PartialValue {

  public readonly Model.Element Element; // the element in the counterexample model associated with the value
  public readonly List<Constraint> Constraints;
  private readonly PartialState state; // corresponding state in the counterexample model
  private readonly Type type;
  private bool haveExpanded;

  private bool nullable = false;
  public bool Nullable => nullable;

  internal static PartialValue Get(Model.Element element, PartialState state) {
    if (state.allPartialValues.TryGetValue(element, out var value)) {
      return value;
    }
    return new PartialValue(element, state);
  }

  private PartialValue(Model.Element element, PartialState state) {
    Element = element;
    this.state = state;
    Constraints = new();
    haveExpanded = false;
    state.allPartialValues[element] = this;
    type = state.Model.GetFormattedDafnyType(element);
    new TypeTestConstraint(this, type);
    state.Model.AddTypeConstraints(this);
  }

  public IEnumerable<PartialValue> GetRelatedValues() {
    var relatedValues = new HashSet<PartialValue>() { this };
    if (!haveExpanded) {
      state.Model.GetExpansion(state, this);
      haveExpanded = true;
    }
    foreach (var constraint in Constraints) {
      foreach (var value in constraint.ReferencedValues) {
        if (!relatedValues.Contains(value)) {
          relatedValues.Add(value);
          yield return value;
        }
      }

      if (constraint is DefinitionConstraint definitionConstraint &&
          !relatedValues.Contains(definitionConstraint.DefinedValue)) {
        relatedValues.Add(definitionConstraint.DefinedValue);
        yield return definitionConstraint.DefinedValue;
      }
    }
  }

  public string ShortName => ""; // TODO

  public Type Type => type;

  public string PrimitiveLiteral {
    get {
      return Constraints.OfType<LiteralExprConstraint>()
        .Select(literal => literal.LiteralExpr.ToString()).FirstOrDefault() ?? "";
    }
  }

  public Dictionary<string, PartialValue> Fields() {
    var fields = new Dictionary<string, PartialValue>();
    foreach (var memberSelectExpr in Constraints.OfType<MemberSelectExprConstraint>().Where(constraint => constraint.Obj == this)) {
      fields[memberSelectExpr.MemberName] = memberSelectExpr.DefinedValue;
    }
    return fields;
  }

  public IEnumerable<PartialValue> UnnamedDestructors() {
    var datatypeValue = Constraints.OfType<DatatypeValueConstraint>().FirstOrDefault(constraint => constraint.DefinedValue == this);
    if (datatypeValue != null) {
      foreach (var destructor in datatypeValue.UnnamedDestructors) {
        yield return destructor;
      }
    }
  }

  public IEnumerable<PartialValue> SetElements() {
    return Constraints.OfType<ContainmentConstraint>()
      .Where(containment => containment.Set == this)
      .Select(containment => containment.Element);
  }

  public string DatatypeConstructorName() {
    return Constraints.OfType<DatatypeConstructorCheckConstraint>()
      .Select(constructorCheck => constructorCheck.ConstructorName).FirstOrDefault() ?? "";
  }

  public IEnumerable<(PartialValue Key, PartialValue Value)> Mappings() {
    foreach (var mapping in Constraints.OfType<MapSelectExprConstraint>().Where(constraint => constraint.Map == this)) {
      yield return new(mapping.Key, mapping.DefinedValue);
    }
  }

  public int? Cardinality() {
    if (Type is not SeqType or SetType or MapType) {
      return -1;
    }

    if (Constraints.OfType<EmptyConstraint>().Any()) {
      return 0;
    }

    var cardinality = Constraints.OfType<CardinalityConstraint>().FirstOrDefault(constraint => constraint.Collection == this)?.DefinedValue;
    if (cardinality == null) {
      return -1;
    }
    var cardinalityLiteral = cardinality.Constraints.OfType<LiteralExprConstraint>().FirstOrDefault()?.LiteralExpr as LiteralExpr;
    if (cardinalityLiteral == null) {
      return -1;
    }
    if (cardinalityLiteral.Value is not BigInteger bigInteger ||
      !bigInteger.LessThanOrEquals(new BigInteger(int.MaxValue))) {
      return -1;
    }

    return (int)bigInteger;
  }


  public PartialValue this[int i] {
    get {
      foreach (var seqSelectConstraint in Constraints.OfType<SeqSelectExprWithLiteralConstraint>()
                 .Where(constraint => constraint.Seq == this)) {
        if (seqSelectConstraint.Index.ToString() == i.ToString()) {
          return seqSelectConstraint.DefinedValue;
        }
      }
      foreach (var seqSelectConstraint in Constraints.OfType<SeqSelectExprConstraint>()
                 .Where(constraint => constraint.Seq == this)) {
        var indexLiteral = seqSelectConstraint.Index.Constraints.OfType<LiteralExprConstraint>().FirstOrDefault()?.LiteralExpr;
        if (indexLiteral != null && indexLiteral.ToString() == i.ToString()) {
          return seqSelectConstraint.DefinedValue;
        }
      }
      return null;
    }
  }

  public override bool Equals(object obj) {
    return obj is PartialValue other && other.Element == Element && other.state == state;
  }

  public override int GetHashCode() {
    return Element.GetHashCode();
  }

}