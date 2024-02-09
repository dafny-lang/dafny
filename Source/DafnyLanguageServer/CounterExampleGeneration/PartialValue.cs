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
  private readonly List<PartialValue> relatedValues;
  private readonly PartialState state; // corresponding state in the counterexample model
  private readonly Type type;
  private bool haveExpanded;

  private bool nullable = false;
  public bool Nullable => nullable;

  public IEnumerable<Expression> Values(Dictionary<PartialValue, Expression> definitions) {
    if (!definitions.ContainsKey(this)) {
      yield break;
    }

    yield return definitions[this];
    foreach (var constraint in Constraints.OfType<DefinitionConstraint>().Where(definition => definition.definedValue == this)) {
      yield return constraint.AsExpression(definitions, false);
    }
  }

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
    relatedValues = new();
    haveExpanded = false;
    state.allPartialValues[element] = this;
    type = state.Model.GetFormattedDafnyType(element);
    AddConstraint(new TypeTestConstraint(this, type));
    state.Model.AddTypeConstraints(this);
  }

  public IEnumerable<PartialValue> GetRelatedValues() {
    if (haveExpanded) {
      foreach (var value in relatedValues) {
        yield return value;
      }
      yield break;
    }
    foreach (var value in state.Model.GetExpansion(state, this)) {
      if (!relatedValues.Contains(value)) {
        relatedValues.Add(value);
      }
      yield return value;
    }
    haveExpanded = true;
  }

  private void AddRelatedValuesConnections(List<PartialValue> involvedValues) {
    involvedValues.Add(this);
    for (int i = 0; i < involvedValues.Count; i++) {
      for (int j = 0; j < i; j++) {
        if (involvedValues[i] == involvedValues[j]) {
          continue;
        }
        if (!involvedValues[i].relatedValues.Contains(involvedValues[j])) {
          involvedValues[i].relatedValues.Add(involvedValues[j]);
        }
        if (!involvedValues[j].relatedValues.Contains(involvedValues[i])) {
          involvedValues[j].relatedValues.Add(involvedValues[i]);
        }
      }
    }
  }

  internal void AddConstraint(Constraint constraint) {
    Constraints.Add(constraint);
    AddRelatedValuesConnections(constraint.referencedValues);
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
    foreach (var relatedValue in relatedValues) {
      foreach (var memberSelectExpr in relatedValue.Constraints.OfType<MemberSelectExprConstraint>().Where(constraint => constraint.definedValue == relatedValue && constraint.Obj == this)) {
        fields[memberSelectExpr.MemberName] = relatedValue;
      }
    }
    return fields;
  }

  public IEnumerable<PartialValue> UnnamedDestructors() {
    var datatypeValue = Constraints.OfType<DatatypeValueConstraint>().FirstOrDefault(constraint => constraint.definedValue == this);
    if (datatypeValue != null) {
      foreach (var destructor in datatypeValue.UnnamedDestructors) {
        yield return destructor;
      }
    }
  }

  public IEnumerable<PartialValue> SetElements() {
    return Constraints.OfType<ContainmentConstraint>()
      .Where(containment => containment.set == this)
      .Select(containment => containment.element);
  }

  public string DatatypeConstructorName() {
    return Constraints.OfType<DatatypeConstructorCheckConstraint>()
      .Select(constructorCheck => constructorCheck.constructorName).FirstOrDefault() ?? "";
  }

  public Dictionary<PartialValue, PartialValue> Mappings = new(); // TODO

  public int? Cardinality(Dictionary<PartialValue, Expression> definitions) {
    if (Type is not SeqType or SetType or MapType) {
      return -1;
    }

    LiteralExpr cardinality = null;

    foreach (var relatedValue in relatedValues) {
      var relatedValueDescribesCardinality = false;
      foreach (var definition in relatedValue.Values(definitions)) {
        if (definition is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Cardinality } unaryOpExpr
            && unaryOpExpr.E == definitions[this]) {
          relatedValueDescribesCardinality = true;
          break;
        }
      }

      if (!relatedValueDescribesCardinality) {
        continue;
      }

      cardinality = relatedValue.Values(definitions).OfType<LiteralExpr>().First();
      break;
    }

    if (cardinality == null || cardinality.Value is not BigInteger bigInteger ||
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
          return seqSelectConstraint.definedValue;
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