// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable

using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

/// <summary>
/// Each PartialValue corresponds to an Element in the counterexample model returned by Boogie and represents a
/// Dafny value about which we might have limited information (e.g. a sequence of which we only know one element)
/// </summary>
public class PartialValue {

  public readonly Model.Element Element; // the element in the counterexample model associated with the value
  public readonly List<Constraint> Constraints; // constraints describing this value
  public readonly PartialState state; // corresponding state in the counterexample model
  private readonly Type type; // Dafny type associated with the value
  private bool haveExpanded;

  /// <summary>
  /// This factory method ensures we don't create duplicate partial value objects for the same element and state in the
  /// counterexample model
  /// </summary>
  public static PartialValue Get(Model.Element element, PartialState state) {
    if (state.AllPartialValues.TryGetValue(element, out var value)) {
      return value;
    }

    return new PartialValue(element, state);
  }

  private PartialValue(Model.Element element, PartialState state) {
    Element = element;
    this.state = state;
    Constraints = [];
    haveExpanded = false;
    state.AllPartialValues[element] = this;
    type = state.Model.GetFormattedDafnyType(element);
    var _ = new TypeTestConstraint(this, type);
    state.Model.AddTypeConstraints(this);
  }

  /// <summary>
  /// Return all partial values that appear in any of the constraints describing this element
  /// </summary>
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

  public bool Nullable => Constraints.OfType<TypeTestConstraint>()
    .Any(test => test.Type is UserDefinedType userDefinedType && userDefinedType.Name.EndsWith("?"));

  public Type Type => type;

  public string PrimitiveLiteral {
    get {
      return Constraints.OfType<LiteralExprConstraint>()
        .Select(literal => literal.LiteralExpr.ToString()).FirstOrDefault() ?? "";
    }
  }

  public Dictionary<string, PartialValue> Fields() {
    var fields = new Dictionary<string, PartialValue>();
    foreach (var memberSelectExpr in Constraints.OfType<MemberSelectExprConstraint>()
               .Where(constraint => Equals(constraint.Obj, this))) {
      fields[memberSelectExpr.MemberName] = memberSelectExpr.DefinedValue;
    }

    return fields;
  }

  public IEnumerable<PartialValue> UnnamedDestructors() {
    var datatypeValue = Constraints.OfType<DatatypeValueConstraint>()
      .FirstOrDefault(constraint => Equals(constraint.DefinedValue, this));
    if (datatypeValue != null) {
      foreach (var destructor in datatypeValue.UnnamedDestructors) {
        yield return destructor;
      }
    }
  }

  public IEnumerable<PartialValue> SetElements() {
    return Constraints.OfType<ContainmentConstraint>()
      .Where(containment => Equals(containment.Set, this))
      .Select(containment => containment.Element);
  }

  public string DatatypeConstructorName() {
    return Constraints.OfType<DatatypeConstructorCheckConstraint>()
      .Select(constructorCheck => constructorCheck.ConstructorName).FirstOrDefault() ?? "";
  }

  public IEnumerable<(PartialValue Key, PartialValue Value)> Mappings() {
    foreach (var mapping in Constraints.OfType<MapSelectExprConstraint>().Where(constraint => Equals(constraint.Map, this))) {
      yield return new(mapping.Key, mapping.DefinedValue);
    }
  }

  public int? Cardinality() {
    if (Constraints.OfType<LiteralExprConstraint>().Any(constraint =>
          (constraint.LiteralExpr is DisplayExpression displayExpression && !displayExpression.SubExpressions.Any()) ||
          (constraint.LiteralExpr is MapDisplayExpr mapDisplayExpr && !mapDisplayExpr.Elements.Any()))) {
      return 0;
    }

    var cardinality = Constraints.OfType<CardinalityConstraint>()
      .FirstOrDefault(constraint => Equals(constraint.Collection, this))?.DefinedValue;
    if (cardinality == null) {
      return -1;
    }

    var cardinalityLiteral =
      cardinality.Constraints.OfType<LiteralExprConstraint>().FirstOrDefault()?.LiteralExpr as LiteralExpr;
    if (cardinalityLiteral == null) {
      return -1;
    }

    if (cardinalityLiteral.Value is not BigInteger bigInteger ||
        !bigInteger.LessThanOrEquals(new BigInteger(int.MaxValue))) {
      return -1;
    }

    return (int)bigInteger;
  }


  public PartialValue? this[int i] {
    get {
      foreach (var seqSelectConstraint in Constraints.OfType<SeqSelectExprWithLiteralConstraint>()
                 .Where(constraint => Equals(constraint.Seq, this))) {
        if (seqSelectConstraint.Index.ToString() == i.ToString()) {
          return seqSelectConstraint.DefinedValue;
        }
      }

      foreach (var seqSelectConstraint in Constraints.OfType<SeqSelectExprConstraint>()
                 .Where(constraint => Equals(constraint.Seq, this))) {
        var indexLiteral = seqSelectConstraint.Index.Constraints.OfType<LiteralExprConstraint>().FirstOrDefault()
          ?.LiteralExpr;
        if (indexLiteral != null && indexLiteral.ToString() == i.ToString()) {
          return seqSelectConstraint.DefinedValue;
        }
      }

      return null;
    }
  }

  public override bool Equals(object? obj) {
    return obj is PartialValue other && other.Element == Element && other.state == state;
  }

  public override int GetHashCode() {
    return Element.GetHashCode();
  }

}