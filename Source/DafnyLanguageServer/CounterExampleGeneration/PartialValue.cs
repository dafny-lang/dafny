// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

public class PartialValue {

  public static readonly string ElementNamePrefix = "$";
  public readonly IdentifierExpr ElementIdentifier;
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
    foreach (var constraint in Constraints) {
      if (constraint.definesValue == this) {
        yield return constraint.AsExpression(definitions, false);
      }
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
    ElementIdentifier = new IdentifierExpr(Token.NoToken, ElementNamePrefix + Element.Id);
    ElementIdentifier.Type = type;
    AddConstraint(new TypeTestExpr(Token.NoToken, ElementIdentifier, type), new());
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

  internal Constraint AddConstraint(Expression constrainingExpression, List<PartialValue> referencedValues) {
    if (constrainingExpression is TypeTestExpr typeTestExpr && typeTestExpr.ToType is UserDefinedType userDefinedType && userDefinedType.Name.EndsWith("?")) {
      nullable = true;
    }
    if (!referencedValues.Contains(this)) {
      referencedValues.Add(this);
    }
    constrainingExpression.Type = Type.Bool;
    var constraint = new Constraint(constrainingExpression, referencedValues, new List<Constraint>());
    Constraints.Add(constraint);
    AddRelatedValuesConnections(referencedValues);
    return constraint;
  }

  internal void AddDefinition(Expression constrainingExpression, List<PartialValue> referencedValues, List<Constraint> antecedents) {
    constrainingExpression.Type = type;
    if (referencedValues.Contains(this)) {
      referencedValues.Remove(this);
    }
    var constraint = new Constraint(constrainingExpression, referencedValues, antecedents, this);
    Constraints.Add(constraint);
    AddRelatedValuesConnections(referencedValues);
  }

  internal void AddName(Expression constrainingExpression) {
    constrainingExpression.Type = type;
    var constraint = new Constraint(constrainingExpression, new List<PartialValue> { this }, new List<Constraint>(), this);
    Constraints.Add(constraint);
  }

  public string ShortName => ""; // TODO

  public Type Type => type;

  public string PrimitiveLiteral {
    get {
      var literalValue = Constraints.FirstOrDefault(constraint =>
        constraint.definesValue == this && constraint.rawExpression is LiteralExpr, null);
      if (literalValue != null) {
        return literalValue.ToString();
      }

      return "";
    }
  }

  public Dictionary<string, PartialValue> Fields() {
    var fields = new Dictionary<string, PartialValue>();
    foreach (var relatedValue in relatedValues) {
      foreach (var definition in relatedValue.Constraints.Where(constraint => constraint.definesValue == relatedValue)) {
        if (definition.rawExpression is MemberSelectExpr memberSelectExpr &&
            memberSelectExpr.Obj.ToString() == ElementIdentifier.ToString()) {
          fields[memberSelectExpr.MemberName] = relatedValue;
        }
      }
    }
    return fields;
  }

  public IEnumerable<PartialValue> UnnamedDestructors() {
    foreach (var constraint in Constraints.Where(constraint => constraint.definesValue == this)) {
      if (constraint.rawExpression is DatatypeValue datatypeValue) {
        foreach (var argument in constraint.ReferencedValues) {
          if (argument != this) {
            yield return argument;
          }
        }
      }
    }
    yield break;
  }

  public IEnumerable<PartialValue> SetElements() {
    foreach (var constraint in Constraints) {
      if (constraint.rawExpression is BinaryExpr binaryExpr && binaryExpr.Op is BinaryExpr.Opcode.In) {
        foreach (var relatedValue in relatedValues) {
          if (relatedValue.ElementIdentifier.ToString() == binaryExpr.E0.ToString()) {
            yield return relatedValue;
          }
        }
      }
    }
  }

  public string DatatypeConstructorName {
    get {
      foreach (var constraint in Constraints) {
        if (constraint.rawExpression is MemberSelectExpr memberSelectExpr &&
            memberSelectExpr.MemberName.EndsWith("?")) {
          return memberSelectExpr.MemberName[..^1];
        }
      }
      return "";
    }
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
      PartialValue index = null;
      foreach (var relatedValue in relatedValues) {
        if (relatedValue.PrimitiveLiteral == i.ToString()) {
          index = relatedValue;
          break;
        }
      }

      if (index == null) {
        return null;
      }

      foreach (var relatedValue in relatedValues) {
        foreach (var constraint in relatedValue.Constraints) {
          if (constraint.definesValue == relatedValue
              && constraint.rawExpression is SeqSelectExpr seqSelectExpr
              && seqSelectExpr.Seq.ToString() == ElementIdentifier.ToString()
              && seqSelectExpr.E0.ToString() == index.ElementIdentifier.ToString()) {
            return relatedValue;
          }
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

  public override string ToString() {
    var printOptions = DafnyOptions.Default;
    var constraintsToPrint = new List<string>();
    foreach (var constraint in Constraints) {
      constraintsToPrint.Add(Printer.ExprToString(printOptions, constraint.rawExpression));
    }
    return string.Join(", ", constraintsToPrint);
  }

}