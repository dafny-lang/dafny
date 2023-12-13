// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

public class PartialValue {

  public static string ElementNamePrefix = "$";
  public readonly IdentifierExpr ElementIdentifier;
  public readonly Model.Element Element; // the element in the counterexample model associated with the value
  public List<Constraint> constraints;
  private List<PartialValue> relatedValues;
  private readonly PartialState state; // corresponding state in the counterexample model
  private readonly Type type;
  private bool haveExpanded;
  private static Dictionary<PartialState, Dictionary<Model.Element, PartialValue>> allPartialValues = new();

  public IEnumerable<Expression> Values(Dictionary<PartialValue, Expression> definitions) {
    if (definitions.ContainsKey(this)) {
      yield break;
    }

    yield return definitions[this];
    foreach (var constraint in constraints) {
      if (constraint.definesValue == this) {
        yield return constraint.AsExpression(definitions, false);
      }
    }
  }

  internal static PartialValue Get(Model.Element element, PartialState state) {
    if (allPartialValues.ContainsKey(state) && allPartialValues[state].ContainsKey(element)) {
      return allPartialValues[state][element];
    }
    return new PartialValue(element, state);
  }

  internal static IEnumerable<PartialValue> AllPartialValuesForState(PartialState state) {
    if (!allPartialValues.ContainsKey(state)) {
      yield break;
    }
    foreach (var value in allPartialValues[state].Values) {
      yield return value;
    }
  }

  private PartialValue(Model.Element element, PartialState state) {
    Element = element;
    this.state = state;
    constraints = new();
    relatedValues = new();
    haveExpanded = false;
    if (!allPartialValues.ContainsKey(state)) {
      allPartialValues[state] = new();
    }
    allPartialValues[state][element] = this;
    type = state.Model.GetFormattedDafnyType(element);
    ElementIdentifier = new IdentifierExpr(Token.NoToken, ElementNamePrefix + Element.Id);
    ElementIdentifier.Type = type;
    AddConstraint(new TypeTestExpr(Token.NoToken, ElementIdentifier, type), new());
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

  internal void AddConstraint(Expression constrainingExpression, List<PartialValue> referencedValues) { 
    if (!referencedValues.Contains(this)) {
      referencedValues.Add(this);
    }
    var constraint = new Constraint(constrainingExpression, referencedValues);
    constraints.Add(constraint);
    AddRelatedValuesConnections(referencedValues);
  }
  
  internal void AddDefinition(Expression constrainingExpression, List<PartialValue> referencedValues) {
    constrainingExpression.Type = type;
    if (referencedValues.Contains(this)) {
      referencedValues.Remove(this);
    }
    var constraint = new Constraint(constrainingExpression, referencedValues, this);
    constraints.Add(constraint);
    AddRelatedValuesConnections(referencedValues);
  }
  
  internal void AddName(Expression constrainingExpression) {
    constrainingExpression.Type = type;
    var constraint = new Constraint(constrainingExpression, new List<PartialValue> {this}, this);
    constraints.Add(constraint);
  }

  public bool IsPrimitive => false; // TODO

  public string ShortName => ""; // TODO

  public Type Type => type;

  public string Value => ""; // TODO

  public Dictionary<string, List<PartialValue>> Children => new(); // TODO

  public string CanonicalName() => ""; // TODO

  public Dictionary<PartialValue, PartialValue> Mappings = new(); // TODO

  public int? Cardinality(Dictionary<PartialValue, Expression> definitions) {
    if (Type is not SeqType or SetType or MapType) {
      return -1;
    }

    LiteralExpr cardinality = null;
    foreach (var constraint in constraints.OfType<BinaryExpr>()
               .Where(binaryExpr => binaryExpr.Op == BinaryExpr.Opcode.Eq)) {
      if (constraint.E0 is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Cardinality } unaryOpExpr
          && constraint.E1 is LiteralExpr literalExpr
          && unaryOpExpr.E is IdentifierExpr identifierExpr 
          && identifierExpr.Name == ElementIdentifier.Name) {
        cardinality = literalExpr;
        break;
      }
    }

    if (cardinality == null) {
      foreach (var relatedValue in relatedValues) {
        var relatedValueDescribesCardinality = false;
        foreach (var definition in relatedValue.Values(definitions)) {
          if (definition is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Cardinality } unaryOpExpr
              && unaryOpExpr.E is IdentifierExpr identifierExpr 
              && identifierExpr.Name == ElementIdentifier.Name) {
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
    }

    if (cardinality == null || cardinality.Value is not BigInteger bigInteger || 
        !bigInteger.LessThanOrEquals(new BigInteger(int.MaxValue))) {
      return -1;
    }
    
    return (int) bigInteger;
  }


  public PartialValue this[int i] {
    get { throw new System.NotImplementedException(); } // TODO
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
    foreach (var constraint in constraints) {
      constraintsToPrint.Add(Printer.ExprToString(printOptions, constraint.rawExpression));
    }
    return string.Join(", ", constraintsToPrint);
  }
  
}