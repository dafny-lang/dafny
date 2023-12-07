// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration; 

public class PartialValue {

  private static string ElementNamePrefix = "$";
  private static ExpressionAnalyzer analyzer = new();
  public readonly Model.Element Element; // the element in the counterexample model associated with the value
  public HashSet<Expression> constraints; // constraints imposed on this value
  public IEnumerable<Expression> ResolvableConstraints =>
    constraints.Where(constraint => analyzer.AllTypesAreKnown(constraint));
  public Expression definition;
  public HashSet<Expression> potentialDefinitions;
  private HashSet<PartialValue> relatedValues;
  private readonly PartialState state; // corresponding state in the counterexample model
  private readonly Type type;
  private bool haveExpanded;
  private string ElementName => ElementNamePrefix + Element.Id;
  private static Dictionary<PartialState, Dictionary<Model.Element, PartialValue>> allPartialValues = new();
  public bool HasCompleteDefinition => analyzer.DefinitionIsComplete(definition);

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
    type = state.Model.GetFormattedDafnyType(element);
    constraints = new();
    definition = new IdentifierExpr(Token.NoToken, ElementName);
    definition.Type = type;
    // TODO: do not add the constraint if the type cannot be fully reconstructed
    constraints.Add(new TypeTestExpr(Token.NoToken, definition, type));
    potentialDefinitions = new();
    relatedValues = new HashSet<PartialValue>();
    haveExpanded = false;
    if (!allPartialValues.ContainsKey(state)) {
      allPartialValues[state] = new();
    }
    allPartialValues[state][element] = this;
  }

  public IEnumerable<PartialValue> GetRelatedValues() {
    if (haveExpanded) {
      foreach (var value in relatedValues) {
        yield return value;
      }
      yield break;
    }
    foreach (var value in state.Model.GetExpansion(state, this)) {
      relatedValues.Add(value);
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
        involvedValues[i].relatedValues.Add(involvedValues[j]);
        involvedValues[j].relatedValues.Add(involvedValues[i]);
      }
    }
  }

  internal void AddConstraint(Expression constraint, List<PartialValue> involvedValues) { 
    constraint.Type = Type.Bool;
    constraints.Add(constraint);
    AddRelatedValuesConnections(involvedValues);
  }

  private void PropagateRelatedDefinition(PartialValue updatedValue) {
    var newConstraints = new HashSet<Expression>();
    var newPotentialDefinitions = new HashSet<Expression>();
    var substituter = new DefinitionSubstituter(updatedValue.ElementName, updatedValue.definition);
    foreach (var constraint in constraints) {
      newConstraints.Add(substituter.CloneExpr(constraint));
    }
    Expression newDefinition = null;
    foreach (var constraint in potentialDefinitions) {
      var newPotentialDefinition = substituter.CloneExpr(constraint);
      newPotentialDefinitions.Add(newPotentialDefinition);
      if (analyzer.DefinitionIsComplete(newPotentialDefinition)) {
        newDefinition = newPotentialDefinition;
      }
    }
    constraints = newConstraints;
    potentialDefinitions = newPotentialDefinitions;
    if (newDefinition != null) {
      potentialDefinitions.Remove(newDefinition);
      SetDefinition(newDefinition);
    }
  }

  private void SetDefinition(Expression definition) {
    this.definition = definition;
    HashSet<Expression> newConstraints = new();
    var substituter = new DefinitionSubstituter(ElementName, definition);
    foreach (var constraint in constraints) {
      newConstraints.Add(substituter.CloneExpr(constraint));
    }
    foreach (var notADefinition in potentialDefinitions) {
      newConstraints.Add(new BinaryExpr(
        Token.NoToken, 
        BinaryExpr.Opcode.Eq, 
        definition, 
        substituter.CloneExpr(notADefinition)));
    }
    potentialDefinitions = new HashSet<Expression>();
    constraints = newConstraints;
    foreach (var relatedValue in relatedValues) {
      relatedValue.PropagateRelatedDefinition(this);
    }
  }
  
  internal void AddDefinition(Expression definition, List<PartialValue> involvedValues) {
    definition.Type = Type;
    AddRelatedValuesConnections(involvedValues);
    var newDefinitionIsComplete = analyzer.DefinitionIsComplete(definition);
    var currentDefinitionIsComplete = analyzer.DefinitionIsComplete(this.definition);
    if (currentDefinitionIsComplete) {
      constraints.Add(new BinaryExpr(
        Token.NoToken, 
        BinaryExpr.Opcode.Eq,
        this.definition,
        definition));
      return;
    }
    if (!newDefinitionIsComplete) {
      potentialDefinitions.Add(definition);
      return;
    } 
    SetDefinition(definition);
  }

  public bool IsPrimitive => false; // TODO

  public string ShortName => ""; // TODO

  public Type Type => type;

  public string Value => ""; // TODO

  public Dictionary<string, List<PartialValue>> Children => new(); // TODO

  public string CanonicalName() => ""; // TODO

  public Dictionary<PartialValue, PartialValue> Mappings = new(); // TODO

  public int GetLength() => 0; // TODO


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
    foreach (var potentialDefinition in potentialDefinitions) {
      constraintsToPrint.Add(Printer.ExprToString(printOptions, new BinaryExpr(Token.NoToken,  BinaryExpr.Opcode.Eq, definition, potentialDefinition)));
    }
    foreach (var constraint in constraints) {
      constraintsToPrint.Add(Printer.ExprToString(printOptions, constraint));
    }
    return Printer.ExprToString(printOptions, definition) + " : " + string.Join(", ", constraintsToPrint);
  }


  private class DefinitionSubstituter : Cloner {

    private string name;
    private Expression definition;

    public DefinitionSubstituter(string name, Expression definition) {
      this.name = name;
      this.definition = definition;
    }
    public override Expression CloneExpr(Expression expr) {
      if (expr is IdentifierExpr identifierExpr && identifierExpr.Name == name) {
        return definition;
      }
      var result = base.CloneExpr(expr);
      if (result is DatatypeValue datatypeValue) {
        datatypeValue.Bindings.AcceptArgumentExpressionsAsExactParameterList();
      }
      return result;
    }
  }

  private class ExpressionAnalyzer : Cloner {

    private bool definitionComplete = true;
    private bool allTypesAreKnown = true;

    public bool DefinitionIsComplete(Expression definition) {
      definitionComplete = true;
      CloneExpr(definition);
      return definitionComplete;
    }

    public bool AllTypesAreKnown(Expression constraint) {
      allTypesAreKnown = true;
      CloneExpr(constraint);
      return allTypesAreKnown;
    }

    public override Expression CloneExpr(Expression expr) {
      if (expr is IdentifierExpr identifierExpr && identifierExpr.Name.StartsWith(ElementNamePrefix)) {
        definitionComplete = false;
      }

      return base.CloneExpr(expr);
    }

    public override Type CloneType(Type typ) {
      if (typ is UserDefinedType userDefinedType && userDefinedType.Name == DafnyModel.UnknownType.Name) {
        allTypesAreKnown = false;
      }

      return base.CloneType(typ);
    }
  }
}