using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

public class Constraint {

  private static ExpressionAnalyzer analyzer = new();
  internal Expression rawExpression;
  private List<PartialValue> referencedValues;
  private List<Constraint> antecedents; // these constraints should go prior to this one to guarantee well-formedness
  public IEnumerable<PartialValue> ReferencedValues => referencedValues.AsEnumerable();
  public readonly PartialValue? definesValue;

  public bool IsIdentifier => rawExpression is IdentifierExpr;

  public Constraint(Expression expression, IEnumerable<PartialValue> referencedValues, IEnumerable<Constraint> antecedents, PartialValue? definesValue = null) {
    this.rawExpression = expression;
    this.referencedValues = referencedValues.ToList();
    this.definesValue = definesValue;
    this.antecedents = antecedents.ToList();
  }

  public Expression? AsExpression(Dictionary<PartialValue, Expression> definitions, bool wrapDefinitions) {
    if (!analyzer.AllTypesAreKnown(rawExpression)) {
      return null;
    }
    var newExpression = new DefinitionSubstituter(definitions).CloneExpr(rawExpression);
    if (!analyzer.DefinitionIsComplete(newExpression)) {
      return null;
    }
    if (definesValue == null) {
      return newExpression;
    }

    if (!definitions.TryGetValue(definesValue, out var valueDefinition) ||
        valueDefinition.ToString() == newExpression.ToString()) {
      return null;
    }

    if (!wrapDefinitions) {
      return newExpression;
    }
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, valueDefinition, newExpression);
  }

  public static void FindDefinitions(Dictionary<PartialValue, Expression> knownDefinitions, List<Constraint> constraints, bool allowNewIdentifiers) {
    var foundANewDefinition = true;
    var substituter = new DefinitionSubstituter(knownDefinitions);
    var oldConstraints = new List<Constraint>();
    oldConstraints.AddRange(constraints);
    constraints.Clear();
    while (foundANewDefinition) {
      foundANewDefinition = false;
      foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || !constraint.IsIdentifier)) {
        if (!constraints.Contains(constraint) && constraint.definesValue == null && constraint.ReferencedValues.All(value => knownDefinitions.ContainsKey(value))) {
          constraints.Add(constraint);
          foundANewDefinition = true;
          break;
        }
      }
      foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || !constraint.IsIdentifier)) { // First add as constraints the literal expressions
        if (constraint.definesValue != null && !knownDefinitions.ContainsKey(constraint.definesValue) &&
            constraint.ReferencedValues.Count() == 0 && constraint.antecedents.All(constraints.Contains)) {
          constraints.Add(constraint);
          var definition = substituter.CloneExpr(constraint.rawExpression);
          definition.Type = constraint.rawExpression.Type;
          knownDefinitions[constraint.definesValue] = definition;
          substituter.AddSubstitution(constraint.definesValue, definition);
          foundANewDefinition = true;
          break;
        }
      }
      if (foundANewDefinition) { continue; }
      foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || !constraint.IsIdentifier)) {
        if (constraint.definesValue != null && !knownDefinitions.ContainsKey(constraint.definesValue) &&
            constraint.ReferencedValues.All(value => knownDefinitions.ContainsKey(value)) && constraint.ReferencedValues.Count() > 0
            && constraint.antecedents.All(constraints.Contains)) {
          constraints.Add(constraint);
          var definition = substituter.CloneExpr(constraint.rawExpression);
          definition.Type = constraint.rawExpression.Type;
          knownDefinitions[constraint.definesValue] = definition;
          substituter.AddSubstitution(constraint.definesValue, definition);
          foundANewDefinition = true;
          break;
        }
      }
    }
    foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || !constraint.IsIdentifier)) {
      if (!constraints.Contains(constraint) && constraint.definesValue == null) {
        constraints.Add(constraint);
      }
    }
    foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || !constraint.IsIdentifier)) {
      if (!constraints.Contains(constraint) && constraint.definesValue != null) {
        constraints.Add(constraint);
      }
    }
  }

  public override string ToString() {
    return Printer.ExprToString(DafnyOptions.Default, rawExpression);
  }

  private class DefinitionSubstituter : Cloner {

    private Dictionary<string, Expression> substMap;

    public DefinitionSubstituter(Dictionary<PartialValue, Expression> substMap) {
      this.substMap = new Dictionary<string, Expression>();
      foreach (var partialValue in substMap.Keys) {
        this.substMap[partialValue.ElementIdentifier.Name] = substMap[partialValue];
      }
    }

    public void AddSubstitution(PartialValue key, Expression value) {
      substMap[key.ElementIdentifier.Name] = value;
    }
    public override Expression CloneExpr(Expression expr) {
      if (expr is IdentifierExpr identifierExpr && substMap.TryGetValue(identifierExpr.Name, out var cloneExpr)) {
        return cloneExpr;
      }
      if (expr is IdentifierExpr identifierExpr2 && identifierExpr2.Name.StartsWith(PartialValue.ElementNamePrefix)) {
        return expr;
      }
      var result = base.CloneExpr(expr);
      if (result is DatatypeValue datatypeValue) {
        datatypeValue.Bindings.AcceptArgumentExpressionsAsExactParameterList();
      }

      if (expr != null && expr.Type != null) {
        result.Type = expr.Type;
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
      if (expr is IdentifierExpr identifierExpr && identifierExpr.Name.StartsWith(PartialValue.ElementNamePrefix)) {
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