// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration; 

public class PartialValue {

  public readonly Model.Element Element; // the element in the counterexample model associated with the value
  public HashSet<Expression> constraints; // constraints imposed on this value
  public Expression definition;
  private HashSet<PartialValue> relatedValues;
  private readonly PartialState state; // corresponding state in the counterexample model
  private readonly Type type;

  internal PartialValue(Model.Element element, PartialState state) {
    Element = element;
    this.state = state;
    type = state.Model.GetDafnyType(element);
    constraints = new();
    definition = new IdentifierExpr(Token.NoToken, Element.ToString());
    relatedValues = null;
  }

  public IEnumerable<PartialValue> GetRelatedValues() {
    if (relatedValues != null) {
      foreach (var value in relatedValues) {
        yield return value;
      }
      yield break;
    }
    relatedValues = new HashSet<PartialValue>();
    foreach (var value in state.Model.GetExpansion(state, this)) {
      relatedValues.Add(value);
      yield return value;
    }
  }

  internal void AddConstraint(Expression constraint) { 
    constraints.Add(constraint);
  }
  
  internal void AddDefinition(Expression definition) {
    if (this.definition is IdentifierExpr expr && expr.Name == Element.ToString()) {
      this.definition = definition;
      HashSet<Expression> newConstraints = new();
      var substituter = new DefinitionSubstituter(expr.Name, definition);
      foreach (var constraint in constraints) {
        newConstraints.Add(substituter.CloneExpr(constraint));
      }
      constraints = newConstraints;
      return;
    }
    constraints.Add(new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, definition, this.definition));
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

  public void AddAtIndex(object p0, string idx) {
    throw new System.NotImplementedException();
  }

  public void SetLength(object length) {
    throw new System.NotImplementedException();
  }

  public void AddMapping(object key, object p1) {
    throw new System.NotImplementedException();
  }

  public override bool Equals(object obj) {
    return obj is PartialValue other && other.Element == Element && other.state == state;
  }

  public override int GetHashCode() {
    return Element.GetHashCode();
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
      return base.CloneExpr(expr);
    }
  }
}