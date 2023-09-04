// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using Dafny;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration; 

public class PartialValue {

  public readonly Model.Element Element; // the element in the counterexample model associated with the value
  private HashSet<Expression> constraints; // constraints imposed on this value
  private Expression definition; // a deterministic expression that can be used to name this value
  private HashSet<Expression> synonyms;
  private readonly PartialState state; // corresponding state in the counterexample model
  private bool constraintsGathered;

  public bool HasDefinition => definition != null;

  internal PartialValue(Model.Element element, PartialState state, Expression definition=null) {
    Element = element;
    this.state = state;
    this.definition = definition; // TODO: what to do when definition is replaced?
    constraints = new();
    synonyms = new();
    constraintsGathered = false;
  }

  public IEnumerable<PartialValue> GetRelatedValues() {
    GatherConstraints();
    return Sequence<PartialValue>.Empty; // TODO
  }

  public void GatherConstraints() {
    if (constraintsGathered) {
      return;
    }
    // TODO
  }

  internal void AddDefinition(Expression definition, bool addAsSynonym=false) {
    if (!HasDefinition) {
      this.definition = definition;
    } else if (addAsSynonym) {
      synonyms.Add(definition);
    }
    constraints.Add(definition);
  }

  public bool IsPrimitive => false; // TODO

  public string ShortName => ""; // TODO

  public Type Type => Type.Int; // TODO

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
}