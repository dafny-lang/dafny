// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace DafnyServer.CounterExampleGeneration {
  
  public class DafnyModelVariable {
    
    public readonly string Name; // name given to the variable at creation
    public readonly string Type; // Dafny type of the variable
    internal readonly Model.Element Element;
    private readonly DafnyModelState state; // the associated captured state
    // A child is a field or a value at a given index of an array, etc.
    // This dictionary maps the name of the child or field to resp. variable:
    private readonly Dictionary<string, DafnyModelVariable> children; 

    /// <summary>
    /// Creates a new variable to be associated with the given model element in
    /// a given counterexample state or returns such a variable if one already
    /// exists.
    /// </summary>
    /// <param name="state"></param>
    /// <param name="element"></param>
    /// <param name="name">the name to be assigned to the variable OR,
    /// if parent != null, the name of the field associated with it. In the later
    /// case, Name is set to some unique id.</param>
    /// <param name="parent">if not null, this variable represents the field of
    /// some parent object</param>
    /// <param name="duplicate">forces the creation of a new variable even if
    /// one already exists </param>
    /// <returns></returns>
    public static DafnyModelVariable Get(DafnyModelState state, 
      Model.Element element, string name, DafnyModelVariable parent=null, 
      bool duplicate=false) {
      if (state.ExistsVar(element)) {
        parent?.AddChild(name, state.GetVar(element));
        if (!duplicate)
          return state.GetVar(element);
      }
      return new(state, element, name, parent);
    }

    private DafnyModelVariable(DafnyModelState state, Model.Element element, 
      string name, DafnyModelVariable parent) {
      this.state = state;
      Element = element;
      Type = state.Model.GetDafnyType(element);
      children = new();
      state.AddVar(element, this);
      if (parent == null) {
        Name = name;
        return;
      }
      Name = "@" + state.VarIndex++;
      parent.AddChild(name, this);
    }

    public IEnumerable<DafnyModelVariable> GetExpansion() {
      return state.Model.GetExpansion(state, this);
    }

    public string Value {
      get {
        string result = state.Model.CanonicalName(Element);
        foreach (var key in children.Keys) {
          if (children[key].IsPrimitive)
            result += ", " + ShortName + key + "=" + children[key].Value;
          else
            result += ", " + ShortName + key + "=" + children[key].ShortName;
        }
        return result;
      }
    }

    public bool IsPrimitive => DafnyModel.IsPrimitive(Element, state);
    
    public string ShortName => Regex.Replace(Name, @"#\d+$", "");
    
    private void AddChild(string name, DafnyModelVariable child) {
      children[name] = child;
    }
  }
}