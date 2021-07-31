// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
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
    // This dictionary associates a child name with resp. variable:
    // several children can have same names (particularly, sets can have
    // many children called true and falls)
    private readonly Dictionary<string, HashSet<DafnyModelVariable>> children; 

    /// <summary>
    /// Create a new variable to be associated with the given model element in
    /// a given counterexample state or return such a variable if one already
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
        if (!duplicate) {
          return state.GetVar(element);
        }
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
        string result = state.Model.CanonicalName(Element, state);
        if (children.Count == 0)
          return result == "" ? "()" : result;
        List<Tuple<string, string>> childList = new();
        foreach (var childName in children.Keys) {
          foreach (var child in children[childName]) {
            if (child.IsPrimitive) {
              childList.Add(new Tuple<string, string>(childName, child.Value));
            } else {
              childList.Add(new Tuple<string, string>(childName, child.ShortName));
            }
          }
        }
        string childValues;
        if (Type.StartsWith("set<")) {
          childValues = string.Join(", ",
            childList.ConvertAll(tpl => tpl.Item2 + " => " + tpl.Item1));
        } else {
          childValues = string.Join(", ",
            childList.ConvertAll(tpl => tpl.Item1 + " => " + tpl.Item2));
        }
        return result + "(" + childValues + ")";
      }
    }

    public bool IsPrimitive => DafnyModel.IsPrimitive(Element, state);
    
    public string ShortName => Regex.Replace(Name, @"#\d+$", "");
    
    private void AddChild(string name, DafnyModelVariable child) {
      if (!children.ContainsKey(name)) {
        children[name] = new();
      }
      children[name].Add(child);
    }

    public override int GetHashCode() {
      return Element.Id;
    }

    public override bool Equals(object? obj) {
      if (obj is not DafnyModelVariable other)
        return false;
      return other.Element == Element && other.state == state && other.Name == Name;
    }
  }
}