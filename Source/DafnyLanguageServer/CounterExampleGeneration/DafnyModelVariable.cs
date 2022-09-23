// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable disable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration {

  /// <summary>
  /// A static class for generating instance of DafnyModelvariable and its
  /// subclasses. The factory chooses which subclass of DafnyModelVariable to
  /// employ depending on the DafnyModelType` of the `Element` for which the
  /// variable is generated.
  /// </summary>
  public static class DafnyModelVariableFactory {

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
      Model.Element element, string name, DafnyModelVariable parent = null,
      bool duplicate = false) {
      if (state.ExistsVar(element)) {
        parent?.AddChild(name, state.GetVar(element));
        if (!duplicate) {
          return state.GetVar(element);
        }
        return new DuplicateVariable(state, state.GetVar(element), name, parent);
      }

      return state.Model.GetDafnyType(element) switch {
        SeqType _ => new SeqVariable(state, element, name, parent),
        MapType _ => new MapVariable(state, element, name, parent),
        _ => new DafnyModelVariable(state, element, name, parent)
      };
    }
  }

  /// <summary>
  /// Represents a variable at a particular state. Note that a variable in Dafny
  /// source can be represented by multiple DafnyModelVariables, one for each
  /// DafnyModelState in DafnyModel.
  /// </summary>
  public class DafnyModelVariable {

    public readonly string Name; // name given to the variable at creation
    public readonly Microsoft.Dafny.Type Type; // Dafny type of the variable
    public readonly Model.Element Element;
    // Maps a field name, sequence index, or some other identifier to
    // a list of DafnyModelVariables that represent the corresponding value
    private readonly Dictionary<string, List<DafnyModelVariable>> children;
    private readonly DafnyModelState state; // the associated captured state
    public virtual Dictionary<string, List<DafnyModelVariable>> Children => children;

    internal DafnyModelVariable(DafnyModelState state, Model.Element element,
      string name, DafnyModelVariable parent) {
      this.state = state;
      Element = element;
      Type = state.Model.GetDafnyType(element);
      children = new Dictionary<string, List<DafnyModelVariable>>();
      state.AddVar(element, this);
      if (parent == null) {
        Name = name;
      } else {
        Name = "@" + state.VarIndex++;
        parent.AddChild(name, this);
      }
      state.AddVarName(ShortName);
    }

    public virtual IEnumerable<DafnyModelVariable> GetExpansion() {
      return state.Model.GetExpansion(state, this);
    }

    public string CanonicalName() {
      return state.Model.CanonicalName(Element);
    }

    public virtual string Value {
      get {
        var result = state.Model.CanonicalName(Element);
        if (children.Count == 0) {
          return result == "" ? "()" : result;
        }

        List<(string ChildName, string ChildValue)> childList = new();
        foreach (var childName in children.Keys) {
          foreach (var child in children[childName]) {
            if (child.IsPrimitive) {
              childList.Add(new ValueTuple<string, string>(childName, child.Value));
            } else {
              childList.Add(new ValueTuple<string, string>(childName, child.ShortName));
            }
          }
        }
        string childValues;
        if (Type is SetType) {
          childValues = string.Join(", ",
            childList.ConvertAll(tpl => tpl.Item2 + " := " + tpl.Item1));
          return result + "{" + childValues + "}";
        }
        childValues = string.Join(", ",
            childList.ConvertAll(tpl => tpl.Item1 + " := " + tpl.Item2));
        return result + "(" + childValues + ")";
      }
    }

    public bool IsPrimitive => DafnyModel.IsPrimitive(Element, state);

    public string ShortName {
      get {
        var shortName = Regex.Replace(Name, @"#.*$", "");
        return state.VarNameIsShared(shortName) ? Name : shortName;
      }
    }

    internal void AddChild(string name, DafnyModelVariable child) {
      if (!children.ContainsKey(name)) {
        children[name] = new();
      }
      children[name].Add(child);
    }

    public override int GetHashCode() {
      return Element.Id.GetHashCode();
    }

    public override bool Equals(object obj) {
      if (obj is not DafnyModelVariable other) {
        return false;
      }

      return other.Element == Element &&
             other.state == state &&
             other.Name == Name;
    }
  }

  /// <summary>
  /// a variable that has a different name but represents the same Element in
  /// the same DafnyModelState as some other variable.
  /// </summary>
  public class DuplicateVariable : DafnyModelVariable {

    public readonly DafnyModelVariable Original;

    internal DuplicateVariable(DafnyModelState state,
      DafnyModelVariable original, string newName, DafnyModelVariable parent)
      : base(state, original.Element, newName, parent) {
      Original = original;
    }

    public override string Value => Original.ShortName;

    public override Dictionary<string, List<DafnyModelVariable>> Children => Original.Children;

    public override IEnumerable<DafnyModelVariable> GetExpansion() {
      return Original.GetExpansion();
    }
  }

  /// <summary>
  /// A variable that represents a sequence. 
  /// </summary>
  public class SeqVariable : DafnyModelVariable {

    private DafnyModelVariable seqLength;
    // Dafny integers are unbounded, hence using strings for seq indices:
    private readonly Dictionary<string, DafnyModelVariable> seqElements;

    internal SeqVariable(DafnyModelState state, Model.Element element,
      string name, DafnyModelVariable parent)
      : base(state, element, name, parent) {
      seqLength = null;
      seqElements = new Dictionary<string, DafnyModelVariable>();
    }

    public override string Value {
      get {
        var length = GetLength();
        if (length == -1 || seqElements.Count != length) {
          return base.Value;
        }
        List<string> result = new();
        for (int i = 0; i < length; i++) {
          var id = i.ToString();
          if (!seqElements.ContainsKey(id)) {
            return base.Value;
          }
          result.Add(seqElements[id].IsPrimitive ?
            seqElements[id].Value :
            seqElements[id].ShortName);
        }
        return "[" + string.Join(", ", result) + "]";
      }
    }

    public int GetLength() {
      if (int.TryParse((seqLength?.Element as Model.Integer)?.Numeral,
            out var value)) {
        return value;
      }
      return -1;
    }

    public DafnyModelVariable this[int index] => seqElements.GetValueOrDefault(index.ToString(), null);

    public void SetLength(DafnyModelVariable seqLength) {
      this.seqLength = seqLength;
    }

    public void AddAtIndex(DafnyModelVariable e, string index) {
      if (index == null) {
        return;
      }
      seqElements[index] = e;
    }
  }

  /// <summary>
  /// A variable that represents a map.
  /// </summary>
  public class MapVariable : DafnyModelVariable {

    public readonly Dictionary<DafnyModelVariable, DafnyModelVariable>
      Mappings = new();

    internal MapVariable(DafnyModelState state, Model.Element element,
      string name, DafnyModelVariable parent)
      : base(state, element, name, parent) { }

    public override string Value {
      get {
        if (Mappings.Count == 0) {
          return "()";
        }
        // maps a key-value pair to how many times it appears in the map
        // a key value pair can appear many times in a map due to "?:int" etc.
        Dictionary<string, int> mapStrings = new();
        foreach (var key in Mappings.Keys) {
          var keyString = key.IsPrimitive ? key.Value : key.Name;
          var valueString = "?";
          if (Mappings[key] != null) {
            valueString = Mappings[key].IsPrimitive
              ? Mappings[key].Value
              : Mappings[key].Name;
          }
          var mapString = keyString + " := " + valueString;
          mapStrings[mapString] =
            mapStrings.GetValueOrDefault(mapString, 0) + 1;
        }

        return "(" + string.Join(", ", mapStrings.Keys.ToList()
                 .ConvertAll(keyValuePair =>
                   mapStrings[keyValuePair] == 1
                     ? keyValuePair
                     : keyValuePair + " [+" + (mapStrings[keyValuePair] - 1) +
                       "]")) +
               ")";
      }
    }

    public void AddMapping(DafnyModelVariable from, DafnyModelVariable to) {
      if (Mappings.ContainsKey(from)) {
        return;
      }
      Mappings[from] = to;
    }
  }
}