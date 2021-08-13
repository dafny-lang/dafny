// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace DafnyServer.CounterExampleGeneration {

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
      Model.Element element, string name, DafnyModelVariable parent=null, 
      bool duplicate=false) {
      if (state.ExistsVar(element)) {
        parent?.AddChild(name, state.GetVar(element));
        if (!duplicate) {
          return state.GetVar(element);
        }
        return new DuplicateVariable(state, state.GetVar(element), name, parent);
      }
      if (state.Model.GetDafnyType(element).Name == "seq") {
        return new SeqVariable(state, element, name, parent);
      }
      if (state.Model.GetDafnyType(element).Name == "map") {
        return new MapVariable(state, element, name, parent);
      }
      return new DafnyModelVariable(state, element, name, parent);
    }
  }
  
  public class DafnyModelVariable {
    
    public readonly string Name; // name given to the variable at creation
    public readonly DafnyModelType Type; // Dafny type of the variable
    public readonly Model.Element Element;
    private readonly DafnyModelState state; // the associated captured state
    // A child is a field or a value at a given index of an array, etc.
    // This dictionary associates a child name with resp. variable:
    // several children can have same names (particularly, sets can have
    // many children called true and falls)
    public readonly Dictionary<string, HashSet<DafnyModelVariable>> children;

    internal DafnyModelVariable(DafnyModelState state, Model.Element element, 
      string name, DafnyModelVariable parent) {
      this.state = state;
      Element = element;
      Type = state.Model.GetDafnyType(element);
      children = new();
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

    public virtual string Value {
      get {
        string result = state.Model.CanonicalName(Element, state);
        if (children.Count == 0)
          return result == "" ? "()" : result;
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
        if (Type.Name == "set") {
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
      return Element.Id;
    }

    public override bool Equals(object obj) {
      if (obj is not DafnyModelVariable other)
        return false;
      return other.Element == Element && other.state == state && other.Name == Name;
    }
  }

  public class DuplicateVariable : DafnyModelVariable {
    public readonly DafnyModelVariable original;

    internal DuplicateVariable(DafnyModelState state, DafnyModelVariable original, string newName, DafnyModelVariable parent)
      : base(state, original.Element, newName, parent) {
      this.original = original;
    }

    public override string Value => original.ShortName;

    public override IEnumerable<DafnyModelVariable> GetExpansion() {
      return original.GetExpansion();
    }
  }
  
  public class SeqVariable : DafnyModelVariable {
    
    private DafnyModelVariable seqLength;
    Dictionary<int, DafnyModelVariable> seqElements;

    internal SeqVariable(DafnyModelState state, Model.Element element, string name, DafnyModelVariable parent)
      : base(state, element, name, parent) {
      seqLength = null;
      seqElements = new Dictionary<int, DafnyModelVariable>();
    }

    public override string Value {
      get {
        var length = GetLength();
        if (length == null || seqElements.Count != length) {
          return base.Value;
        }
        List<string> result = new();
        for (int i = 0; i < length; i++) {
          if (!seqElements.ContainsKey(i)) {
            return base.Value;
          }
          result.Add(seqElements[i].IsPrimitive ? 
            seqElements[i].Value : 
            seqElements[i].ShortName);
        }
        return "[" + String.Join(", ", result) + "]";
      }
    }

    public int? GetLength() {
      return (seqLength?.Element as Model.Integer)?.AsInt();
    }

    public DafnyModelVariable GetAtIndex(int i) {
      return seqElements.GetValueOrDefault(i, null);
    }

    public void SetLength(DafnyModelVariable seqLength) {
      this.seqLength = seqLength;
    }

    public void AddAtIndex(DafnyModelVariable e, int? index) {
      if (index == null) {
        return;
      }
      seqElements[(int) index] = e;
    }
  }

  public class MapVariable : DafnyModelVariable {

    public readonly Dictionary<DafnyModelVariable, DafnyModelVariable> mappings = new();

    internal MapVariable(DafnyModelState state, Model.Element element, string name, DafnyModelVariable parent) : base(state, element, name, parent) { }

    public override string Value {
      get {
        if (mappings.Count == 0)
          return "()";
        // maps a key value pair to how many times it appears in the map
        // a key value pair can appear many times in a map due to "?:int" etc.
        Dictionary<string, int> mapStrings = new();
        foreach (var key in mappings.Keys) {
          var keyString = key.IsPrimitive ? key.Value : key.Name;
          var valueString = "?";
          if (mappings[key] != null) {
            valueString = mappings[key].IsPrimitive
              ? mappings[key].Value
              : mappings[key].Name;
          }
          var mapString = keyString + " := " + valueString;
          mapStrings[mapString] = mapStrings.GetValueOrDefault(mapString, 0) + 1;
        }
        return "(" + String.Join(", ", mapStrings.Keys.ToList()
          .ConvertAll(keyValuePair => 
            mapStrings[keyValuePair] == 1 ? 
              keyValuePair: 
              keyValuePair + " [+"+ (mapStrings[keyValuePair] - 1) + "]")) + ")";
      }
    }
    
    public void AddMapping(DafnyModelVariable from, DafnyModelVariable to) {
      if (mappings.ContainsKey(from)) {
        return;
      }
      mappings[from] = to;
    }
  }

  public class DafnyModelType  {
    
    public readonly string Name;
    public readonly List<DafnyModelType> TypeArgs;

    public DafnyModelType(string name, List<DafnyModelType> typeArgs) {
      Name = name;
      TypeArgs = typeArgs;
    }

    public DafnyModelType(string name):this(name, new List<DafnyModelType>()) { }

    public override string ToString() {
      if (TypeArgs.Count == 0) {
        return Name;
      }
      return Name + "<" + String.Join(",", TypeArgs.ConvertAll(x => x.ToString())) + ">";
    }

    /// <summary>
    /// Recursively convert this type's name and the names of its type arguments
    /// to the Dafny format. So, for instance,
    /// Mo__dule___mModule2__.Cla____ss is converted to  Mo_dule_.Module2_.Cla__ss
    /// </summary>
    public DafnyModelType InDafnyFormat() {
      // The line below converts "_m" used in boogie to separate modules to ".":
      var tmp = Regex.Replace(Name, "(?<=[^_](__)*)_m", ".");
      // The code below converts every "__" to "_":
      var removeNextUnderscore = false;
      var newName = "";
      foreach (var c in tmp) {
        if (c == '_') {
          if (!removeNextUnderscore) {
            newName += c;
          }
          removeNextUnderscore = !removeNextUnderscore;
        } else {
          newName += c;
        }
      }
      return new(newName, TypeArgs.ConvertAll(type => type.InDafnyFormat()));
    }
  }
}