using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie.ModelViewer.Dafny {
  public class DafnyModelVariable {
    private DafnyModelState state;
    private Dictionary<string, DafnyModelVariable> children;
    public readonly Model.Element element;
    public readonly string Name;
    public readonly string Type;

    public static DafnyModelVariable Get(DafnyModelState state,
      Model.Element element, string name, DafnyModelVariable parent=null, bool duplicate=false) {
      if (state.ExistsVar(element)) {
        if (parent != null)
          parent.AddChild(name, state.GetVar(element));
        if (!duplicate)
          return state.GetVar(element);
      }
      return new(state, element, name, parent);
    }

    private DafnyModelVariable(DafnyModelState state, Model.Element element, string name, DafnyModelVariable parent) {
      this.state = state;
      this.element = element;
      Type = state.dm.GetDafnyType(element);
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
      return state.dm.GetExpansion(state, this);
    }

    public void AddChild(string name, DafnyModelVariable child) {
      children[name] = child;
    }
    
    public virtual string Value {
      get {
        string result = state.dm.CanonicalName(element);
        foreach (var key in children.Keys) {
          if (children[key].IsPrimitive)
            result += ", " + ShortName + key + "=" + children[key].Value;
          else
            result += ", " + ShortName + key + "=" + children[key].ShortName;
        }
        return result;
      }
    }

    public virtual bool IsPrimitive =>
      (element.Kind != Model.ElementKind.Uninterpreted 
       || element == state.dm.f_null.GetConstant()
       || state.dm.f_type.AppWithArg(0, element)?.Result == state.dm.f_char.GetConstant()) && 
      element.Kind != Model.ElementKind.Array && 
      (element.Kind != Model.ElementKind.DataValue || 
       ((Model.DatatypeValue) element).ConstructorName == "-");
    
    public virtual string ShortName => Regex.Replace(Name, @"#\d+$", "");
  }
}