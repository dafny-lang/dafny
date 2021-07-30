using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie.ModelViewer.Dafny
{
  public class DafnyModelState {
    private readonly List<DafnyModelVariable> Vars = new();
    internal readonly DafnyModel dm;
    private readonly List<DafnyModelVariable> skolems;
    private Model.CapturedState state;
    private DafnyModel langModel;
    private Dictionary<Model.Element, DafnyModelVariable> varMap;

    public int VarIndex; // used to assign unique indices to variables

    public DafnyModelState(DafnyModel parent, Model.CapturedState s) {
      state = s;
      langModel = parent;
      dm = parent;
      state = s;
      VarIndex = 0;
      varMap = new Dictionary<Model.Element, DafnyModelVariable>();
      skolems = new List<DafnyModelVariable>(SkolemVars());
      SetupVars();
    }

    public HashSet<DafnyModelVariable> ExpandedVariableSet(int maxDepth) {
      HashSet<DafnyModelVariable> vars = new();
      List<Tuple<DafnyModelVariable, int>> varsToAdd = new();
      Vars.ForEach(v => varsToAdd.Add(new Tuple<DafnyModelVariable, int>(v, 0)));
      skolems.ForEach(v => varsToAdd.Add(new Tuple<DafnyModelVariable, int>(v, 0)));
      while (varsToAdd.Count != 0) {
        var (next, depth) = varsToAdd[0];
        varsToAdd.RemoveAt(0);
        if (vars.Contains(next))
          continue;
        vars.Add(next);
        if (depth < maxDepth)
          foreach (var v in next.GetExpansion().
            Where(x => !vars.Contains(x) && !x.IsPrimitive)) { 
            varsToAdd.Add(new Tuple<DafnyModelVariable, int>(v, depth + 1));
          }
      }
      return vars;
    }

    public bool ExistsVar(Model.Element element) {
      return varMap.ContainsKey(element);
    }

    public void AddVar(Model.Element element, DafnyModelVariable var) {
      varMap[element] = var;
    }
    
    public DafnyModelVariable GetVar(Model.Element element) {
      return varMap[element];
    }

    void SetupVars() {
      var names = Util.Empty<string>();

      if (dm.states.Count > 0) {
        var prev = dm.states.Last();
        names = prev.Vars.Map(v => v.Name);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names) {
        if (dm.GetUserVariableName(v) != null) {
          var val = state.TryGet(v);
          var vn = DafnyModelVariable.Get(this, val, v, duplicate:true);
          if (curVars.ContainsKey(v))
            dm.RegisterLocalValue(vn.Name, val);
          Vars.Add(vn);
        }
      }
    }

    IEnumerable<DafnyModelVariable> SkolemVars() {
      foreach (var f in dm.model.Functions) {
        if (f.Arity != 0) continue;
        int n = f.Name.IndexOf('!');
        if (n == -1) continue;
        string name = f.Name.Substring(0, n);
        if (!name.Contains('#')) continue;
        yield return DafnyModelVariable.Get(this, f.GetConstant(), name);
      }
    }
    
    public Model.CapturedState State => state;
    
    public virtual string CapturedStateName => State.Name;

    public virtual string Name => langModel.ShortenToken(state.Name, 20, true);
  }
}