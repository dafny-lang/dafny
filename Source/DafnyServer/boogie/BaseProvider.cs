using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer.BCT
{
  public class Provider : ILanguageProvider
  {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m)
    {
      return m.TryGetFunc("$Alloc") != null;
    }

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      var dm = new BCTModel(m, opts);
      foreach (var s in m.States)
      {
        var sn = new StateNode(dm.states.Count, dm, s);
        dm.states.Add(sn);
      }
      dm.FinishStates();
      return dm;
    }
  }

  class BCTModel : LanguageModel
  {
    public readonly Model.Func f_heap_select;
    public readonly Dictionary<Model.Element, Model.Element[]> ArrayLengths = new Dictionary<Model.Element, Model.Element[]>();
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    public List<StateNode> states = new List<StateNode>();

    public BCTModel(Model m, ViewOptions opts)
      : base(m, opts)
    {
      f_heap_select = m.MkFunc("[3]", 3);

      foreach (Model.Func fn in m.Functions)
      {

      }
    }

    internal void FinishStates()
    {
      GenerateSourceLocations(states);
    }

    public override IEnumerable<IState> States
    {
      get { return states; }
    }

    public string GetUserVariableName(string name)
    {
      if (name == "$this")
        return "this";
      if (name.Contains("$"))
        return null;
      if (name == "isControlChecked" || name == "isControlEnabled")
        return null;
      return name;
    }

    public Model.Element Image(Model.Element elt, Model.Func f)
    {
      var r = f.AppWithResult(elt);
      if (r != null)
        return r.Args[0];
      return null;
    }

    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt)
    {
      List<ElementNode> result = new List<ElementNode>();
      return result;
    }
  }

  class StateNode : NamedState
  {
    internal readonly BCTModel dm;
    internal readonly List<VariableNode> vars = new List<VariableNode>();
    internal readonly int index;

    public StateNode(int i, BCTModel parent, Model.CapturedState s)
      : base(s, parent)
    {
      dm = parent;
      state = s;
      index = i;

      SetupVars();
    }

    void SetupVars()
    {
      var names = Util.Empty<string>();

      if (dm.states.Count > 0)
      {
        var prev = dm.states.Last();
        names = prev.vars.Map(v => v.realName);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names)
      {
        if (dm.GetUserVariableName(v) != null)
        {
          var val = state.TryGet(v);
          var vn = new VariableNode(this, v, val);
          vn.updatedHere = dm.states.Count > 0 && curVars.ContainsKey(v);
          if (curVars.ContainsKey(v))
            dm.RegisterLocalValue(vn.Name, val);
          vars.Add(vn);
        }
      }

      dm.Flush(Nodes);
    }

    public override IEnumerable<IDisplayNode> Nodes
    {
      get
      {
        return vars;
      }
    }
  }

  class ElementNode : DisplayNode
  {
    protected StateNode stateNode;
    protected Model.Element elt;
    protected BCTModel vm { get { return stateNode.dm; } }

    public ElementNode(StateNode st, EdgeName name, Model.Element elt)
      : base(st.dm, name, elt)
    {
      this.stateNode = st;
      this.elt = elt;
    }

    public ElementNode(StateNode st, string name, Model.Element elt)
      : this(st, new EdgeName(name), elt) { }

    protected override void ComputeChildren()
    {
      children.AddRange(vm.GetExpansion(stateNode, elt));
    }
  }

  class VariableNode : ElementNode
  {
    public bool updatedHere;
    public string realName;

    public VariableNode(StateNode par, string realName, Model.Element elt)
      : base(par, realName, elt)
    {
      this.realName = realName;
      name = new EdgeName(vm.GetUserVariableName(realName));
    }
  }
}
