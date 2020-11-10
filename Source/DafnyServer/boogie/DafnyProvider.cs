using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.ModelViewer.Dafny
{
  public class Provider : ILanguageProvider
  {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m)
    {
      return m.TryGetFunc("$$Language$Dafny") != null;
    }

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      var dm = new DafnyModel(m, opts);
      foreach (var s in m.States)
      {
        var sn = new StateNode(dm.states.Count, dm, s);
        dm.states.Add(sn);
      }
      dm.FinishStates();
      return dm;
    }
  }

  public class DafnyModel : LanguageModel
  {
    public readonly Model.Func f_heap_select, f_set_select, f_seq_length, f_seq_index, f_box, f_dim, f_index_field, f_multi_index_field, f_dtype, f_null;
    public readonly Dictionary<Model.Element, Model.Element[]> ArrayLengths = new Dictionary<Model.Element, Model.Element[]>();
    public readonly Dictionary<Model.Element, Model.FuncTuple> DatatypeValues = new Dictionary<Model.Element, Model.FuncTuple>();
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    public List<StateNode> states = new List<StateNode>();

    public DafnyModel(Model m, ViewOptions opts)
      : base(m, opts)
    {
      f_heap_select = m.MkFunc("[3]", 3);
      f_set_select = m.MkFunc("[2]", 2);
      f_seq_length = m.MkFunc("Seq#Length", 1);
      f_seq_index = m.MkFunc("Seq#Index", 2);
      f_box = m.MkFunc("$Box", 1);
      f_dim = m.MkFunc("FDim", 1);
      f_index_field = m.MkFunc("IndexField", 1);
      f_multi_index_field = m.MkFunc("MultiIndexField", 2);
      f_dtype = m.MkFunc("dtype", 1);
      f_null = m.MkFunc("null", 0);

      // collect the array dimensions from the various array.Length functions, and
      // collect all known datatype values
      foreach (var fn in m.Functions)
      {
        if (Regex.IsMatch(fn.Name, "^_System.array[0-9]*.Length[0-9]*$"))
        {
          int j = fn.Name.IndexOf('.', 13);
          int dims = j == 13 ? 1 : int.Parse(fn.Name.Substring(13, j - 13));
          int idx = j == 13 ? 0 : int.Parse(fn.Name.Substring(j + 7));
          foreach (var tpl in fn.Apps)
          {
            var elt = tpl.Args[0];
            var len = tpl.Result;
            Model.Element[] ar;
            if (!ArrayLengths.TryGetValue(elt, out ar))
            {
              ar = new Model.Element[dims];
              ArrayLengths.Add(elt, ar);
            }
            Contract.Assert(ar[idx] == null);
            ar[idx] = len;
          }
        }
        else if (fn.Name.StartsWith("#") && fn.Name.IndexOf('.') != -1 && fn.Name[1] != '#')
        {
          foreach (var tpl in fn.Apps)
          {
            var elt = tpl.Result;
            DatatypeValues.Add(elt, tpl);
          }
        }
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
      if (name.StartsWith("$")) // this covers $Heap and $_Frame and $nw...
        return null;
      if (name.Contains("##"))  // a temporary variable of the translation
        return null;
#if SOMETIME_AGAIN
      var hash = name.IndexOf('#');
      if (0 < hash)
        return name.Substring(0, hash);
#endif
      return name;
    }

    public Model.Element Image(Model.Element elt, Model.Func f)
    {
      var r = f.AppWithResult(elt);
      if (r != null)
        return r.Args[0];
      return null;
    }

    protected override string CanonicalBaseName(Model.Element elt, out NameSeqSuffix suff)
    {
      Model.FuncTuple fnTuple;
      suff = NameSeqSuffix.WhenNonZero;
      if (DatatypeValues.TryGetValue(elt, out fnTuple))
      {
        // elt is s a datatype value, make its name be the name of the datatype constructor
        string nm = fnTuple.Func.Name;
        if (fnTuple.Func.Arity == 0)
          return nm;
        else
          return nm + "(...)";
      }
      var seqLen = f_seq_length.AppWithArg(0, elt);
      if (seqLen != null)
      {
        // elt is a sequence
        return string.Format("[Length {0}]", seqLen.Result.AsInt());
      }

      if (elt == f_null.GetConstant())
        return "null";

      var tp = f_dtype.TryEval(elt);
      if (tp != null)
      {
        foreach (var app in tp.References)
        {
          if (app.Args.Length == 0 && app.Func.Name.StartsWith("class."))
          {
            suff = NameSeqSuffix.Always;
            return app.Func.Name.Substring(6);
          }
        }
      }

      return base.CanonicalBaseName(elt, out suff);
    }

    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt)
    {
      List<ElementNode> result = new List<ElementNode>();

      if (elt.Kind != Model.ElementKind.Uninterpreted)
        return result;

      // Perhaps elt is a known datatype value
      Model.FuncTuple fnTuple;
      if (DatatypeValues.TryGetValue(elt, out fnTuple))
      {
        // elt is a datatype value
        int i = 0;
        foreach (var arg in fnTuple.Args)
        {
          var edgname = new EdgeName(this, i.ToString());
          result.Add(new FieldNode(state, edgname, arg));
          i++;
        }
        return result;
      }

      // Perhaps elt is a sequence
      var seqLen = f_seq_length.AppWithArg(0, elt);
      if (seqLen != null)
      {
        // elt is a sequence
        foreach (var tpl in f_seq_index.AppsWithArg(0, elt))
        {
          var edgname = new EdgeName(this, "[%0]", tpl.Args[1]);
          result.Add(new FieldNode(state, edgname, Unbox(tpl.Result)));
        }
        return result;
      }

      // Perhaps elt is a set
      foreach (var tpl in f_set_select.AppsWithArg(0, elt))
      {
        var setElement = tpl.Args[1];
        var containment = tpl.Result;
        var edgname = new EdgeName(this, "[%0]", Unbox(setElement));
        result.Add(new FieldNode(state, edgname, containment));
      }
      if (result.Count != 0)
        return result;  // elt is a set

      // It seems elt is an object or array
      Model.Element[] lengths;
      if (ArrayLengths.TryGetValue(elt, out lengths))
      {
        int i = 0;
        foreach (var len in lengths)
        {
          var name = lengths.Length == 1 ? "Length" : "Length" + i;
          var edgname = new EdgeName(this, name);
          result.Add(new FieldNode(state, edgname, len));
          i++;
        }
      }
      var heap = state.State.TryGet("$Heap");
      if (heap != null)
      {
        foreach (var tpl in f_heap_select.AppsWithArgs(0, heap, 1, elt))
        {
          var field = new FieldName(tpl.Args[2], this);
          if (field.NameFormat != "alloc")
          {
            var edgname = new EdgeName(this, field.NameFormat, field.NameArgs);
            result.Add(new FieldNode(state, edgname, Unbox(tpl.Result)));
          }
        }
      }
      return result;
    }

    class FieldName
    {
      public readonly Model.Element Field;
      public readonly int Dims;
      public readonly string NameFormat;
      public readonly Model.Element[] NameArgs;

      public FieldName(Model.Element elt, DafnyModel dm)
      {
        Field = elt;
        NameArgs = new Model.Element[Dims];
        var tpl = dm.f_dim.AppWithArg(0, elt);
        if (tpl != null)
        {
          Dims = tpl.Result.AsInt();
          NameArgs = new Model.Element[Dims];
          for (int i = Dims; 0 <= --i;)
          {
            if (i == 0)
            {
              tpl = dm.f_index_field.AppWithResult(elt);
              NameArgs[i] = tpl.Args[0];
            }
            else
            {
              tpl = dm.f_multi_index_field.AppWithResult(elt);
              NameArgs[i] = tpl.Args[1];
              elt = tpl.Args[0];
            }
          }
        }
        // now for the name
        if (Dims == 0)
        {
          NameFormat = Field.ToString();
          foreach (var n in Field.Names)
          {
            NameFormat = n.Func.Name;
            int dot = NameFormat.LastIndexOf('.');
            if (0 <= dot)
              NameFormat = NameFormat.Substring(dot + 1);
            break;
          }
        }
        else
        {
          NameFormat = "[";
          string sep = "";
          for (int i = 0; i < Dims; i++)
          {
            NameFormat += sep + "%" + i;
            sep = ",";
          }
          NameFormat += "]";
        }
      }
    }

    Model.Element Unbox(Model.Element elt)
    {
      var unboxed = f_box.AppWithResult(elt);
      if (unboxed != null)
        return unboxed.Args[0];
      else
        return elt;
    }
  }

  public class StateNode : NamedState
  {
    internal readonly DafnyModel dm;
    public readonly List<VariableNode> Vars = new List<VariableNode>();
    internal readonly List<VariableNode> skolems;
    internal readonly int index;

    public StateNode(int i, DafnyModel parent, Model.CapturedState s)
       : base(s, parent)
    {
      dm = parent;
      state = s;
      index = i;

      skolems = new List<VariableNode>(SkolemVars());
      SetupVars();
    }

    void SetupVars()
    {
      var names = Util.Empty<string>();

      if (dm.states.Count > 0)
      {
        var prev = dm.states.Last();
        names = prev.Vars.Map(v => v.realName);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names)
      {
        if (dm.GetUserVariableName(v) != null)
        {
          var val = state.TryGet(v);
          var shortName = Regex.Replace(v, @"#\d+$", "");
          var vn = new VariableNode(this, v, val, names.Any(n => n != v && Regex.Replace(n, @"#\d+$", "") == shortName) ? v : shortName);
          vn.updatedHere = dm.states.Count > 0 && curVars.ContainsKey(v);
          if (curVars.ContainsKey(v))
            dm.RegisterLocalValue(vn.Name, val);
          Vars.Add(vn);
        }
      }

      dm.Flush(Nodes);
    }

    IEnumerable<VariableNode> SkolemVars()
    {
      foreach (var f in dm.model.Functions)
      {
        if (f.Arity != 0) continue;
        int n = f.Name.IndexOf('!');
        if (n == -1) continue;
        string name = f.Name.Substring(0, n);
        if (!name.Contains('#')) continue;
        yield return new VariableNode(this, name, f.GetConstant(), name);
      }
    }

    public override IEnumerable<IDisplayNode> Nodes
    {
      get
      {
        return Vars.Concat(skolems);
      }
    }
  }

  public class ElementNode : DisplayNode
  {
    protected StateNode stateNode;
    protected Model.Element elt;
    protected DafnyModel vm { get { return stateNode.dm; } }

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

  class FieldNode : ElementNode
  {
    public FieldNode(StateNode par, EdgeName realName, Model.Element elt)
      : base(par, realName, elt)
    {
      /*
      var idx = realName.LastIndexOf('.');
      if (idx > 0)
        name = realName.Substring(idx + 1);
       */
    }
  }

  class MapletNode : ElementNode
  {
    public MapletNode(StateNode par, EdgeName realName, Model.Element elt)
      : base(par, realName, elt)
    {
    }
  }

  public class VariableNode : ElementNode
  {
    public bool updatedHere;
    public string realName;

    public VariableNode(StateNode par, string realName, Model.Element elt, string shortName)
      : base(par, realName, elt)
    {
      this.realName = realName;
      name = new EdgeName(vm.GetUserVariableName(realName));
      ShortName = shortName;
    }
  }
}
