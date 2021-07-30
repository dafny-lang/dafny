// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.ModelViewer.Dafny
{
  public class Provider
  {
    public static Provider Instance = new();
    private Provider() { }

    public DafnyModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      var dm = new DafnyModel(m, opts);
      foreach (var s in m.States)
      {
        var sn = new DafnyModelState(dm, s);
        dm.states.Add(sn);
      }
      return dm;
    }
  }

  public class DafnyModel : LanguageModel
  {
    public readonly Model.Func f_set_select, f_seq_length, f_seq_index, f_box, f_dim, f_index_field, f_multi_index_field, f_dtype, f_null;
    public readonly Dictionary<Model.Element, Model.Element[]> ArrayLengths = new();
    public readonly Dictionary<Model.Element, Model.FuncTuple> DatatypeValues = new();
    public List<DafnyModelState> states = new();

    public DafnyModel(Model m, ViewOptions opts) : base(m, opts) {
      f_set_select = MergeMapSelectFunctions(2);
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

    /// <summary>
    /// Creates a new function that merges together the applications of all the
    /// functions that have a certain arity and whose name matches the
    /// "^MapType[0-9]*Select$" pattern. This has previously been done by
    /// Boogie's Model Parser as a preprocessing step but has been deprecated
    /// since 2.9.2
    /// </summary>
    private Model.Func MergeMapSelectFunctions(int arity) {
      var name = "[" + arity + "]";
      if (model.HasFunc(name)) {
        // Coming up with a new name if the ideal one is reserved
        var id = 0;
        while (model.HasFunc(name + "#" + id)) {
          id++;
        }
        name += "#" + id;
      }
      var result = model.MkFunc(name, arity);
      foreach (var func in model.Functions) {
        if (!Regex.IsMatch(func.Name, "^MapType[0-9]*Select$") ||
            func.Arity != arity) {
          continue;
        }
        foreach (var app in func.Apps) {
          result.AddApp(app.Result, app.Args);
        }
        result.Else ??= func.Else;
      }
      return result;
    }

    public IEnumerable<DafnyModelState> States => states;

    public string GetUserVariableName(string name)
    {
      if (name.StartsWith("$")) // this covers $Heap and $_Frame and $nw...
        return null;
      if (name.Contains("##"))  // a temporary variable of the translation
        return null;
      return name;
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

    public IEnumerable<DafnyModelVariable> GetExpansion(DafnyModelState dafnyModelState, DafnyModelVariable var)
    {
      List<DafnyModelVariable> result = new ();

      if (var.element.Kind != Model.ElementKind.Uninterpreted)
        return result;

      // Perhaps elt is a known datatype value
      Model.FuncTuple fnTuple;
      if (DatatypeValues.TryGetValue(var.element, out fnTuple))
      {
        // elt is a datatype value
        int i = 0;
        foreach (var arg in fnTuple.Args)
        {
          result.Add(DafnyModelVariable.Get(dafnyModelState, arg, var.element.ToString() + i, var));
          i++;
        }
        return result;
      }

      // Perhaps elt is a sequence
      var seqLen = f_seq_length.AppWithArg(0, var.element);
      if (seqLen != null)
      {
        // elt is a sequence
        foreach (var tpl in f_seq_index.AppsWithArg(0, var.element))
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result), "[" + tpl.Args[1] + "]", var));
        return result;
      }

      // Perhaps elt is a set
      foreach (var tpl in f_set_select.AppsWithArg(0, var.element))
      {
        var setElement = tpl.Args[1];
        var containment = tpl.Result;
        result.Add(DafnyModelVariable.Get(dafnyModelState, containment, "["+Unbox(setElement)+"]", var));
      }
      if (result.Count != 0)
        return result;  // elt is a set

      // It seems elt is an object or array
      Model.Element[] lengths;
      if (ArrayLengths.TryGetValue(var.element, out lengths))
      {
        int i = 0;
        foreach (var len in lengths)
        {
          var name = lengths.Length == 1 ? "Length" : "Length" + i;
          result.Add(DafnyModelVariable.Get(dafnyModelState, len, name, var));
          i++;
        }
      }
      var heap = dafnyModelState.State.TryGet("$Heap");
      if (heap == null)
        return result;
      var instances = f_set_select.AppsWithArgs(0, heap, 1, var.element);
      if (instances == null || (!instances.Any()))
        return result;
      foreach (var tpl in f_set_select.AppsWithArg(0, instances.ToList()[0].Result))
      {
        var field = new FieldName(tpl.Args[1], this);
        if (field.NameFormat != "alloc")
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result), "." + field.NameFormat, var));
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

  public class DafnyModelState
  {
    public readonly List<DafnyModelVariable> Vars = new();
    internal readonly DafnyModel dm;
    private readonly List<DafnyModelVariable> skolems;
    private Model.CapturedState state;
    private LanguageModel langModel;
    private Dictionary<Model.Element, DafnyModelVariable> varMap;

    public DafnyModelState(DafnyModel parent, Model.CapturedState s) {
      state = s;
      langModel = parent;
      dm = parent;
      state = s;
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

    void SetupVars()
    {
      var names = Util.Empty<string>();

      if (dm.states.Count > 0)
      {
        var prev = dm.states.Last();
        names = prev.Vars.Map(v => v.Name);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names)
      {
        if (dm.GetUserVariableName(v) != null)
        {
          var val = state.TryGet(v);
          var vn = DafnyModelVariable.Get(this, val, v);
          if (curVars.ContainsKey(v))
            dm.RegisterLocalValue(vn.Name, val);
          Vars.Add(vn);
        }
      }
    }

    IEnumerable<DafnyModelVariable> SkolemVars()
    {
      foreach (var f in dm.model.Functions)
      {
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

  public class DafnyModelVariable
  {
    private DafnyModelState state;
    private Dictionary<string, DafnyModelVariable> children;
    public readonly Model.Element element;
    public readonly string Name;
    
    private static int index;

    public static DafnyModelVariable Get(DafnyModelState state,
      Model.Element element, string name, DafnyModelVariable parent=null) {
      if (state.ExistsVar(element)) {
        if (parent != null)
          parent.AddChild(name, state.GetVar(element));
        return state.GetVar(element);
      }
      return new(state, element, name, parent);
    }

    private DafnyModelVariable(DafnyModelState state, Model.Element element, string name, DafnyModelVariable parent) {
      this.state = state;
      this.element = element;
      children = new();
      state.AddVar(element, this);
      if (parent == null) {
        Name = name;
        return;
      }
      Name = "@" + index++;
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
      (element.Kind != Model.ElementKind.Uninterpreted || element == state.dm.f_null.GetConstant()) && 
      element.Kind != Model.ElementKind.Array && 
      (element.Kind != Model.ElementKind.DataValue || 
       ((Model.DatatypeValue) element).ConstructorName == "-");
    
    public virtual string ShortName => Regex.Replace(Name, @"#\d+$", "");
  }
}
