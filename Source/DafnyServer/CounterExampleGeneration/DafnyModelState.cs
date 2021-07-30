// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace DafnyServer.CounterExampleGeneration {
  
  public class DafnyModelState {
    
    internal readonly DafnyModel Model;
    internal readonly Model.CapturedState State;
    private readonly List<DafnyModelVariable> vars;
    private readonly List<DafnyModelVariable> skolems;
    // The following map helps to avoid the creation of multiple variables for
    // the same element.
    private readonly Dictionary<Model.Element, DafnyModelVariable> varMap;
    internal int VarIndex; // used to assign unique indices to variables

    public DafnyModelState(DafnyModel model, Model.CapturedState state) {
      Model = model;
      State = state;
      VarIndex = 0;
      vars = new();
      varMap = new ();
      skolems = new List<DafnyModelVariable>(SkolemVars());
      SetupVars();
    }

    /// <summary>
    /// Start with the union of vars and skolems and expand it by adding the
    /// variables that represent fields of any object in the original set or
    /// elements of any sequence in the original set, etc. This is done
    /// recursively in breadth-first order and only up to a certain maximum
    /// depth.
    /// </summary>
    /// <param name="maxDepth">The maximum depth up to which to expand the
    /// variable set. Can be null to indicate that there is no limit</param>
    /// <returns>List of variables</returns>
    public HashSet<DafnyModelVariable> ExpandedVariableSet(int? maxDepth) {
      HashSet<DafnyModelVariable> expandedSet = new();
      // The following is the queue for elements to be added to the set. The 2nd
      // element of a tuple is the depth of the variable w.r.t. the original set
      List<Tuple<DafnyModelVariable, int>> varsToAdd = new();
      vars.ForEach(v => varsToAdd.Add(new Tuple<DafnyModelVariable, int>(v, 0)));
      skolems.ForEach(v => varsToAdd.Add(new Tuple<DafnyModelVariable, int>(v, 0)));
      while (varsToAdd.Count != 0) {
        var (next, depth) = varsToAdd[0];
        varsToAdd.RemoveAt(0);
        if (expandedSet.Contains(next))
          continue;
        expandedSet.Add(next);
        if (depth == maxDepth)
          break;
        // fields of primitive types are skipped:
        foreach (var v in next.GetExpansion().
            Where(x => !expandedSet.Contains(x) && !x.IsPrimitive)) { 
            varsToAdd.Add(new Tuple<DafnyModelVariable, int>(v, depth + 1));
        }
      }
      return expandedSet;
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
    
    public string FullStateName => State.Name;

    public string ShortenedStateName => ShortenName(State.Name, 20);

    /// <summary>
    /// Initializes the vars list, which stores all variables relevant to
    /// the counterexample except for Skolem constants
    /// </summary>
    private void SetupVars() {
      var names = Enumerable.Empty<string>();
      if (Model.States.Count > 0) {
        var prev = Model.States.Last();
        names = prev.vars.ConvertAll(v => v.Name);
      }
      names = names.Concat(State.Variables).Distinct();
      var curVars = State.Variables.ToDictionary(x => x);
      foreach (var v in names) {
        if (Model.GetUserVariableName(v) != null) {
          var val = State.TryGet(v);
          var vn = DafnyModelVariable.Get(this, val, v, duplicate:true);
          if (curVars.ContainsKey(v))
            Model.RegisterLocalValue(vn.Name, val);
          vars.Add(vn);
        }
      }
    }

    /// <summary>
    /// Returns list of variables associated with Skolem constants
    /// </summary>
    private IEnumerable<DafnyModelVariable> SkolemVars() {
      foreach (var f in Model.Model.Functions) {
        if (f.Arity != 0) continue;
        var n = f.Name.IndexOf('!');
        if (n == -1) continue;
        var name = f.Name.Substring(0, n);
        if (!name.Contains('#')) continue;
        yield return DafnyModelVariable.Get(this, f.GetConstant(), name, 
          null, true);
      }
    }
    
    private static string ShortenName(string name, int fnLimit) {
      var loc = TryParseSourceLocation(name);
      if (loc != null) {
        var fn = loc.Filename;
        var idx = fn.LastIndexOfAny(new[]{ '\\', '/' });
        if (idx > 0)
          fn = fn.Substring(idx + 1);
        if (fn.Length > fnLimit) {
          fn = fn.Substring(0, fnLimit) + "..";
        }
        var addInfo = loc.AddInfo;
        if (addInfo != "")
          addInfo = ":" + addInfo;
        return $"{fn}({loc.Line},{loc.Column}){addInfo}";
      }
      return name;
    }
    /// <summary>
    /// Parses a string (typically the name of the captured state in Boogie) to
    /// extract a SourceLocation from it. An example of a string to be parsed:
    /// @"c:\users\foo\bar.c(12,10) : random string"
    /// The ": random string" part is optional.
    /// </summary>
    private static SourceLocation TryParseSourceLocation(string name) {
      var par = name.LastIndexOf('(');
      if (par <= 0) return null;
      var res = new SourceLocation() { Filename = name.Substring(0, par) };
      var words = name.Substring(par + 1)
        .Split(',', ')', ':')
        .Where(x => x != "")
        .ToArray();
      if (words.Length < 2) return null;
      if (!int.TryParse(words[0], out res.Line) || 
          !int.TryParse(words[1], out res.Column)) 
        return null;
      var colon = name.IndexOf(':', par);
      res.AddInfo = colon > 0 ? name.Substring(colon + 1).Trim() : "";
      return res;
    }
    
    private class SourceLocation {
      public string Filename;
      public string AddInfo;
      public int Line;
      public int Column;
    }
  }
}