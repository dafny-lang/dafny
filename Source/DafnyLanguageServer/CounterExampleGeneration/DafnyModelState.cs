// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

namespace DafnyServer.CounterexampleGeneration {

  /// <summary>
  /// Represents a program state in a DafnyModel
  /// </summary>
  public class DafnyModelState {

    internal readonly DafnyModel Model;
    internal readonly Model.CapturedState State;
    internal int VarIndex; // used to assign unique indices to variables
    private readonly List<DafnyModelVariable> vars;
    private readonly List<DafnyModelVariable> boundVars;
    // varMap prevents the creation of multiple variables for the same element.
    private readonly Dictionary<Model.Element, DafnyModelVariable> varMap;
    // varNameCount keeps track of the number of variables with the same name.
    // Name collision can happen in the presence of an old expression,
    // for instance, in which case the it is important to distinguish between
    // two variables that have the same name using an index provided by Boogie
    private readonly Dictionary<string, int> varNameCount;

    private const string InitialStateName = "<initial>";
    private static readonly Regex StatePositionRegex = new(
      @".*\((?<line>\d+),(?<character>\d+)\)",
      RegexOptions.IgnoreCase | RegexOptions.Singleline
    );

    internal DafnyModelState(DafnyModel model, Model.CapturedState state) {
      Model = model;
      State = state;
      VarIndex = 0;
      vars = new();
      varMap = new();
      varNameCount = new();
      boundVars = new(BoundVars());
      SetupVars();
    }

    /// <summary>
    /// Start with the union of vars and boundVars and expand the set by adding 
    /// variables that represent fields of any object in the original set or
    /// elements of any sequence in the original set, etc. This is done
    /// recursively in breadth-first order and only up to a certain maximum
    /// depth.
    /// </summary>
    /// <param name="maxDepth">The maximum depth up to which to expand the
    /// variable set.</param>
    /// <returns>Set of variables</returns>
    public HashSet<DafnyModelVariable> ExpandedVariableSet(int maxDepth) {
      HashSet<DafnyModelVariable> expandedSet = new();
      // The following is the queue for elements to be added to the set. The 2nd
      // element of a tuple is the depth of the variable w.r.t. the original set
      List<Tuple<DafnyModelVariable, int>> varsToAdd = new();
      vars.ForEach(variable => varsToAdd.Add(new(variable, 0)));
      boundVars.ForEach(variable => varsToAdd.Add(new(variable, 0)));
      while (varsToAdd.Count != 0) {
        var (next, depth) = varsToAdd[0];
        varsToAdd.RemoveAt(0);
        if (expandedSet.Contains(next)) {
          continue;
        }
        if (depth == maxDepth) {
          break;
        }
        expandedSet.Add(next);
        // fields of primitive types are skipped:
        foreach (var v in next.GetExpansion().
            Where(variable => !expandedSet.Contains(variable) && !variable.IsPrimitive)) {
          varsToAdd.Add(new(v, depth + 1));
        }
      }
      return expandedSet;
    }

    internal bool ExistsVar(Model.Element element) {
      return varMap.ContainsKey(element);
    }

    internal void AddVar(Model.Element element, DafnyModelVariable var) {
      if (!ExistsVar(element)) {
        varMap[element] = var;
      }
    }

    internal DafnyModelVariable GetVar(Model.Element element) {
      return varMap[element];
    }

    internal void AddVarName(string name) {
      varNameCount[name] = varNameCount.GetValueOrDefault(name, 0) + 1;
    }

    internal bool VarNameIsShared(string name) {
      return varNameCount.GetValueOrDefault(name, 0) > 1;
    }

    public string FullStateName => State.Name;

    private string ShortenedStateName => ShortenName(State.Name, 20);

    public bool IsInitialState => FullStateName.Equals(InitialStateName);

    public int GetLineId() {
      var match = StatePositionRegex.Match(ShortenedStateName);
      if (!match.Success) {
        throw new ArgumentException(
          $"state does not contain position: {ShortenedStateName}");
      }
      return int.Parse(match.Groups["line"].Value);
    }

    public int GetCharId() {
      var match = StatePositionRegex.Match(ShortenedStateName);
      if (!match.Success) {
        throw new ArgumentException(
          $"state does not contain position: {ShortenedStateName}");
      }
      return int.Parse(match.Groups["character"].Value);
    }

    /// <summary>
    /// Initialize the vars list, which stores all variables relevant to
    /// the counterexample except for the bound variables
    /// </summary>
    private void SetupVars() {
      var names = Enumerable.Empty<string>();
      if (Model.States.Count > 0) {
        var prev = Model.States.Last();
        names = prev.vars.ConvertAll(variable => variable.Name);
      }
      names = names.Concat(State.Variables).Distinct();
      foreach (var v in names) {
        if (!DafnyModel.IsUserVariableName(v)) {
          continue;
        }
        var val = State.TryGet(v);
        if (val == null) {
          continue; // This variable has no value in the model, so ignore it.
        }

        var vn = DafnyModelVariableFactory.Get(this, val, v, duplicate: true);
        vars.Add(vn);
      }
    }

    /// <summary>
    /// Return list of bound variables
    /// </summary>
    private IEnumerable<DafnyModelVariable> BoundVars() {
      foreach (var f in Model.Model.Functions) {
        if (f.Arity != 0) {
          continue;
        }
        int n = f.Name.IndexOf('!');
        if (n == -1) {
          continue;
        }
        var name = f.Name.Substring(0, n);
        if (!name.Contains('#')) {
          continue;
        }

        yield return DafnyModelVariableFactory.Get(this, f.GetConstant(), name,
          null, true);
      }
    }

    private static string ShortenName(string name, int fnLimit) {
      var loc = TryParseSourceLocation(name);
      if (loc != null) {
        var fn = loc.Filename;
        int idx = fn.LastIndexOfAny(new[] { '\\', '/' });
        if (idx > 0) {
          fn = fn.Substring(idx + 1);
        }
        if (fn.Length > fnLimit) {
          fn = fn.Substring(0, fnLimit) + "..";
        }
        var addInfo = loc.AddInfo;
        if (addInfo != "") {
          addInfo = ":" + addInfo;
        }
        return $"{fn}({loc.Line},{loc.Column}){addInfo}";
      }
      return name;
    }

    /// <summary>
    /// Parse a string (typically the name of the captured state in Boogie) to
    /// extract a SourceLocation from it. An example of a string to be parsed:
    /// @"c:\users\foo\bar.c(12,10) : random string"
    /// The ": random string" part is optional.
    /// </summary>
    private static SourceLocation TryParseSourceLocation(string name) {
      int par = name.LastIndexOf('(');
      if (par <= 0) {
        return null;
      }
      var res = new SourceLocation() { Filename = name.Substring(0, par) };
      var words = name.Substring(par + 1)
        .Split(',', ')', ':')
        .Where(x => x != "")
        .ToArray();
      if (words.Length < 2) {
        return null;
      }
      if (!int.TryParse(words[0], out res.Line) ||
          !int.TryParse(words[1], out res.Column)) {
        return null;
      }
      int colon = name.IndexOf(':', par);
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