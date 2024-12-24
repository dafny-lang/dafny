// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class PartialState {

  public bool IsLoopEntryState => FullStateName.Contains(CaptureStateExtensions.AfterLoopIterationsStateMarker);
  // ghost variables introduced by the counterexample whose values must be true for the counterexample to hold:
  public List<string> LoopGuards = new();
  public readonly Dictionary<PartialValue, List<string>> KnownVariableNames = new();
  private readonly List<PartialValue> initialPartialValues;
  internal readonly DafnyModel Model;
  internal readonly Model.CapturedState State;
  private const string InitialStateName = "<initial>";
  private static readonly Regex StatePositionRegex = new(
    @".*\((?<line>\d+),(?<character>\d+)\)",
    RegexOptions.IgnoreCase | RegexOptions.Singleline
  );
  internal readonly Dictionary<Model.Element, PartialValue> AllPartialValues = new();

  private const string BoundVarPrefix = "boundVar";

  internal PartialState(DafnyModel model, Model.CapturedState state) {
    Model = model;
    State = state;
    initialPartialValues = new List<PartialValue>();
    SetupBoundVars();
    SetupVars();
  }

  /// <summary>
  /// Start with the union of vars and boundVars and expand the set by adding 
  /// all partial values that are necessary to fully constrain the counterexample.
  /// </summary>
  /// <returns>Set of partial values</returns>
  public HashSet<PartialValue> ExpandedVariableSet() {
    HashSet<PartialValue> expandedSet = new();
    // The following is the queue for elements to be added to the set. The 2nd
    // element of a tuple is the depth of the variable w.r.t. the original set
    List<Tuple<PartialValue, int>> varsToAdd = new();
    initialPartialValues.ForEach(variable => varsToAdd.Add(new(variable, 0)));
    while (varsToAdd.Count != 0) {
      var (next, depth) = varsToAdd[0];
      varsToAdd.RemoveAt(0);
      if (expandedSet.Contains(next)) {
        continue;
      }
      expandedSet.Add(next);
      // fields of primitive types are skipped:
      foreach (var v in next.GetRelatedValues().
          Where(variable => !expandedSet.Contains(variable))) {
        varsToAdd.Add(new(v, depth + 1));
      }
    }
    return expandedSet;
  }

  /// <summary>
  /// Return a conjunction of expression that is represented by a balanced AST. This is intended to prevent
  /// stackoverflow errors that occur if multiple conjuncts are joined in a linked list fashion.
  /// </summary>
  /// <returns></returns>
  private Expression GetCompactConjunction(List<Expression> conjuncts) {
    if (!conjuncts.Any()) {
      return new LiteralExpr(Token.NoToken, true);
    }

    if (conjuncts.Count() == 1) {
      return conjuncts.First();
    }

    var middle = conjuncts.Count() / 2;
    var left = GetCompactConjunction(conjuncts.Take(middle).ToList());
    var right = GetCompactConjunction(conjuncts.Skip(middle).ToList());
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, left, right);
  }

  /// <summary>
  /// Convert this counterexample state into an assumption that could be inserted in Dafny source code
  /// </summary>
  public Statement AsAssumption() {
    var allVariableNames = new Dictionary<PartialValue, Expression>();
    var variables = ExpandedVariableSet().ToArray();
    var constraintSet = new HashSet<Constraint>();

    // Collect all constraints into one list:
    foreach (var variable in variables) {
      foreach (var constraint in variable.Constraints) {
        constraintSet.Add(constraint);
      }
    }

    // Ignore TypeTest constraints because they make the counterexample too verbose
    var constraints = constraintSet.Where(constraint => constraint is not TypeTestConstraint).ToList();
    constraints = Constraint.ResolveAndOrder(allVariableNames, constraints, true, true);

    // Create a bound variable for every partial value that we cannot otherwise refer to using variables in scope
    var boundVars = new List<BoundVar>();
    for (int i = 0; i < variables.Length; i++) {
      if (!allVariableNames.ContainsKey(variables[i])) {
        boundVars.Add(new BoundVar(Token.NoToken, BoundVarPrefix + boundVars.Count, variables[i].Type));
        allVariableNames[variables[i]] = new IdentifierExpr(Token.NoToken, boundVars.Last());
      }
    }

    // Translate all constraints to Dafny expressions, removing any duplicates:
    var constraintsAsExpressions = new List<Expression>();
    var constraintsAsStrings = new HashSet<String>();
    foreach (var constraint in constraints) {
      var constraintAsExpression = constraint.AsExpression(allVariableNames);
      if (constraintAsExpression == null) {
        continue;
      }
      var constraintAsString = constraintAsExpression.ToString();
      if (constraintsAsStrings.Contains(constraintAsString)) {
        continue;
      }

      constraintsAsStrings.Add(constraintAsString);
      constraintsAsExpressions.Add(constraintAsExpression);
    }

    // Convert the constraints into one conjunction
    Expression expression = GetCompactConjunction(constraintsAsExpressions);

    if (constraintsAsExpressions.Count > 0 && boundVars.Count > 0) {
      expression = new ExistsExpr(Token.NoToken, SourceOrigin.NoToken, boundVars, null, expression, null);
    }

    if ((LoopGuards.Count != 0 && !IsLoopEntryState) || LoopGuards.Count > 1) {
      Expression loopGuard = new IdentifierExpr(Token.NoToken, LoopGuards[0]);
      for (int i = 1; i < LoopGuards.Count; i++) {
        if (i == LoopGuards.Count - 1 && IsLoopEntryState) {
          continue;
        }
        loopGuard = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, loopGuard,
          new IdentifierExpr(Token.NoToken, LoopGuards[i]));
      }
      expression = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Imp, loopGuard, expression);
    }

    if (!IsLoopEntryState) {
      return new AssumeStmt(SourceOrigin.NoToken, expression, null);
    }
    return new AssignStatement(SourceOrigin.NoToken, new List<Expression>() { new IdentifierExpr(Token.NoToken, LoopGuards.Last()) },
        new List<AssignmentRhs>() { new ExprRhs(expression) });
  }

  /// <summary>
  /// Initialize the vars list, which stores all variables relevant to
  /// the counterexample except for the bound variables
  /// </summary>
  private void SetupVars() {
    var names = Enumerable.Empty<string>();
    foreach (var partialState in Model.States) {
      names = names.Concat(partialState.State.Variables);
    }
    names = names.Concat(State.Variables).Distinct().ToList();
    var notDefinitelyAssigned = new HashSet<string>();
    foreach (var name in names.Where(name => name.StartsWith(BoogieGenerator.DefassPrefix))) {
      var val = State.TryGet(name);
      if (val == null) {
        continue;
      }
      if (val is Model.Boolean { Value: false }) {
        notDefinitelyAssigned.Add(name[7..]);
      }
    }
    foreach (var v in names) {
      if (!IsUserVariableName(v) || notDefinitelyAssigned.Contains(v)) {
        continue;
      }
      var val = State.TryGet(v);
      if (val == null) {
        continue; // This variable has no value in the model, so ignore it.
      }

      var value = PartialValue.Get(val, this);
      initialPartialValues.Add(value);
      var _ = new IdentifierExprConstraint(value, v.Split("#").First());
      if (!KnownVariableNames.ContainsKey(value)) {
        KnownVariableNames[value] = new List<string>();
      }
      KnownVariableNames[value].Add(v.Split("#").First());
    }
  }

  /// <summary>
  /// Return True iff the variable name is referring to a variable that has
  /// a direct analog in Dafny source (i.e. not $Heap, $_Frame, $nw, etc.)
  /// </summary>
  private static bool IsUserVariableName(string name) =>
    !name.Contains("$") && name.Count(c => c == '#') <= 1;

  /// <summary>
  /// Instantiate BoundVariables
  /// </summary>
  private void SetupBoundVars() {
    foreach (var f in Model.Model.Functions) {
      if (f.Arity != 0) {
        continue;
      }
      int n = f.Name.IndexOf('!');
      if (n == -1) {
        continue;
      }
      var name = f.Name[..n];
      if (!name.Contains('#') || name.Contains('$')) {
        continue;
      }

      var value = PartialValue.Get(f.GetConstant(), this);
      initialPartialValues.Add(value);
      var _ = new IdentifierExprConstraint(value, name);
      if (!KnownVariableNames.ContainsKey(value)) {
        KnownVariableNames[value] = new();
      }
      KnownVariableNames[value].Add(name);
    }
  }

  public string FullStateName => State.Name;

  private string ShortenedStateName => ShortenName(State.Name, 20);

  public bool IsInitialState => FullStateName.Equals(InitialStateName);

  public bool StateContainsPosition() {
    return StatePositionRegex.Match(ShortenedStateName).Success;
  }

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

  private static string ShortenName(string name, int fnLimit) {
    var loc = TryParseSourceLocation(name);
    if (loc != null) {
      var fn = loc.Filename;
      int idx = fn.LastIndexOfAny(new[] { '\\', '/' });
      if (idx > 0) {
        fn = fn[(idx + 1)..];
      }
      if (fn.Length > fnLimit) {
        fn = fn[..fnLimit] + "..";
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
  private static SourceLocation? TryParseSourceLocation(string name) {
    int par = name.LastIndexOf('(');
    if (par <= 0) {
      return null;
    }
    // var res = new SourceLocation { Filename = name[..par] };
    var words = name[(par + 1)..]
      .Split(',', ')', ':')
      .Where(x => x != "")
      .ToArray();
    if (words.Length < 2) {
      return null;
    }
    if (!int.TryParse(words[0], out var line) ||
        !int.TryParse(words[1], out var column)) {
      return null;
    }
    int colon = name.IndexOf(':', par);
    var res = new SourceLocation(
      name[..par],
      colon > 0 ? name[(colon + 1)..].Trim() : "",
      line,
      column);
    return res;
  }

  private class SourceLocation {
    public readonly string Filename;
    public readonly string AddInfo;
    public readonly int Line;
    public readonly int Column;

    public SourceLocation(string filename, string addInfo, int line, int column) {
      Filename = filename;
      AddInfo = addInfo;
      Line = line;
      Column = column;
    }
  }

}