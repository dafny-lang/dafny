using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;

namespace DafnyTestGeneration {

  /// <summary> Allows converting a counterexample to a test method </summary>
  public class TestMethod {

    private static int nextId; // next unique id to be assigned

    // maps a basic type (int, real, bv4, etc.) to the set of values that
    // the model assigns to variables of this type. Values are represented
    // as integers. For conversion rules, see GetUnspecifiedValue method.
    private readonly Dictionary<string, HashSet<int>> reservedValues = new();
    // maps a particular element to a value reserved for it (see above)
    private readonly Dictionary<Model.Element, int> reservedValuesMap = new();
    // list of values to mock together with their types
    public readonly List<(string id, DafnyModelType type)> ObjectsToMock = new();
    // maps a variable that is mocked to its unique id
    private readonly Dictionary<DafnyModelVariable, string> mockedVarId = new();
    public readonly List<(string parentId, string fieldName, string childId)> Assignments = new();
    private readonly int id = nextId++;
    public readonly DafnyInfo DafnyInfo;
    // name of the method for which the counterexample is generated
    public readonly string MethodName;
    // values of the arguments to be passed to the method call
    public readonly List<string> ArgValues;

    public TestMethod(DafnyInfo dafnyInfo, string log) {
      DafnyInfo = dafnyInfo;
      var typeNames = ExtractPrintedInfo(log, "Types | ");
      var argumentNames = ExtractPrintedInfo(log, "Impl | ");
      var dafnyModel = DafnyModel.ExtractModel(log);
      MethodName = Utils.GetDafnyMethodName(argumentNames.First());
      argumentNames.RemoveAt(0);
      RegisterReservedValues(dafnyModel.Model);
      ArgValues = ExtractInputs(dafnyModel.States.First(), argumentNames, typeNames);
    }

    /// <summary>
    /// Extract values that certain elements have at a certain state in the
    /// model.
    /// </summary>
    /// <param name="state"> DafnyModelState to work with</param>
    /// <param name="printOutput"> Output of print command for each element.
    /// This can either be a value of a basic type ("1.0", "false", etc.),
    /// a reference to an element ("T@U!val!25", etc.) or an empty string,
    /// which means that one has to come up with a value based on its
    /// type alone </param>
    /// <param name="types">the types of the elements</param>
    /// <returns></returns>
    private List<string> ExtractInputs(DafnyModelState state, IReadOnlyList<string> printOutput, IReadOnlyList<string> types) {
      var result = new List<string>();
      var vars = state.ExpandedVariableSet(null);
      for (var i = 0; i < printOutput.Count; i++) {
        if (printOutput[i] == "") {
          result.Add(GetDefaultValue(DafnyModelType.FromString(types[i])));
          continue;
        }
        if (!printOutput[i].StartsWith("T@")) {
          if (Regex.IsMatch(printOutput[i], "^[0-9]+bv[0-9]+$")) {
            var baseIndex = printOutput[i].IndexOf('b');
            result.Add($"({printOutput[i][..baseIndex]} as {printOutput[i][baseIndex..]})");
          } else {
            result.Add(printOutput[i]);
          }
          continue;
        }
        foreach (var variable in vars) {
          if ((variable.Element as Model.Uninterpreted)?.Name != printOutput[i]) {
            continue;
          }
          result.Add(ExtractVariable(variable));
          break;
        }
      }
      return result;
    }

    /// <summary>
    /// Extract the value of a variable. This can have side-effects on
    /// assignments, reservedValues, reservedValuesMap, and objectsToMock.
    /// </summary>
    private string ExtractVariable(DafnyModelVariable variable) {
      if (mockedVarId.ContainsKey(variable)) {
        return mockedVarId[variable];
      }

      if (variable.Value.StartsWith("?")) {
        return GetUnspecifiedValue(variable.Type, variable.Element);
      }

      if (variable is DuplicateVariable duplicateVariable) {
        return ExtractVariable(duplicateVariable.Original);
      }

      List<string> elements = new();
      switch (variable.Type.Name) {
        case "?":
          return "null";
        case "char":
        case "int":
        case "real":
        case "bool":
        case var bvType when new Regex("^bv[0-9]+$").IsMatch(bvType):
          return variable.Value;
        case "seq":
          var seqVar = variable as SeqVariable;
          if (seqVar?.GetLength() == null) {
            return "[]";
          }
          for (var i = 0; i < seqVar.GetLength(); i++) {
            var element = seqVar[i];
            if (element == null) {
              elements.Add(GetDefaultValue(variable.Type.TypeArgs.First()));
              continue;
            }
            elements.Add(ExtractVariable(element));
          }
          return $"[{string.Join(", ", elements)}]";
        case "set":
          if (!variable.children.ContainsKey("true")) {
            return "{}";
          }
          foreach (var element in variable.children["true"]) {
            elements.Add(ExtractVariable(element));
          }
          return $"{{{string.Join(", ", elements)}}}";
        case "map":
          var mapVar = variable as MapVariable;
          List<string> mappingStrings = new();
          foreach (var mapping in mapVar?.Mappings ?? new()) {
            mappingStrings.Add($"{ExtractVariable(mapping.Key)} := {ExtractVariable(mapping.Value)}");
          }
          return $"map[{string.Join(", ", mappingStrings)}]";
        case var arrType when new Regex("^_System.array[0-9]*\\?$").IsMatch(arrType):
          break;
        default:
          var varId = $"v{ObjectsToMock.Count}";
          var dafnyType =
            new DafnyModelType(variable.Type.GetNonNullable().InDafnyFormat().ToString());
          ObjectsToMock.Add(new(varId, dafnyType));
          mockedVarId[variable] = varId;
          foreach (var filedName in variable.children.Keys) {
            if (variable.children[filedName].Count != 1) {
              continue;
            }
            Assignments.Add(new(varId, filedName, ExtractVariable(variable.children[filedName].First())));
          }
          return varId;
      }
      return "null";
    }

    /// <summary>
    /// Return a value that is unique to the given element among elements
    /// of a particular type. The value must be of a basic type.
    /// </summary>
    /// <param name="type"></param>
    /// <param name="element"></param>
    /// <returns></returns>
    private string GetUnspecifiedValue(DafnyModelType type, Model.Element element) {
      var value = GetUnspecifiedValue(type.Name, element);
      return type.Name switch {
        "char" => $"'{Convert.ToChar(value)}'",
        "int" => value.ToString(),
        "real" => $"{value}.0",
        "bool" => (value == 1).ToString(),
        var bvType when new Regex("bv[0-9]+$").IsMatch(bvType) =>
          $"({value} as {bvType})",
        _ => "null" // Shouldn't happen
      };
    }

    /// <summary>
    /// Return an integer for a Model.Element, whose value is unspecified.
    /// The integer must be unique among elements that represent values of
    /// the same type. The integer has different meaning depending
    /// on the type of the element, see GetUnspecifiedValue method.
    /// </summary>
    /// <param name="typeName">TypeName of value represented by element</param>
    /// <param name="element"></param>
    /// <returns></returns>
    private int GetUnspecifiedValue(string typeName, Model.Element element) {
      if (reservedValuesMap.ContainsKey(element)) {
        return reservedValuesMap[element];
      }

      if (!reservedValues.ContainsKey(typeName)) {
        reservedValues[typeName] = new();
      }

      // 33 is the first non special character (excluding space)
      var i = typeName == "char" ? 33 : 0;
      while (reservedValues[typeName].Contains(i)) {
        i++;
      }

      reservedValues[typeName].Add(i);
      reservedValuesMap[element] = i;
      return i;
    }

    /// <summary>
    /// Return the default value for a variable of a particular type.
    /// Note that default value is different from unspecified value.
    /// An unspecified value is such a value for which a model does reserve
    /// an element (e.g. T@U!val!25).
    /// </summary>
    private string GetDefaultValue(DafnyModelType type) {
      var result = type.Name switch {
        "char" => "\'a\'",
        "bool" => "false",
        "int" => "0",
        "real" => "0.0",
        "seq" => "[]",
        "set" => "{}",
        "map" => "map[]",
        var bv when new Regex("^bv[0-9]+$").IsMatch(bv) => $"(0 as {bv})",
        var nullable when new Regex("^.*?$").IsMatch(nullable) => "null",
        _ => null
      };
      if (result != null) {
        return result;
      }
      // this should only be reached if the type is non-nullable
      var varId = $"v{ObjectsToMock.Count}";
      ObjectsToMock.Add(new(varId, type));
      return varId;
    }

    /// <summary>
    /// Registered all values of basicTypes specified by the model in
    /// the reservedValues map;
    /// </summary>
    private void RegisterReservedValues(Model model) {
      var fCharToInt = model.MkFunc("char#ToInt", 1);
      reservedValues["char"] = new();
      foreach (var app in fCharToInt.Apps) {
        reservedValues["char"].Add(((Model.Integer)app.Result).AsInt());
      }

      var fU2Int = model.MkFunc("U_2_int", 1);
      reservedValues["int"] = new();
      foreach (var app in fU2Int.Apps) {
        // this skips negative values
        if (app.Result is Model.Integer) {
          reservedValues["int"].Add(app.Result.AsInt());
        }
      }

      var fU2Bool = model.MkFunc("U_2_bool", 1);
      reservedValues["bool"] = new();
      foreach (var app in fU2Bool.Apps) {
        reservedValues["bool"].Add(((Model.Boolean)app.Result).Value ? 1 : 0);
      }

      var fU2Real = model.MkFunc("U_2_real", 1);
      reservedValues["real"] = new();
      foreach (var app in fU2Real.Apps) {
        var resultAsString = app.Result.ToString() ?? "";
        // this skips fractions and negative values
        if (app.Result is Model.Real && resultAsString.Contains("/")) {
          reservedValues["real"].Add(int.Parse(Regex.Replace(
            resultAsString, "\\.0$", "")));
        }
      }

      foreach (var func in model.Functions) {
        if (!Regex.IsMatch(func.Name, "^U_2_bv[0-9]+$")) {
          continue;
        }

        var type = func.Name[4..];
        if (!reservedValues.ContainsKey(type)) {
          reservedValues[type] = new();
        }

        foreach (var app in func.Apps) {
          reservedValues[type].Add(((Model.BitVector)app.Result).AsInt());
        }
      }
    }

    /// <summary>
    /// Extract output of an "assume {:print ...} true;"  statement.
    /// </summary>
    /// <param name="log">the counterexample log as a string</param>
    /// <param name="prefix">the prefix of the print statement such as
    /// "Types" or "Impl" - these come from ProgramModifier</param>
    private static List<string> ExtractPrintedInfo(string log, string prefix) {
      var lines = log.Split("\n");
      foreach (var line in lines) {
        if (!line.StartsWith(prefix)) {
          continue;
        }

        var result = line.Split("|").ToList();
        result.RemoveAt(0);
        for (var i = 0; i < result.Count; i++) {
          result[i] = Regex.Replace(result[i],
            "/ *([0-9]+\\.[0-9]+) +([0-9]+\\.[0-9]+)", "$1/$2");
          result[i] = Regex.Replace(result[i], "[)( \\\\]", "");
        }

        return result;
      }

      return new List<string>();
    }

    /// <summary>  Return the test method as a list of lines of code </summary>
    private List<string> TestMethodLines() {

      List<string> lines = new();

      // test method parameters and declaration:
      var parameters = string.Join(", ", ObjectsToMock
        .Select(kVPair => $"{kVPair.id}:{kVPair.type}"));
      var returnParNames = new List<string>();
      for (var i = 0; i < DafnyInfo.GetReturnTypes(MethodName).Count; i++) {
        returnParNames.Add("r" + i);
      }

      var returnsDeclaration = string.Join(", ",
        Enumerable.Range(0, returnParNames.Count).Select(i =>
            $"{returnParNames[i]}:{DafnyInfo.GetReturnTypes(MethodName)[i]}"));
      var modifiesClause = string.Join("",
        ObjectsToMock.Select(i => $" modifies {i.id}"));
      lines.Add($"method test{id}({parameters}) " +
                $"returns ({returnsDeclaration}) {modifiesClause} {{");

      // assignments necessary to set up the test case:
      foreach (var assignment in Assignments) {
        lines.Add($"{assignment.parentId}.{assignment.fieldName} := " +
                  $"{assignment.childId};");
      }

      // the method call itself:
      string methodCall;
      if (DafnyInfo.IsStatic(MethodName)) {
        methodCall = $"{MethodName}({string.Join(", ", ArgValues)});";
      } else {
        var receiver = ArgValues[0];
        ArgValues.RemoveAt(0);
        methodCall = $"{receiver}.{MethodName.Split(".").Last()}" +
                     $"({string.Join(", ", ArgValues)});";
        ArgValues.Insert(0, receiver);
      }

      var returnValues = "";
      if (returnParNames.Count != 0) {
        returnValues = string.Join(", ", returnParNames) + " := ";
      }

      lines.Add(returnValues + methodCall);
      lines.Add("}");

      return lines;
    }

    public override string ToString() {
      return string.Join("\n", TestMethodLines());
    }

    public override int GetHashCode() {
      var lines = TestMethodLines();
      lines.RemoveAt(0);
      var hashCode = string.Join("", lines).GetHashCode();
      return hashCode;
    }

    public override bool Equals(object? obj) {
      if (obj is not TestMethod other) {
        return false;
      }
      var otherLines = other.TestMethodLines();
      var lines = TestMethodLines();
      lines.RemoveAt(0);
      otherLines.RemoveAt(0);
      return string.Join("", lines) == string.Join("", otherLines);
    }
  }
}