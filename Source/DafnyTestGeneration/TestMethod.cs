using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using MapType = Microsoft.Dafny.MapType;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  /// <summary> Allows converting a counterexample to a test method </summary>
  public class TestMethod {

    private static int nextId; // next unique id to be assigned

    // list of values to mock together with their types
    public readonly List<(string id, Type type)> ObjectsToMock = new();
    // maps a variable that is mocked to its unique id
    private readonly Dictionary<DafnyModelVariable, string> mockedVarId = new();
    public readonly List<(string parentId, string fieldName, string childId)> Assignments = new();
    public readonly List<(string id, Type type, string value)> ValueCreation = new();
    private readonly int id = nextId++;
    public readonly DafnyInfo DafnyInfo;
    // name of the method for which the counterexample is generated
    public readonly string MethodName;
    // values of the arguments to be passed to the method call
    public readonly List<string> ArgValues;
    // number of type arguments for the method (all will be set to defaultType)
    public readonly int NOfTypeArgs;
    // default type to replace any type variable with
    private readonly Type defaultType = Type.Int;
    // the DafnyModel that describes the inputs to this test method
    private readonly DafnyModel dafnyModel;
    // Set of all types for which a {:synthesize} - annotated method is needed
    // These methods are used to get fresh instances of the corresponding types
    private static readonly HashSet<string> TypesToSynthesize = new();
    // is set to true wheneve the tool ecnounters something it does not support
    private readonly List<string> errorMessages = new(); 
    // records parameters for GetDefaultValue call - this is used to to
    // terminate potential infinite recursion
    private List<string> getDefaultValueParams = new();

    public TestMethod(DafnyInfo dafnyInfo, string log) {
      DafnyInfo = dafnyInfo;
      var typeNames = ExtractPrintedInfo(log, "Types | ");
      var argumentNames = ExtractPrintedInfo(log, "Impl | ");
      dafnyModel = DafnyModel.ExtractModel(log);
      MethodName = argumentNames.First();
      argumentNames.RemoveAt(0);
      NOfTypeArgs = dafnyInfo.GetNOfTypeArgs(MethodName);
      ArgValues = ExtractInputs(dafnyModel.States.First(), argumentNames, typeNames);
    }

    public bool IsValid => errorMessages.Count == 0;

    public static void ClearTypesToSynthesize() {
      TypesToSynthesize.Clear();
    }

    /// <summary>
    /// Returns the name given to a {:synthesize} - annotated method that
    /// returns a value of certain type
    /// </summary>
    private static string GetSynthesizeMethodName(string typ) {
      return "getFresh" + Regex.Replace(typ, "[^a-zA-Z]", "");
    }

    /// <summary>
    /// Returns a string that contains all the {:synthesize} annotated methods
    /// necessary to compile the tests
    /// </summary>
    public static string EmitSynthesizeMethods() {
      var result = "";
      foreach (var typ in TypesToSynthesize) {
        var methodName = GetSynthesizeMethodName(typ);
        result += $"\nmethod {{:synthesize}} {methodName}() " +
                  $"returns (o:{typ}) ensures fresh(o)";
      }
      return result;
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
      var parameterIndex = DafnyInfo.IsStatic(MethodName) ? -1 : -2; // TODO: this is wrong
      for (var i = 0; i < printOutput.Count; i++) {
        if (types[i] == "Ty") {
          continue; // this means that this parameter is a type variable
        }
        parameterIndex++;
        if (printOutput[i] == "") {
          getDefaultValueParams = new();
          result.Add(GetDefaultValue(DafnyInfo.GetFormalsTypes(MethodName)[parameterIndex]));
          continue;
        }
        if (!printOutput[i].StartsWith("T@")) {
          string baseValue;
          if (Regex.IsMatch(printOutput[i], "^[0-9]+bv[0-9]+$")) {
            var baseIndex = printOutput[i].IndexOf('b');
            baseValue = $"({printOutput[i][..baseIndex]} as {printOutput[i][baseIndex..]})";
          } else {
            baseValue = printOutput[i];
          }

          var type = DafnyModelTypeUtils.ReplaceTypeVariables(
            DafnyInfo.GetFormalsTypes(MethodName)[parameterIndex],
            defaultType);
          if (type is IntType or RealType or BoolType or BitvectorType) {
            result.Add(baseValue);
          } else {
            var typeString = type.ToString();
            // TODO: find a more elegant solution
            if (typeString.StartsWith("_System.")) {
              typeString = typeString[8..];
            }
            result.Add($"({baseValue} as {typeString})");
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

    // Returns a new value of the defaultType type (set to int by default)
    private string GetADefaultTypeValue(DafnyModelVariable variable) {
      return dafnyModel.GetUnreservedNumericValue(variable.Element, Type.Int);
    }

    private string GetFunctionOfType(ArrowType type) {
      type = (ArrowType) DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      getDefaultValueParams = new();
      var lambda = 
        $"({string.Join(",", type.TypeArgs.SkipLast(1).Select((t, i) => "a" + i + ":" + t))})" + // parameter types
        $"=>" + // return type
        $"{GetDefaultValue(type.TypeArgs.Last())}"; // body
      return lambda;
    }

    /// <summary>
    /// Try to reduce the type from a synonym down to superset type until
    /// a certain condition is met
    /// </summary>
    private Type GetBasicType(Type start, Func<Type, bool> stopCondition) {
      if (!stopCondition(start) &&
             DafnyInfo.GetSupersetType(start) != null) {
        return GetBasicType(
          DafnyInfo.GetSupersetType(start),
          stopCondition);
      }
      return start;
    }

    /// <summary>
    /// Extract the value of a variable. This can have side-effects on
    /// assignments, reservedValues, reservedValuesMap, and objectsToMock.
    /// </summary>
    private string ExtractVariable(DafnyModelVariable variable, Type? asType=null) {
      if (mockedVarId.ContainsKey(variable)) {
        return mockedVarId[variable];
      }

      if (variable is DuplicateVariable duplicateVariable) {
        return ExtractVariable(duplicateVariable.Original, asType);
      }

      List<string> elements = new();
      var variableType = DafnyModelTypeUtils.GetInDafnyFormat(
        DafnyModelTypeUtils.ReplaceTypeVariables(variable.Type, defaultType));
      if (variableType.ToString() == defaultType.ToString() && 
          variableType.ToString() != variable.Type.ToString()) {
        return GetADefaultTypeValue(variable);
      }
      switch (variableType) {
        case IntType:
        case RealType:
        case BoolType:
        case CharType:
        case BitvectorType:
          return variable.Value;
        case SeqType seqType:
          var asBasicSeqType = GetBasicType(asType, type => type is SeqType) as SeqType;
          string seqName;
          var seqVar = variable as SeqVariable;
          if (seqVar?.GetLength() == null) {
            seqName = "d" + ValueCreation.Count;
            ValueCreation.Add((seqName, asType ?? variableType, "[]"));
            return seqName;
          }
          for (var i = 0; i < seqVar.GetLength(); i++) {
            var element = seqVar[i];
            if (element == null) {
              getDefaultValueParams = new();
              elements.Add(GetDefaultValue(seqType.Arg, asBasicSeqType?.TypeArgs?.FirstOrDefault((Type?)null)));
              continue;
            }
            elements.Add(ExtractVariable(element));
          }
          seqName = "d" + ValueCreation.Count;
          ValueCreation.Add((seqName, asType ?? variableType, $"[{string.Join(", ", elements)}]"));
          return seqName;
        case SetType:
          var asBasicSetType = GetBasicType(asType, type => type is SetType) as SetType;
          string setName;
          if (!variable.children.ContainsKey("true")) {
            setName = "d" + ValueCreation.Count;
            ValueCreation.Add((setName, asType ?? variableType, "{}"));
            return setName;
          }
          foreach (var element in variable.children["true"]) {
            elements.Add(ExtractVariable(element, asBasicSetType?.TypeArgs?.FirstOrDefault((Type?)null)));
          }
          setName = "d" + ValueCreation.Count;
          ValueCreation.Add((setName, asType ?? variableType, $"{{{string.Join(", ", elements)}}}"));
          return setName;
        case MapType:
          var asBasicMapType = GetBasicType(asType, type => type is MapType) as MapType;
          var mapVar = variable as MapVariable;
          List<string> mappingStrings = new();
          foreach (var mapping in mapVar?.Mappings ?? new()) {
            var asTypeTypeArgs =
              asBasicMapType?.TypeArgs?.Count == 2 ? asBasicMapType.TypeArgs : null;
            mappingStrings.Add($"{ExtractVariable(mapping.Key, asTypeTypeArgs?[0])} := {ExtractVariable(mapping.Value, asTypeTypeArgs?[1])}");
          }
          var mapName = "d" + ValueCreation.Count;
          ValueCreation.Add((mapName, asType ?? variableType, $"map[{string.Join(", ", mappingStrings)}]"));
          return mapName;
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_System.Tuple"):
          var tupleName = "d" + ValueCreation.Count;
          // TODO: specify type
          ValueCreation.Add((tupleName, DafnyModel.UndefinedType, "(" + 
            string.Join(",", variable.children.Values
            .Select(v => ExtractVariable(v.First()))) +")"));
          return tupleName;
        case DafnyModelTypeUtils.DatatypeType dataType:
          if (variable.CanonicalName() == "") {
            // TODO: Can fields be non-empty in this case?
            getDefaultValueParams = new();
            return GetDefaultValue(dataType, asType);
          }

          var basicType = GetBasicType(asType ?? dataType,
            type => type == null || type is not UserDefinedType ||
                    DafnyInfo.Datatypes.ContainsKey((type as UserDefinedType)
                      .Name)) as UserDefinedType;
          if (basicType == null ||
              !DafnyInfo.Datatypes.ContainsKey(basicType.Name)) {
            errorMessages.Add($"// Failed: Cannot find datatype {dataType} in DafnyInfo");
            return dataType.ToString();
          }
          var ctor = DafnyInfo.Datatypes[basicType.Name].Ctors.FirstOrDefault(ctor => ctor.Name == variable.CanonicalName(), null);
          if (ctor == null) {
            errorMessages.Add($"// Failed: Cannot find constructor {variable.CanonicalName()} for datatype {basicType}");
            return basicType.ToString();
          }
          List<string> fields = new();
          for (int i = 0; i < ctor.Destructors.Count; i++) {
            var fieldName = ctor.Destructors[i].Name;
            if (!variable.children.ContainsKey(fieldName)) {
              fieldName = $"[{i}]";
            }

            if (!variable.children.ContainsKey(fieldName)) {
              errorMessages.Add($"// Failed: Cannot find destructor " +
                                $"{ctor.Destructors[i].Name} of constructor " +
                                $"{variable.CanonicalName()} for datatype " +
                                $"{basicType}");
              return basicType.ToString();
            }

            var destructorType = DafnyModelTypeUtils.CopyWithReplacements(
              DafnyModelTypeUtils.UseFullName(ctor.Destructors[i].Type),
              ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), basicType.TypeArgs);
            destructorType = DafnyModelTypeUtils.ReplaceType(destructorType,
              _ => true,
              t => DafnyInfo.Datatypes.ContainsKey(t.Name)
                ? new DafnyModelTypeUtils.DatatypeType(t)
                : new UserDefinedType(t.tok, t.Name, t.TypeArgs));
            fields.Add(ctor.Destructors[i].Name + ":=" +
                       ExtractVariable(variable.children[fieldName].First(), destructorType));
          }

          var value = basicType.ToString();
          if (fields.Count == 0) {
            value += "." + variable.CanonicalName();
          } else {
            value += "." + variable.CanonicalName() + "(" +
                     string.Join(",", fields) + ")";
          }
          var name = "d" + ValueCreation.Count;
          ValueCreation.Add((name, asType ?? dataType, value));
          return name;
        case ArrowType arrowType:
          var asBasicArrowType = GetBasicType(asType, type => type is ArrowType) as ArrowType;
          return GetFunctionOfType(asBasicArrowType ?? arrowType);
        case UserDefinedType undefined when undefined.Name == DafnyModel.UndefinedType.Name:
          errorMessages.Add($"// Failed to determine a variable type (element {variable.Element})");
          return "null";
        case UserDefinedType arrType when new Regex("^_System.array[0-9]*\\?$").IsMatch(arrType.Name):
          errorMessages.Add($"// Failed because arrays are not yet supported (type {arrType} element {variable.Element})");
          break; 
        case UserDefinedType _ when variable.CanonicalName() == "null":
          return "null";
        default:
          var varId = $"v{ObjectsToMock.Count}";
          var dafnyType = DafnyModelTypeUtils.GetNonNullable(asType ?? variableType);
          ObjectsToMock.Add(new(varId, dafnyType));
          TypesToSynthesize.Add(dafnyType.ToString());
          mockedVarId[variable] = varId;
          foreach (var fieldName in variable.children.Keys) {
            if (variable.children[fieldName].Count != 1) {
              continue;
            }
            Assignments.Add(new(varId, fieldName, ExtractVariable(variable.children[fieldName].First())));
          }
          return varId;
      }
      errorMessages.Add($"// Failed because variable has unknown type {variableType} (element {variable.Element})");
      return "null";
    }

    /// <summary>
    /// Return the default value for a variable of a particular type.
    /// Note that default value is different from unspecified value.
    /// An unspecified value is such a value for which a model does reserve
    /// an element (e.g. T@U!val!25).
    /// </summary>
    private string GetDefaultValue(Type type, Type? asType=null) {
      type = GetBasicType(type, type => DafnyInfo.GetSupersetType(type) == null);
      type = DafnyModelTypeUtils.ReplaceType(type,
        _ => true,
        t => DafnyInfo.Datatypes.ContainsKey(t.Name) ? 
          new DafnyModelTypeUtils.DatatypeType(t) : 
          new UserDefinedType(t.tok, t.Name, t.TypeArgs));
      type = DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      switch (type) {
        case IntType:
          return "0";
        case RealType:
          return "0.0";
        case BoolType:
          return "false";
        case CharType:
          return "\'a\'";
        case BitvectorType bitvectorType:
          return $"(0 as bv{bitvectorType.Width})";
        case SeqType:
          var seqName = "d" + ValueCreation.Count;
          ValueCreation.Add((seqName, asType ?? type, "[]"));
          return seqName;
        case SetType:
          var setName = "d" + ValueCreation.Count;
          ValueCreation.Add((setName, asType ?? type, "{}"));
          return setName;
        case MapType:
          var mapName = "d" + ValueCreation.Count;
          ValueCreation.Add((mapName, asType ?? type, "map[]"));
          return mapName;
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_System.Tuple"):
          // TODO: specify type
          var tupleName = "d" + ValueCreation.Count;
          ValueCreation.Add((tupleName, DafnyModel.UndefinedType, "(" + 
            string.Join(",", tupleType.TypeArgs.Select(arg => GetDefaultValue(arg))) + ")"));
          return tupleName;
        case DafnyModelTypeUtils.DatatypeType datatypeType:
          string value;
          if (getDefaultValueParams.Contains(datatypeType.Name)) {
            errorMessages.Add($"// Failed to non-recursively construct a default value for type {datatypeType}");
            return datatypeType.Name + ".UNKNOWN";
          } 
          if (!DafnyInfo.Datatypes.ContainsKey(datatypeType.Name)) {
            errorMessages.Add($"// Failed to determine default constructors for datatype (type {datatypeType})");
            return datatypeType.Name + ".UNKNOWN";
          }
          getDefaultValueParams.Add(datatypeType.ToString());
          var ctor = DafnyInfo.Datatypes[datatypeType.Name].Ctors.MinBy(ctor => ctor.Destructors.Count);
          if (ctor.Destructors.Count == 0) {
            value = datatypeType + "." + ctor.Name;
          } else {
            var assignemnets = ctor.Destructors.Select(destructor =>
              destructor.Name + ":=" + GetDefaultValue(
                DafnyModelTypeUtils.CopyWithReplacements(DafnyModelTypeUtils.UseFullName(destructor.Type),
                    ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), datatypeType.TypeArgs),
                DafnyModelTypeUtils.CopyWithReplacements(DafnyModelTypeUtils.UseFullName(destructor.Type),
                  ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), datatypeType.TypeArgs)));
            value = datatypeType + "." + ctor.Name + "(" +
                   string.Join(",", assignemnets) + ")";
          }
          var name = "d" + ValueCreation.Count;
          ValueCreation.Add((name, asType ?? datatypeType, value));
          getDefaultValueParams.RemoveAt(getDefaultValueParams.Count - 1);
          return name;
          
        case ArrowType arrowType:
          return GetFunctionOfType(arrowType);
        case UserDefinedType unDefinedType when unDefinedType.Name == DafnyModel.UndefinedType.Name:
          errorMessages.Add($"// Failed to determine type of a default value");
          return "null";
        case UserDefinedType userDefinedType when userDefinedType.Name.EndsWith("?"):
          return "null";
      }
      // this should only be reached if the type is non-nullable
      var varId = $"v{ObjectsToMock.Count}";
      ObjectsToMock.Add(new(varId, type));
      TypesToSynthesize.Add(type.ToString());
      return varId;
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

      if (errorMessages.Count != 0) {
        if (DafnyOptions.O.TestGenOptions.Verbose) {
          lines.AddRange(errorMessages);
        }
        return lines;
      }

      // test method parameters and declaration:
      var mockedLines = ObjectsToMock
        .Select(kVPair => $"var {kVPair.id} := " +
                          $"{GetSynthesizeMethodName(kVPair.type.ToString())}();");
      
      List<string> valueCreation = new();
      foreach (var line in ValueCreation) {
        if (line.type.ToString() == "?") {
          // TODO: This is currently done for tuples
          valueCreation.Add($"var {line.id} := {line.value};");
        } else {
          valueCreation.Add($"var {line.id} : {line.type} := {line.value};");
        }
      }

      var returnParNames = new List<string>();
      for (var i = 0; i < DafnyInfo.GetReturnTypes(MethodName).Count; i++) {
        returnParNames.Add("r" + i);
      }

      lines.Add($"method {{:test}} test{id}() {{");
      lines.AddRange(mockedLines);
      lines.AddRange(valueCreation);

      // assignments necessary to set up the test case:
      foreach (var assignment in Assignments) {
        lines.Add($"{assignment.parentId}.{assignment.fieldName} := " +
                  $"{assignment.childId};");
      }

      // the method call itself:
      var typeArguments = "";
      if (NOfTypeArgs > 0) {
        typeArguments = "<" + string.Join(",", Enumerable.Repeat(defaultType.ToString(), NOfTypeArgs)) + ">";
      }
      string methodCall;
      string receiver = "";
      if (DafnyInfo.IsStatic(MethodName)) {
        methodCall = $"{MethodName}{typeArguments}({string.Join(", ", ArgValues)});";
      } else {
        receiver = ArgValues[0];
        ArgValues.RemoveAt(0);
        methodCall = $"{receiver}.{MethodName.Split(".").Last()}" +
                     $"{typeArguments}({string.Join(", ", ArgValues)});";
        ArgValues.Insert(0, receiver);
      }

      var returnValues = "";
      if (returnParNames.Count != 0) {
        returnValues = "var " + string.Join(", ", returnParNames) + " := ";
      }

      lines.Add(returnValues + methodCall);
      if (!DafnyInfo.IsStatic(MethodName)) {
        ArgValues.RemoveAt(0);
      }

      if (DafnyOptions.O.TestGenOptions.Oracle ==
          TestGenerationOptions.Oracles.Spec) {
        lines.AddRange(DafnyInfo.GetEnsures(ArgValues,
          returnParNames,
          MethodName,
          receiver).Select(e => "expect " + Printer.ExprToString(e) + ";"));
      }

      if (!DafnyInfo.IsStatic(MethodName)) {
        ArgValues.Insert(0, receiver);
      }
      lines.Add("}");

      return lines;
    }

    public override string ToString() {
      return string.Join("\n", TestMethodLines());
    }

    public override int GetHashCode() {
      var lines = TestMethodLines();
      if (lines.Count == 0) {
        return "".GetHashCode();
      }
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
      if (lines.Count != otherLines.Count) {
        return false;
      }
      if (lines.Count == 0) {
        return true;
      }
      lines.RemoveAt(0);
      otherLines.RemoveAt(0);
      return string.Join("", lines) == string.Join("", otherLines);
    }
  }
}