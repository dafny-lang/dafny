#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;
using MapType = Microsoft.Dafny.MapType;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  /// <summary> Allows converting a counterexample to a test method </summary>
  public class TestMethod {

    private static int nextId; // next unique id to be assigned

    // list of values to mock together with their types
    // maps a variable that is mocked to its unique id
    private readonly Dictionary<DafnyModelVariable, string> mockedVarId = new();
    public readonly List<(string parentId, string fieldName, string childId)> Assignments = new();
    public readonly List<(string id, Type type, string value)> ValueCreation = new();
    // next id to assign to a variable with given name:
    private Dictionary<string, int> nameToNextId = new();
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
    // List of all types for which a {:synthesize} - annotated method is needed
    // These methods are used to get fresh instances of the corresponding types
    private static readonly List<UserDefinedType> TypesToSynthesize = new();
    // is set to true whenever the tool encounters something it does not support
    private readonly List<string> errorMessages = new();
    // records parameters for GetDefaultValue call - this is used to to
    // terminate potential infinite recursion
    private List<string> getDefaultValueParams = new();
    // similar to above but for objects
    private readonly HashSet<string> getClassTypeInstanceParams = new();
    private Dictionary<string, string> defaultValueForType = new();
    // types for which values have already been created with the use of
    // :testConstructor annotated methods
    private readonly HashSet<string> typesAlreadyConstructed = new();

    public TestMethod(DafnyInfo dafnyInfo, string log) {
      DafnyInfo = dafnyInfo;
      var typeNames = ExtractPrintedInfo(log, "Types | ");
      var argumentNames = ExtractPrintedInfo(log, "Impl | ");
      dafnyModel = DafnyModel.ExtractModel(dafnyInfo.Options, log);
      MethodName = argumentNames.First();
      argumentNames.RemoveAt(0);
      NOfTypeArgs = dafnyInfo.GetTypeArgs(MethodName).Count;
      ArgValues = ExtractInputs(dafnyModel.States.First(), argumentNames, typeNames);
    }

    public bool IsValid => errorMessages.Count == 0;

    public static void ClearTypesToSynthesize() {
      TypesToSynthesize.Clear();
    }

    /// <summary>
    /// Add a tuple to the ValueCreation list with a given type and value.
    /// The name of the variable assigned to the value is chosen so that it is
    /// unique and begins with the name of the type. Return that name.
    /// </summary>
    private string AddValue(Type type, string value) {
      var name = Regex.Replace(type.ToString().Split(".").Last().Split(" ")[0], "[^a-zA-Z]", "");
      if (name == "") {
        name = "v";
      }
      name = name[0].ToString().ToLower() + name[1..];
      if (!nameToNextId.ContainsKey(name)) {
        nameToNextId[name] = 0;
      }
      name += nameToNextId[name]++;
      ValueCreation.Add((name, type, value));
      return name;
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
    public static string EmitSynthesizeMethods(DafnyInfo dafnyInfo) {
      var result = "";
      // ensures that duplicate types in TypesToSynthesize are skipped:
      HashSet<string> emittedTypes = new();
      foreach (var typ in TypesToSynthesize) {
        var typeString = typ.ToString();
        if (emittedTypes.Contains(typeString)) {
          continue;
        }
        emittedTypes.Add(typeString);
        var methodName = GetSynthesizeMethodName(typeString);
        var returnName = "o";
        if (dafnyInfo.IsTrait(typ)) {
          var types = dafnyInfo.GetTypesForTrait(typ);
          int id = 0;
          var typeToNameDict = new Dictionary<string, string>();
          foreach (var resultTyp in types) {
            typeToNameDict[resultTyp.ToString()] = "o_res_" + id++;
          }
          typeToNameDict[typeString] = "o";
          result += $"\nmethod {{:synthesize}} {methodName}(" +
                    $"{string.Join(",", types.ConvertAll(t => $"{typeToNameDict[t.ToString()]}:{t}"))})" +
                    $"returns ({returnName}:{typeString}) ensures fresh({returnName}) " +
                    $"{string.Join(" ", dafnyInfo.GetEnsuresForTrait(typ, returnName, typeToNameDict))}";
        } else {
          var constFields = dafnyInfo.GetNonGhostFields(typ)
            .Where(field => !field.mutable).ToList();
          while (constFields.Any(field => field.name == returnName)) {
            returnName += "o";
          }

          var parameters = string.Join(", ",
            constFields.Select(field => $"{field.name}:{field.type}"));
          var ensures = string.Join(" ",
            constFields.Select(field =>
              $"ensures {returnName}.{field.name}=={field.name}"));
          result += $"\nmethod {{:synthesize}} {methodName}({parameters}) " +
                    $"returns ({returnName}:{typeString}) ensures fresh({returnName}) " +
                    $"{ensures}";
        }
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
      var vars = state.ExpandedVariableSet(-1);
      var parameterIndex = DafnyInfo.IsStatic(MethodName) ? -1 : -2;
      for (var i = 0; i < printOutput.Count; i++) {
        if (types[i] == "Ty") {
          continue; // this means that this parameter is a type variable
        }
        parameterIndex++;
        Type type;
        if (parameterIndex >= 0) {
          type = Utils.UseFullName(
            DafnyInfo.GetFormalsTypes(MethodName)[parameterIndex]);
          type = Utils.CopyWithReplacements(type,
            DafnyInfo.GetTypeArgsWithParents(MethodName).ConvertAll(arg => arg.ToString()),
            Enumerable.Repeat(defaultType, DafnyInfo.GetTypeArgsWithParents(MethodName).Count).ToList());
          type = DafnyModelTypeUtils.ReplaceType(type,
            _ => true,
            type => DafnyInfo.GetSupersetType(type) != null && type.Name.StartsWith("_System") ?
              new UserDefinedType(type.tok, type.Name[8..], type.TypeArgs) :
              new UserDefinedType(type.tok, type.Name, type.TypeArgs));
        } else {
          type = null;
        }
        if (printOutput[i] == "") {
          getDefaultValueParams = new();
          result.Add(GetDefaultValue(type, type));
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
          result.Add(GetPrimitiveAsType(baseValue, type));
          continue;
        }
        foreach (var variable in vars) {
          if ((variable.Element as Model.Uninterpreted)?.Name != printOutput[i]) {
            continue;
          }
          result.Add(ExtractVariable(variable, type));
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
      type = (ArrowType)DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      getDefaultValueParams = new();
      var lambda =
        $"({string.Join(",", type.TypeArgs.SkipLast(1).Select((t, i) => "a" + i + ":" + t))})" + // parameter types
        "=>" + // return type
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
    private string ExtractVariable(DafnyModelVariable variable, Type/*?*/ asType) {
      if (variable == null) {
        if (asType != null) {
          return GetDefaultValue(asType);
        } else {
          errorMessages.Add("// Failed: variable and type are null");
          return "";
        }
      }
      if (asType != null) {
        asType = DafnyModelTypeUtils.ReplaceType(asType,
          type => DafnyInfo.GetSupersetType(type) != null &&
                  type.Name.StartsWith("_System"),
          type => new UserDefinedType(type.tok, type.Name[8..], type.TypeArgs));
      }
      if (mockedVarId.ContainsKey(variable)) {
        return mockedVarId[variable];
      }

      if (variable is DuplicateVariable duplicateVariable) {
        return ExtractVariable(duplicateVariable.Original, asType);
      }

      if (variable.Type.ToString().Contains("_System.Tuple") ||
          (asType?.ToString() ?? "").Contains("_System.Tuple")) {
        errorMessages.Add("// Failed - temporary disable tuple support");
        return "";
      }

      List<string> elements = new();
      var variableType = DafnyModelTypeUtils.GetInDafnyFormat(
        DafnyModelTypeUtils.ReplaceTypeVariables(variable.Type, defaultType));
      variableType = DafnyModelTypeUtils.ReplaceType(variableType,
        type => DafnyInfo.GetSupersetType(type) != null &&
                type.Name.StartsWith("_System"),
        type => new UserDefinedType(type.tok, type.Name[8..], type.TypeArgs));
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
          return GetPrimitiveAsType(variable.Value, asType);
        case SeqType seqType:
          var asBasicSeqType = GetBasicType(asType, type => type is SeqType) as SeqType;
          var seqVar = variable as SeqVariable;
          if (seqVar?.GetLength() == -1) {
            return AddValue(asType ?? variableType, seqType.Arg is CharType ? "\"\"" : "[]");
          }
          for (var i = 0; i < seqVar?.GetLength(); i++) {
            var element = seqVar?[i];
            if (element == null) {
              getDefaultValueParams = new();
              elements.Add(GetDefaultValue(seqType.Arg, asBasicSeqType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
              continue;
            }
            elements.Add(ExtractVariable(element, asBasicSeqType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
          }

          //
          // Work around stack overflow issue that can occur in Dafny when trying to construct large strings.
          // Only apply this for strings i.e. sequences of characters.
          //
          const int chunksize = 100;
          if (seqType.Arg is CharType && elements.Count > chunksize) {
            int i = 0;
            var chunkStrs = new List<string>();
            while (i < elements.Count) {
              int count = Math.Min(chunksize, elements.Count - i);
              string chunk = "\"" + string.Join("", elements.GetRange(i, count)).Replace("'", "") + "\"";
              chunkStrs.Add(chunk);
              i += chunksize;
            }
            return string.Join("+", chunkStrs);
          }


          return AddValue(asType ?? variableType, seqType.Arg is CharType
            ? $"\"{string.Join("", elements.SelectMany(c => c[1..^1]))}\""
            : $"[{string.Join(", ", elements)}]");
        case SetType:
          var asBasicSetType = GetBasicType(asType, type => type is SetType) as SetType;
          if (!variable.Children.ContainsKey("true")) {
            return AddValue(asType ?? variableType, "{}");
          }
          foreach (var element in variable.Children["true"]) {
            elements.Add(ExtractVariable(element, asBasicSetType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
          }
          return AddValue(asType ?? variableType, $"{{{string.Join(", ", elements)}}}");
        case MapType:
          var asBasicMapType = GetBasicType(asType, type => type is MapType) as MapType;
          var mapVar = variable as MapVariable;
          List<string> mappingStrings = new();
          foreach (var mapping in mapVar?.Mappings ?? new()) {
            var asTypeTypeArgs =
              asBasicMapType?.TypeArgs?.Count == 2 ? asBasicMapType.TypeArgs : null;
            mappingStrings.Add($"{ExtractVariable(mapping.Key, asTypeTypeArgs?[0])} := {ExtractVariable(mapping.Value, asTypeTypeArgs?[1])}");
          }
          return AddValue(asType ?? variableType, $"map[{string.Join(", ", mappingStrings)}]");
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_System.Tuple") || tupleType.Name.StartsWith("_System._tuple"):
          errorMessages.Add("// Failed - tuples are not fully supported");
          return AddValue(DafnyModel.UnknownType, "(" +
            string.Join(",", variable.Children.Values
              .Select(v => ExtractVariable(v.First(), null))) + ")");
        case DafnyModelTypeUtils.DatatypeType dataType:
          if (variable.CanonicalName() == "") {
            getDefaultValueParams = new();
            return GetDefaultValue(dataType, asType);
          }

          var basicType = GetBasicType(asType ?? dataType,
            type => type == null || type is not UserDefinedType definedType ||
                    DafnyInfo.Datatypes.ContainsKey(definedType
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
            if (!variable.Children.ContainsKey(fieldName)) {
              fieldName = $"[{i}]";
            }

            if (!variable.Children.ContainsKey(fieldName)) {
              errorMessages.Add($"// Failed: Cannot find destructor " +
                                $"{ctor.Destructors[i].Name} of constructor " +
                                $"{variable.CanonicalName()} for datatype " +
                                $"{basicType}");
              return basicType.ToString();
            }

            var destructorType = Utils.CopyWithReplacements(
              Utils.UseFullName(ctor.Destructors[i].Type),
              ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), basicType.TypeArgs);
            destructorType = DafnyModelTypeUtils.ReplaceType(destructorType,
              _ => true,
              t => DafnyInfo.Datatypes.ContainsKey(t.Name)
                ? new DafnyModelTypeUtils.DatatypeType(t)
                : new UserDefinedType(t.tok, t.Name, t.TypeArgs));
            fields.Add(ctor.Destructors[i].Name + ":=" +
                       ExtractVariable(variable.Children[fieldName].First(), destructorType));
          }

          var value = basicType.ToString();
          if (fields.Count == 0) {
            value += "." + variable.CanonicalName();
          } else {
            value += "." + variable.CanonicalName() + "(" +
                     string.Join(",", fields) + ")";
          }
          return AddValue(asType ?? dataType, value);
        case ArrowType arrowType:
          var asBasicArrowType = GetBasicType(asType, type => type is ArrowType) as ArrowType;
          return GetFunctionOfType(asBasicArrowType ?? arrowType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          if (asType != null) {
            return GetDefaultValue(asType, asType);
          }
          errorMessages.Add($"// Failed to determine a variable type (element {variable.Element}).");
          return "null";
        case UserDefinedType arrType when new Regex("^_System.array[0-9]*\\?$").IsMatch(arrType.Name):
          errorMessages.Add($"// Failed because arrays are not yet supported (type {arrType} element {variable.Element})");
          break;
        case UserDefinedType _ when variable.CanonicalName() == "null":
          return "null";
        case UserDefinedType userDefinedType:
          return GetClassTypeInstance(userDefinedType, asType, variable);
      }
      errorMessages.Add($"// Failed because variable has unknown type {variableType} (element {variable.Element})");
      return "null";
    }

    private string GetTraitTypeInstance(UserDefinedType type) {
      var typesToInitialize = DafnyInfo.GetTypesForTrait(type);
      foreach (var typ in typesToInitialize) {
        defaultValueForType[typ.ToString()] = GetDefaultValue(typ, typ);
      }
      TypesToSynthesize.Add(type);
      return AddValue(type,
        $"{GetSynthesizeMethodName(type.ToString())}(" +
        $"{string.Join(", ", typesToInitialize.ConvertAll(typ => defaultValueForType[typ.ToString()]))})");
    }

    private string GetClassTypeInstance(UserDefinedType type, Type/*?*/ asType, DafnyModelVariable/*?*/ variable) {
      var asBasicType = GetBasicType(asType, _ => false);
      if ((asBasicType != null) && (asBasicType is not UserDefinedType)) {
        return GetDefaultValue(asType, asType);
      }
      string varId;
      var dafnyType = DafnyModelTypeUtils.GetNonNullable(asBasicType ?? type) as UserDefinedType;
      if ((variable == null || (variable.Children.Count == 0 &&
                                !typesAlreadyConstructed.Contains(dafnyType.ToString())))) {
        // this value is unconstrained by counterexample
        var constructorMethod = DafnyInfo.GetUserDefinedConstrutor(dafnyType);
        if (variable != null) {
          // constructor methods have no guarantee of returning a fresh value, 
          // so one may only use it once to create a value constrained by
          // the counterexample
          typesAlreadyConstructed.Add(dafnyType.ToString());
        }
        if (constructorMethod != null) {
          varId = AddValue(dafnyType, constructorMethod);
          return varId;
        }
      }
      if (getClassTypeInstanceParams.Contains(dafnyType.ToString())) {
        errorMessages.Add(
          $"// Failed to find a non-recursive way of constructing value (type {dafnyType})");
        return "null";
      }
      getClassTypeInstanceParams.Add(dafnyType.ToString());
      if (DafnyInfo.IsTrait(dafnyType)) {
        var tmp = GetTraitTypeInstance(dafnyType);
        getClassTypeInstanceParams.Remove(dafnyType.ToString());
        if (variable != null) {
          mockedVarId[variable] = tmp;
        }
        return tmp;
      }
      if (DafnyInfo.IsExtern(dafnyType)) {
        var ctor = DafnyInfo.GetConstructor(dafnyType);
        if (ctor == null) {
          errorMessages.Add($"// Failed to find constructor for extern class {dafnyType}");
          return "null";
        }
        var constructorArgs = new List<string>();
        foreach (var argType in ctor.Ins.Select(formal => formal.Type)) {
          var processedType = Utils.CopyWithReplacements(
            Utils.UseFullName(argType),
            ctor.EnclosingClass.TypeArgs.ConvertAll(arg => arg.Name), dafnyType.TypeArgs);
          constructorArgs.Add(GetDefaultValue(processedType));
        }
        var ctorName = ctor.EnclosingClass.FullDafnyName + (ctor.HasName ? ctor.Name : "");
        varId = AddValue(dafnyType,
          $"new {ctorName}({string.Join(", ", constructorArgs)})");
      } else {
        var constFieldValues = new List<string>();
        var immutableFields = DafnyInfo.GetNonGhostFields(dafnyType)
          .Where(field => !field.mutable);
        foreach (var field in
                 immutableFields) {
          constFieldValues.Add(GetFieldValue(field, variable));
        }
        TypesToSynthesize.Add(dafnyType);
        varId = AddValue(dafnyType, $"{GetSynthesizeMethodName(dafnyType.ToString())}({string.Join(", ", constFieldValues)})");
      }
      getClassTypeInstanceParams.Remove(dafnyType.ToString());
      if (variable != null) {
        mockedVarId[variable] = varId;
      }
      var mutableFields = DafnyInfo.GetNonGhostFields(dafnyType)
        .Where(field => field.mutable);
      foreach (var field in mutableFields) {
        Assignments.Add(new(varId, field.name, GetFieldValue(field, variable)));
      }
      return varId;
    }

    private string GetFieldValue((string name, Type type, bool mutable, string/*?*/ defValue) field, DafnyModelVariable/*?*/ variable) {
      if (field.defValue != null) {
        return field.defValue;
      }
      if (variable != null && variable.Children.ContainsKey(field.name) &&
          variable.Children[field.name].Count == 1) {
        return ExtractVariable(variable.Children[field.name].First(), null);
      }
      if (ValueCreation.Any(obj => obj.type == field.type)) {
        return ValueCreation.First(obj => obj.type == field.type).id;
      }
      return GetDefaultValue(field.type, field.type);
    }

    private static string GetPrimitiveAsType(string value, Type/*?*/ asType) {
      if ((asType is null or IntType or RealType or BoolType or CharType
          or BitvectorType) || value is "[]" or "{}" or "map[]") {
        return value;
      }
      var typeString = asType.ToString();
      if (typeString.StartsWith("_System.")) {
        typeString = typeString[8..];
      }
      return $"({value} as {typeString})";
    }

    /// <summary>
    /// Return the default value for a variable of a particular type.
    /// Note that default value is different from unspecified value.
    /// An unspecified value is such a value for which a model does reserve
    /// an element (e.g. T@U!val!25).
    /// </summary>
    private string GetDefaultValue(Type type, Type/*?*/ asType = null) {
      if (type == null) {
        errorMessages.Add("// Failed - cannot determine type");
        return "";
      }
      if (type.ToString().Contains("_System.Tuple") ||
          (asType?.ToString() ?? "").Contains("_System.Tuple")) {
        errorMessages.Add("// Failed - temporary disable tuple support");
        return "";
      }
      type = GetBasicType(type, type => DafnyInfo.GetSupersetType(type) == null);
      type = DafnyModelTypeUtils.ReplaceType(type,
        _ => true,
        t => DafnyInfo.Datatypes.ContainsKey(t.Name) ?
          new DafnyModelTypeUtils.DatatypeType(t) :
          new UserDefinedType(t.tok, t.Name, t.TypeArgs));
      type = DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      if ((asType != null) && (DafnyInfo.GetWitnessForType(asType) != null)) {
        return DafnyInfo.GetWitnessForType(asType);
      }
      switch (type) {
        case IntType:
          return GetPrimitiveAsType("0", asType);
        case RealType:
          return GetPrimitiveAsType("0.0", asType);
        case BoolType:
          return GetPrimitiveAsType("false", asType);
        case CharType:
          return GetPrimitiveAsType("\'a\'", asType);
        case BitvectorType bitvectorType:
          return GetPrimitiveAsType($"(0 as bv{bitvectorType.Width})", asType);
        case SeqType seqType:
          return AddValue(asType ?? type, seqType.Arg is CharType ? "\"\"" : "[]");
        case SetType:
          return AddValue(asType ?? type, "{}");
        case MapType mapType:
          return AddValue(asType ?? type, mapType.Finite ? "map[]" : "imap[]");
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_System.Tuple") || tupleType.Name.StartsWith("_System._tuple"):
          errorMessages.Add("// Failed - temporary disable tuple support");
          var destructors = new List<string>();
          foreach (var arg in tupleType.TypeArgs) {
            destructors.Add(GetDefaultValue(arg));
          }
          return AddValue(tupleType, "(" + string.Join(",", destructors) + ")");
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
            var assignments = ctor.Destructors.Select(destructor =>
              destructor.Name + ":=" + GetDefaultValue(
                Utils.CopyWithReplacements(Utils.UseFullName(destructor.Type),
                    ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), datatypeType.TypeArgs),
                Utils.CopyWithReplacements(Utils.UseFullName(destructor.Type),
                  ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), datatypeType.TypeArgs)));
            value = datatypeType + "." + ctor.Name + "(" +
                   string.Join(",", assignments) + ")";
          }
          var name = AddValue(asType ?? datatypeType, value);
          getDefaultValueParams.RemoveAt(getDefaultValueParams.Count - 1);
          return name;

        case ArrowType arrowType:
          return GetFunctionOfType(arrowType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          errorMessages.Add($"// Failed to determine type of a default value");
          return "null";
        case UserDefinedType userDefinedType when userDefinedType.Name.EndsWith("?"):
          return "null";
        case UserDefinedType userDefinedType:
          return GetClassTypeInstance(userDefinedType, asType, null);
      }
      errorMessages.Add(
        $"// Failed to extract default value for type " + type ?? "(null)");
      return "null";
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

    /// <summary>  Return the test input as a list of lines of code </summary>
    public List<string> TestInputConstructionLines() {
      List<string> lines = new();

      foreach (var line in ValueCreation) {
        if (line.type is UserDefinedType userDefinedType && (userDefinedType.Name.StartsWith("_System.Tuple") || userDefinedType.Name.StartsWith("_System._tuple"))) {
          lines.Add($"var {line.id}: " +
                    $"({string.Join(",", line.type.TypeArgs.ConvertAll(typ => typ.ToString()))}) " +
                    $":= {line.value};");
        } else {
          lines.Add($"var {line.id} : {line.type} := {line.value};");
          var subsetTypeCondition = DafnyInfo.GetTypeCondition(line.type, line.id);
          if (subsetTypeCondition != null) {
            lines.Add("expect " + Printer.ExprToString(DafnyInfo.Options, subsetTypeCondition) +
                      ", \"Test does not meet type constraints and should be removed\";");
          }
        }
      }

      // assignments necessary to set up the test case:
      foreach (var assignment in Assignments) {
        lines.Add($"{assignment.parentId}.{assignment.fieldName} := " +
                  $"{assignment.childId};");
      }

      return lines;
    }

    /// <summary>  Return the test method as a list of lines of code </summary>
    private List<string> TestMethodLines() {

      List<string> lines = new();

      if (errorMessages.Count != 0) {
        if (DafnyInfo.Options.TestGenOptions.Verbose) {
          lines.AddRange(errorMessages);
        }
        return lines;
      }

      var returnParNames = new List<string>();
      for (var i = 0; i < DafnyInfo.GetReturnTypes(MethodName).Count; i++) {
        returnParNames.Add("r" + i);
      }

      lines.Add($"method {{:test}} test{id}() {{");

      lines.AddRange(TestInputConstructionLines());

      string receiver = "";
      if (!DafnyInfo.IsStatic(MethodName)) {
        receiver = ArgValues[0];
        ArgValues.RemoveAt(0);
      }

      lines.AddRange(DafnyInfo.GetRequires(ArgValues,
        MethodName,
        receiver).Select(e =>
        "expect " + Printer.ExprToString(DafnyInfo.Options, e) +
        ", \"Test does not meet preconditions and should be removed\";"));
      if (!DafnyInfo.IsStatic(MethodName)) {
        ArgValues.Insert(0, receiver);
      }

      // the method call itself:
      var typeArguments = "";
      if (NOfTypeArgs > 0) {
        typeArguments = "<" + string.Join(",", Enumerable.Repeat(defaultType.ToString(), NOfTypeArgs)) + ">";
      }
      string methodCall;
      if (DafnyInfo.IsStatic(MethodName)) {
        methodCall = $"{MethodName}{typeArguments}({string.Join(", ", ArgValues)});";
      } else {
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


      lines.AddRange(DafnyInfo.GetEnsures(ArgValues,
        returnParNames,
        MethodName,
        receiver).Select(e => "expect " + Printer.ExprToString(DafnyInfo.Options, e) + ";"));

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

    public override bool Equals(object/*?*/ obj) {
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