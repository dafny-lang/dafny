// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.Dafny;
using MapType = Microsoft.Dafny.MapType;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using LiteralExpr = Microsoft.Dafny.LiteralExpr;

namespace DafnyTestGeneration {

  /// <summary> Allows converting a counterexample to a test method </summary>
  public class TestMethod {

    private static int nextId; // next unique id to be assigned

    // list of values to mock together with their types
    // maps a variable that is mocked to its unique id
    private readonly Dictionary<PartialValue, string> mockedVarId = new();
    public readonly List<(string parentId, string fieldName, string childId)> Assignments = [];
    public readonly List<(string id, Type type, string value)> ValueCreation = [];
    // next id to assign to a variable with given name:
    private Dictionary<string, int> nameToNextId = new();
    private readonly int id = nextId++;
    public readonly DafnyInfo DafnyInfo;
    // name of the method for which the counterexample is generated
    public readonly string MethodName;
    // values of the arguments to be passed to the method call
    public readonly List<string> ArgValues;
    // expressions of the arguments to be passed to the method call
    public readonly Dictionary<string, Expression> ArgExpressions;
    // expressions of the return values of the method call
    public readonly Dictionary<string, Expression> OutExpressions;
    // number of type arguments for the method (all will be set to defaultType)
    public readonly int NOfTypeArgs;
    // default type to replace any type variable with
    private readonly Type defaultType = Type.Int;
    // the DafnyModel that describes the inputs to this test method
    private readonly DafnyModel dafnyModel;
    // is set to true whenever the tool encounters something it does not support
    private readonly List<string> errorMessages = [];
    // records parameters for GetDefaultValue call - this is used to to
    // terminate potential infinite recursion
    private List<string> getDefaultValueParams = [];
    // similar to above but for objects
    private readonly HashSet<string> getClassTypeInstanceParams = [];
    private readonly Modifications cache;

    private readonly Dictionary<PartialValue, Expression> constraintContext;

    public TestMethod(DafnyInfo dafnyInfo, string log, Modifications cache) {
      DafnyInfo = dafnyInfo;
      this.cache = cache;
      var typeNames = ExtractPrintedInfo(log, "Types | ");
      var argumentNames = ExtractPrintedInfo(log, "Impl | ");
      dafnyModel = DafnyModel.ExtractModel(dafnyInfo.Options, log);
      dafnyModel.AssignConcretePrimitiveValues();
      MethodName = argumentNames.First();
      argumentNames.RemoveAt(0);
      NOfTypeArgs = dafnyInfo.GetTypeArgs(MethodName).Count;
      constraintContext = new Dictionary<PartialValue, Expression>();

      var firstState = dafnyModel.States.First();
      var formalNames = DafnyInfo.GetReturnFormals(MethodName).Select(f => f.Name).ToList();

      List<string> outputValues = Enumerable.Repeat("", formalNames.Count).ToList();
      List<string> outputTypes = Enumerable.Repeat("", formalNames.Count).ToList();

      foreach (var kvn in firstState.KnownVariableNames) {
        var key = kvn.Key;
        var value = kvn.Value;

        constraintContext[key] = new IdentifierExpr(Token.NoToken, firstState.KnownVariableNames[key].First());
        constraintContext[key].Type = key.Type;

        for (int i = 0; i < formalNames.Count; i++) {
          if (value.Contains(formalNames[i])) {
            outputValues[i] = key.Element.ToString().Trim('(', ')').Replace(" ", "");
            outputTypes[i] = key.Type.ToString();
          }
        }
      }
      ArgValues = ExtractInputs(firstState, argumentNames, typeNames);
      ArgExpressions = ExtractExpressions(firstState, argumentNames, typeNames);
      OutExpressions = ExtractExpressions(firstState, outputValues, outputTypes, true);
    }

    public bool IsValid => errorMessages.Count == 0;

    /// <summary>
    /// Add a tuple to the
    /// list with a given type and value.
    /// The name of the variable assigned to the value is chosen so that it is
    /// unique and begins with the name of the type. Return that name.
    /// </summary>
    private string AddValue(Type type, string value) {
      var name = type.IsArrowType ? "arrow" : Regex.Replace(type.ToString().Split(".").Last().Split(" ")[0], "[^a-zA-Z]", "");
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
    public static string EmitSynthesizeMethods(DafnyInfo dafnyInfo, Modifications cache) {
      var result = "";
      // ensures that duplicate types in TypesToSynthesize are skipped:
      HashSet<string> emittedTypes = [];
      foreach (var typ in cache.TypesToSynthesize) {
        var typeString = typ.ToString();
        if (emittedTypes.Contains(typeString)) {
          continue;
        }
        emittedTypes.Add(typeString);
        var methodName = GetSynthesizeMethodName(typeString);
        var returnName = "o";
        if (!dafnyInfo.IsTrait(typ)) {
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
    private List<string> ExtractInputs(PartialState state, IReadOnlyList<string> printOutput, IReadOnlyList<string> types) {
      var result = new List<string>();
      var vars = state.ExpandedVariableSet();
      var constraintSet = new List<Constraint>();
      foreach (var variable in vars) {
        foreach (var constraint in variable.Constraints) {
          constraintSet.Add(constraint);
        }
      }
      var constraints = constraintSet.ToList();
      constraints = Constraint.ResolveAndOrder(constraintContext, constraints, false, false);
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
              new UserDefinedType(type.Origin, type.Name[8..], type.TypeArgs) :
              new UserDefinedType(type.Origin, type.Name, type.TypeArgs));
        } else {
          type = null;
        }
        if (printOutput[i] == "") {
          getDefaultValueParams = [];
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
          result.Add(GetPrimitiveAsType(baseValue, type, type));
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
    private string GetADefaultTypeValue(PartialValue variable) {
      return "0";
    }

    private string GetFunctionOfType(ArrowType type) {
      type = (ArrowType)DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
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
    private string ExtractVariable(PartialValue variable, Type/*?*/ asType) {
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
          type => new UserDefinedType(type.Origin, type.Name[8..], type.TypeArgs));
      }
      if (mockedVarId.ContainsKey(variable)) {
        return mockedVarId[variable];
      }

      List<string> elements = [];
      var variableType = DafnyModelTypeUtils.GetInDafnyFormat(
        DafnyModelTypeUtils.ReplaceTypeVariables(variable.Type, defaultType));
      variableType = DafnyModelTypeUtils.ReplaceType(variableType,
        type => DafnyInfo.GetSupersetType(type) != null &&
                type.Name.StartsWith("_System"),
        type => new UserDefinedType(type.Origin, type.Name[8..], type.TypeArgs));
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
          return GetPrimitiveAsType(variable.PrimitiveLiteral, variableType, asType);
        case SeqType seqType:
          var asBasicSeqType = GetBasicType(asType, type => type is SeqType) as SeqType;
          if (variable?.Cardinality() == -1) {
            if (seqType.Arg is CharType) {
              return "\"\"";
            }
            return AddValue(asType ?? variableType, "[]");
          }
          for (var i = 0; i < variable?.Cardinality(); i++) {
            var element = variable?[i];
            if (element == null) {
              getDefaultValueParams = [];
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

          if (seqType.Arg is CharType || asBasicSeqType?.TypeArgs?.FirstOrDefault((Type/*?*/)null) is CharType) {
            return $"\"{string.Join("", elements.SelectMany(c => c[1..^1]))}\"";
          }
          return AddValue(asType ?? variableType, $"[{string.Join(", ", elements)}]");
        case SetType:
          var asBasicSetType = GetBasicType(asType, type => type is SetType) as SetType;
          foreach (var element in variable.SetElements()) {
            elements.Add(ExtractVariable(element, asBasicSetType?.TypeArgs?.FirstOrDefault((Type/*?*/)null)));
          }
          return AddValue(asType ?? variableType, $"{{{string.Join(", ", elements)}}}");
        case MapType:
          var asBasicMapType = GetBasicType(asType, type => type is MapType) as MapType;
          List<string> mappingStrings = [];
          foreach (var mapping in variable?.Mappings()) {
            var asTypeTypeArgs =
              asBasicMapType?.TypeArgs?.Count == 2 ? asBasicMapType.TypeArgs : null;
            mappingStrings.Add($"{ExtractVariable(mapping.Key, asTypeTypeArgs?[0])} := {ExtractVariable(mapping.Value, asTypeTypeArgs?[1])}");
          }
          return AddValue(asType ?? variableType, $"map[{string.Join(", ", mappingStrings)}]");
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_tuple#"):
          return AddValue(tupleType, "(" +
            string.Join(",", variable.UnnamedDestructors()
              .Select(v => ExtractVariable(v, null))) + ")");
        case ArrowType arrowType:
          var asBasicArrowType = GetBasicType(asType, type => type is ArrowType) as ArrowType;
          var functionOfType = GetFunctionOfType(asBasicArrowType ?? arrowType);
          return AddValue(asBasicArrowType, functionOfType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          if (asType != null) {
            return GetDefaultValue(asType, asType);
          }
          errorMessages.Add($"// Failed to determine a variable type (element {variable.Element}).");
          return "null";
        case UserDefinedType arrType when new Regex("^_System.array[0-9]*\\?$").IsMatch(arrType.Name):
          errorMessages.Add($"// Failed because arrays are not yet supported (type {arrType} element {variable.Element})");
          break;
        case UserDefinedType _ when variable.PrimitiveLiteral != "":
          return "null";
        case UserDefinedType userDefinedType:
          var basicType = GetBasicType(asType ?? userDefinedType,
            type => type == null || type is not UserDefinedType definedType ||
                    DafnyInfo.Datatypes.ContainsKey(definedType
                      .Name)) as UserDefinedType;
          if (basicType == null || !DafnyInfo.Datatypes.ContainsKey(basicType.Name)) {
            return GetClassTypeInstance(userDefinedType, asType, variable);
          }

          if (variable.DatatypeConstructorName() == "") {
            getDefaultValueParams = [];
            return GetDefaultValue(userDefinedType, asType);
          }
          var ctor = DafnyInfo.Datatypes[basicType.Name].Ctors.FirstOrDefault(ctor => ctor.Name == variable.DatatypeConstructorName(), null);
          if (ctor == null) {
            errorMessages.Add($"// Failed: Cannot find constructor {variable.DatatypeConstructorName()} for datatype {basicType}");
            return basicType.ToString();
          }
          List<string> fields = [];
          for (int i = 0; i < ctor.Destructors.Count; i++) {
            var fieldName = ctor.Destructors[i].Name;
            if (!variable.Fields().ContainsKey(fieldName)) {
              fieldName = $"[{i}]";
            }

            if (!variable.Fields().ContainsKey(fieldName)) {
              errorMessages.Add($"// Failed: Cannot find destructor " +
                                $"{ctor.Destructors[i].Name} of constructor " +
                                $"{variable.DatatypeConstructorName()} for datatype " +
                                $"{basicType}. Available destructors are: " +
                                string.Join(",", variable.Fields().Keys.ToList()));
              return basicType.ToString();
            }

            var destructorType = Utils.CopyWithReplacements(
              Utils.UseFullName(ctor.Destructors[i].Type),
              ctor.EnclosingDatatype.TypeArgs.ConvertAll(arg => arg.Name), basicType.TypeArgs);
            if (ctor.Destructors[i].Name.StartsWith("#")) {
              fields.Add(ExtractVariable(variable.Fields()[fieldName], destructorType));
            } else {
              fields.Add(ctor.Destructors[i].Name + ":=" +
                         ExtractVariable(variable.Fields()[fieldName], destructorType));
            }
          }

          var value = basicType.ToString();
          if (fields.Count == 0) {
            value += "." + variable.DatatypeConstructorName();
          } else {
            value += "." + variable.DatatypeConstructorName() + "(" +
                     string.Join(",", fields) + ")";
          }
          return AddValue(asType ?? userDefinedType, value);
      }
      errorMessages.Add($"// Failed because variable has unknown type {variableType} (element {variable.Element})");
      return "null";
    }

    private string GetClassTypeInstance(UserDefinedType type, Type/*?*/ asType, PartialValue/*?*/ variable) {
      var asBasicType = GetBasicType(asType, _ => false);
      if ((asBasicType != null) && (asBasicType is not UserDefinedType)) {
        return GetDefaultValue(asType, asType);
      }
      string varId;
      var dafnyType = DafnyModelTypeUtils.GetNonNullable(asBasicType ?? type) as UserDefinedType;
      if (!DafnyInfo.IsClassType(dafnyType)) {
        errorMessages.Add($"// Failed to identify type class-type {dafnyType} in the AST");
        return "null";
      }
      if (getClassTypeInstanceParams.Contains(dafnyType.ToString())) {
        errorMessages.Add(
          $"// Failed to find a non-recursive way of constructing value (type {dafnyType})");
        return "null";
      }
      getClassTypeInstanceParams.Add(dafnyType.ToString());
      if (DafnyInfo.IsTrait(dafnyType)) {
        return "null";
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
        cache.TypesToSynthesize.Add(dafnyType);
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

    private string GetFieldValue((string name, Type type, bool mutable, string/*?*/ defValue) field, PartialValue/*?*/ variable) {
      if (field.defValue != null) {
        return field.defValue;
      }
      if (variable != null && variable.Fields().ContainsKey(field.name)) {
        return ExtractVariable(variable.Fields()[field.name], field.type);
      }

      var previouslyCreated = ValueCreation.FirstOrDefault(obj =>
        DafnyModelTypeUtils.GetNonNullable(obj.type).ToString() ==
        DafnyModelTypeUtils.GetNonNullable(field.type).ToString(), (null, null, null)).id;
      if (previouslyCreated != null) {
        return previouslyCreated;
      }
      return GetDefaultValue(field.type, field.type);
    }

    private static string GetPrimitiveAsType(string value, Type type, Type/*?*/ asType) {
      if ((type is null) || (asType is null) || value is "[]" or "{}" or "map[]") {
        return value;
      }
      var typeString = type.ToString();
      var asTypeString = asType.ToString();
      if (typeString == asTypeString) {
        return value;
      }
      if (asTypeString.StartsWith("_System.")) {
        asTypeString = asTypeString[8..];
      }
      return $"({value} as {asTypeString})";
    }

    private static Expression GetRealExpr(string value, Type type = null, Type asType = null) {
      bool isNegative = value.Count(c => c == '-') % 2 != 0;

      var matches = Regex.Matches(value, @"\d+(?:\.\d+)?");

      Expression resultExpr;

      if (matches.Count == 1) {
        // Single Decimal: (-3.14) or 3.14
        string numStr = matches[0].Value;
        if (isNegative && numStr != "0" && numStr != "0.0") {
          numStr = "-" + numStr;
        }
        resultExpr = new LiteralExpr(new Token(), BigDec.FromString(numStr));
      } else if (matches.Count >= 2) {
        // Fraction (/ 3.0 4.0) or (/ (- 3.0) 4.0) or 3.0 / 4.0
        string numStr = matches[0].Value;
        string denStr = matches[1].Value;

        if (isNegative && numStr != "0" && numStr != "0.0") {
          numStr = "-" + numStr;
        }

        resultExpr = new BinaryExpr(new Token(), BinaryExpr.Opcode.Div,
          new LiteralExpr(new Token(), BigDec.FromString(numStr)),
          new LiteralExpr(new Token(), BigDec.FromString(denStr)));

      } else {
        resultExpr = new LiteralExpr(new Token(), BigDec.FromString("0.0"));
      }

      if (type != null && asType != null && type.ToString() != asType.ToString()) {
        return new ConversionExpr(new Token(), resultExpr, asType, null);
      }

      return resultExpr;
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
      type = GetBasicType(type, type => DafnyInfo.GetSupersetType(type) == null);
      type = DafnyModelTypeUtils.ReplaceTypeVariables(type, defaultType);
      if ((asType != null) && (DafnyInfo.GetWitnessForType(asType) != null)) {
        return DafnyInfo.GetWitnessForType(asType);
      }
      switch (type) {
        case IntType:
          return GetPrimitiveAsType("0", type, asType);
        case RealType:
          return GetPrimitiveAsType("0.0", type, asType);
        case BoolType:
          return GetPrimitiveAsType("false", type, asType);
        case CharType:
          return GetPrimitiveAsType("\'a\'", type, asType);
        case BitvectorType bitvectorType:
          return GetPrimitiveAsType($"(0 as bv{bitvectorType.Width})", type, asType);
        case SeqType seqType:
          return seqType.Arg is CharType ? "\"\"" : AddValue(asType ?? type, "[]");
        case SetType:
          return AddValue(asType ?? type, "{}");
        case MapType mapType:
          return AddValue(asType ?? type, mapType.Finite ? "map[]" : "imap[]");
        case UserDefinedType tupleType when tupleType.Name.StartsWith("_tuple#"):
          var destructors = new List<string>();
          foreach (var arg in tupleType.TypeArgs) {
            destructors.Add(GetDefaultValue(arg));
          }
          return AddValue(tupleType, "(" + string.Join(",", destructors) + ")");
        case ArrowType arrowType:
          return GetFunctionOfType(arrowType);
        case UserDefinedType unknown when unknown.Name == DafnyModel.UnknownType.Name:
          errorMessages.Add($"// Failed to determine type of a default value");
          return "null";
        case UserDefinedType userDefinedType when userDefinedType.Name.EndsWith("?"):
          return "null";
        case UserDefinedType datatypeType when DafnyInfo.Datatypes.ContainsKey(datatypeType.Name):
          string value;
          if (getDefaultValueParams.Contains(datatypeType.Name)) {
            errorMessages.Add($"// Failed to non-recursively construct a default value for type {datatypeType}");
            return datatypeType.Name + ".UNKNOWN";
          }
          getDefaultValueParams.Add(datatypeType.ToString());
          var ctor = DafnyInfo.Datatypes[datatypeType.Name].Ctors.MinBy(ctor => ctor.Destructors.Count);
          if (ctor.Destructors.Count == 0) {
            value = datatypeType + "." + ctor.Name;
          } else {
            var assignments = ctor.Destructors.Select(destructor =>
              (destructor.Name.StartsWith("#") ? "" : destructor.Name + ":=") + GetDefaultValue(
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
        case UserDefinedType userDefinedType:
          return GetClassTypeInstance(userDefinedType, asType, null);
      }
      errorMessages.Add(
        $"// Failed to extract default value for type " + type ?? "(null)");
      return "null";
    }

    private Expression GetDefaultExpression(Type type) {
      return type switch {
        null => new IdentifierExpr(new Token(), "null"),
        _ when type.IsBoolType => new LiteralExpr(new Token(), false),
        _ when type.IsCharType => new CharLiteralExpr(new Token(), "a"),
        _ when type.IsIntegerType || type.IsBigOrdinalType || type.IsBitVectorType => new LiteralExpr(new Token(), 0),
        _ when type.IsRealType => GetRealExpr("0.0", type, type),
        _ when type.IsStringType => new StringLiteralExpr(new Token(), "", false),
        SeqType => new SeqDisplayExpr(new Token(), new List<Expression>()),
        SetType => new SetDisplayExpr(new Token(), true, new List<Expression>()),
        MapType => new MapDisplayExpr(new Token(), true, new List<MapDisplayEntry>()),
        _ => new IdentifierExpr(new Token(), "null")
      };
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

      return [];
    }

    /// <summary>  Return the test input as a list of lines of code </summary>
    public List<string> TestInputConstructionLines() {
      List<string> lines = [];

      foreach (var line in ValueCreation) {
        lines.Add($"var {line.id} : {line.type} := {line.value};");
        var subsetTypeCondition = DafnyInfo.GetTypeCondition(line.type, line.id);
        if (subsetTypeCondition != null) {
          lines.Add("expect " + Printer.ExprToString(DafnyInfo.Options, subsetTypeCondition) +
                    ", \"If this check fails at runtime, the test does not meet the type constraints\";");
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

      List<string> lines = [];

      if (errorMessages.Count != 0) {
        if (DafnyInfo.Options.Verbose) {
          lines.AddRange(errorMessages);
        }
        return lines;
      }

      var returnParNames = new List<string>();
      var returnFormals = DafnyInfo.GetReturnFormals(MethodName);
      Dictionary<String, String> returnDict = new Dictionary<string, string>();
      for (var i = 0; i < returnFormals.Count; i++) {
        returnParNames.Add("r" + i);
        returnDict["r" + i] = returnFormals[i].Name;
      }

      lines.Add($"method {{:test}} Test{id}() {{");

      lines.AddRange(TestInputConstructionLines());

      string receiver = "";
      if (!DafnyInfo.IsStatic(MethodName)) {
        receiver = ArgValues[0];
        ArgValues.RemoveAt(0);
      }

      if (!DafnyInfo.Options.TestGenOptions.Simplify) {
        lines.AddRange(DafnyInfo.GetRequires(ArgValues,
          MethodName,
          receiver).Select(e =>
          "expect " + Printer.ExprToString(DafnyInfo.Options, e) +
          ", \"If this check fails at runtime, the test does not meet the preconditions\";"));
      }

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

      if (DafnyInfo.Options.TestGenOptions.Simplify && returnParNames.Count != 0 && returnParNames.Count == OutExpressions.Count) {
        foreach (var outVar in returnParNames) {
          var returnLine = "expect " + outVar + " == " + Printer.ExprToString(DafnyInfo.Options, OutExpressions[returnDict[outVar]]) + ";";
          lines.Add(returnLine);
        }
      } else {
        lines.AddRange(DafnyInfo.GetEnsures(ArgValues,
          returnParNames,
          MethodName,
          receiver).Select(e => "expect " + Printer.ExprToString(DafnyInfo.Options, e) + ";"));
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



    /// <summary>
    /// Extracts the AST Expressions for the arguments passed to the method.
    /// </summary>
    private Dictionary<string, Expression> ExtractExpressions(PartialState state, IReadOnlyList<string> printOutput, IReadOnlyList<string> types, bool isReturn = false) {
      var result = new Dictionary<string, Expression>();
      var vars = state.ExpandedVariableSet();

      var parameterIndex = DafnyInfo.IsStatic(MethodName) ? -1 : -2;

      var formals = isReturn
        ? DafnyInfo.GetReturnFormals(MethodName)
        : DafnyInfo.GetFormals(MethodName);

      for (var i = 0; i < printOutput.Count; i++) {
        if (types[i] == "Ty") {
          continue;
        }
        parameterIndex++;

        Type type;
        string paramName;

        if (parameterIndex >= 0) {
          paramName = formals[parameterIndex].Name;
          var formalTypes = isReturn
            ? DafnyInfo.GetReturnTypes(MethodName)
            : DafnyInfo.GetFormalsTypes(MethodName);
          type = Utils.UseFullName(
            formalTypes[parameterIndex]);
          type = Utils.CopyWithReplacements(type,
            DafnyInfo.GetTypeArgsWithParents(MethodName).ConvertAll(arg => arg.ToString()),
            Enumerable.Repeat(defaultType, DafnyInfo.GetTypeArgsWithParents(MethodName).Count).ToList());
          type = DafnyModelTypeUtils.ReplaceType(type,
            _ => true,
            t => DafnyInfo.GetSupersetType(t) != null && t.Name.StartsWith("_System") ?
              new UserDefinedType(t.Origin, t.Name[8..], t.TypeArgs) :
              new UserDefinedType(t.Origin, t.Name, t.TypeArgs));
        } else {
          paramName = "this";
          type = null;
        }
        if (printOutput[i] == "") {
          result[paramName] = GetDefaultExpression(type);
          continue;
        }

        if (!printOutput[i].StartsWith("T@")) {
          if (Regex.IsMatch(printOutput[i], "^[0-9]+bv[0-9]+$")) {
            var baseIndex = printOutput[i].IndexOf('b');
            string numericPart = printOutput[i][..baseIndex];
            var numericLiteral = new LiteralExpr(new Token(), BigInteger.Parse(numericPart));

            if (type != null) {
              result[paramName] = new ConversionExpr(new Token(), numericLiteral, type, null);
            } else {
              result[paramName] = numericLiteral;
            }
          } else {
            result[paramName] = GetParsedValue(printOutput[i], type);
          }
          continue;
        }

        foreach (var variable in vars) {
          if ((variable.Element as Model.Uninterpreted)?.Name != printOutput[i]) {
            continue;
          }
          var expression = ExtractExpression(variable, type);
          if (expression != null) {
            result[paramName] = expression;
          }
          break;
        }
      }
      return result;
    }

    /// <summary>
    /// Recursively constructs a Dafny AST Expression from a PartialValue.
    /// </summary>
    [CanBeNull]
    private Expression ExtractExpression(PartialValue variable, Type/*?*/ asType) {
      if (variable == null) {
        if (asType == null) {
          return null;
        }
        return GetDefaultExpression(asType);
      }

      if (asType != null) {
        asType = DafnyModelTypeUtils.ReplaceType(asType,
          type => DafnyInfo.GetSupersetType(type) != null &&
                  type.Name.StartsWith("_System"),
          type => new UserDefinedType(type.Origin, type.Name[8..], type.TypeArgs));
      }

      if (mockedVarId.ContainsKey(variable)) {
        return new IdentifierExpr(new Token(), mockedVarId[variable]);
      }

      var variableType = DafnyModelTypeUtils.GetInDafnyFormat(
        DafnyModelTypeUtils.ReplaceTypeVariables(variable.Type, defaultType));
      variableType = DafnyModelTypeUtils.ReplaceType(variableType,
        type => DafnyInfo.GetSupersetType(type) != null &&
                type.Name.StartsWith("_System"),
        type => new UserDefinedType(type.Origin, type.Name[8..], type.TypeArgs));
      if (variableType.ToString() == defaultType.ToString() &&
          variableType.ToString() != variable.Type.ToString()) {
        return new LiteralExpr(new Token(), BigInteger.Parse(GetADefaultTypeValue(variable)));
      }

      switch (variableType) {
        case IntType:
        case BigOrdinalType:
        case BitvectorType:
          var literal = new LiteralExpr(new Token(), BigInteger.Parse(variable.PrimitiveLiteral));
          if (asType != null && variableType.ToString() != asType.ToString()) {
            return new ConversionExpr(new Token(), literal, asType, null);
          }

          return literal;

        case RealType:
          return GetRealExpr(variable.PrimitiveLiteral, variableType, asType);

        case BoolType:
          var boolLiteral = new LiteralExpr(new Token(), bool.Parse(variable.PrimitiveLiteral));
          if (asType != null && variableType.ToString() != asType.ToString()) {
            return new ConversionExpr(new Token(), boolLiteral, asType, null);
          }
          return boolLiteral;

        case CharType:
          var varLit = StripString(variable.PrimitiveLiteral);
          var charLiteral = new CharLiteralExpr(new Token(), varLit);
          if (asType != null && variableType.ToString() != asType.ToString()) {
            return new ConversionExpr(new Token(), charLiteral, asType, null);
          }
          return charLiteral;

        case SeqType seqType:
          Type seqElementType = seqType.Arg.NormalizeExpand();

          if (variable?.Cardinality() == -1) {
            if (seqType.Arg is CharType) {
              return new StringLiteralExpr(new Token(), "", false);
            }

            return new SeqDisplayExpr(new Token(), new List<Expression>());
          }

          if (seqElementType is CharType) {
            string extractedString = "";
            for (var i = 0; i < variable?.Cardinality(); i++) {
              var el = variable?[i];
              if (el == null) {
                extractedString += "a";
                continue;
              }

              var elementExpr = ExtractExpression(el, seqElementType);

              if (elementExpr is CharLiteralExpr charExpr) {
                extractedString += charExpr.Value;
              } else {
                extractedString += "a";
              }
            }
            return new StringLiteralExpr(new Token(), extractedString, false);
          }

          var seqElements = new List<Expression>();
          for (var i = 0; i < variable?.Cardinality(); i++) {
            var element = variable?[i];
            if (element == null) {
              seqElements.Add(GetDefaultExpression(seqElementType));
              continue;
            }

            seqElements.Add(ExtractExpression(element, seqElementType));
          }

          return new SeqDisplayExpr(new Token(), seqElements);

        case SetType setType:
          Type setElementType = setType.Arg.NormalizeExpand();
          var setElements = new List<Expression>();
          foreach (var element in variable.SetElements()) {
            setElements.Add(ExtractExpression(element, setElementType));
          }

          return new SetDisplayExpr(new Token(), true, setElements);

        case MapType mapType:
          Type domainType = mapType.Domain.NormalizeExpand();
          Type rangeType = mapType.Range.NormalizeExpand();
          var mapItems = new List<MapDisplayEntry>();
          foreach (var mapping in variable?.Mappings()) {
            var mapKey = ExtractExpression(mapping.Key, domainType);
            var mapValue = ExtractExpression(mapping.Value, rangeType);
            if (mapKey != null && mapValue != null) {
              mapItems.Add(new MapDisplayEntry(mapKey, mapValue));
            }
          }

          return new MapDisplayExpr(new Token(), true, mapItems);


        case UserDefinedType tupleType when tupleType.Name.StartsWith("_tuple#"):
          var tupleValues = variable.UnnamedDestructors().ToList();
          var tupleElements = new List<ActualBinding>();

          for (int i = 0; i < tupleValues.Count; i++) {
            Type innerType = tupleType.TypeArgs[i].NormalizeExpand();
            tupleElements.Add(new ActualBinding(null, ExtractExpression(tupleValues[i], innerType)));
          }

          var ctorName = variable.DatatypeConstructorName();
          if (string.IsNullOrEmpty(ctorName)) {
            ctorName = $"_#Make{tupleElements.Count}";
          }

          return new DatatypeValue(new Token(), tupleType.Name, ctorName, tupleElements);
      }
      return null;
    }

    /// <summary>
    /// Strips string off of double quotes.
    /// </summary>
    private static string StripString(string str) {
      var returnString = str;
      if ((returnString.StartsWith("'") && returnString.EndsWith("'")) || (returnString.StartsWith('"') && returnString.EndsWith('"'))) {
        returnString = returnString.Substring(1, returnString.Length - 2);
      }
      return returnString;
    }

    /// <summary>
    /// Returns the corresponding expression, based on the value's type.
    /// </summary>
    private Expression GetParsedValue(string value, Type type) {
      if (type.IsBoolType) {
        return new LiteralExpr(new Token(), bool.Parse(value));
      }
      if (type.IsIntegerType || type.IsBigOrdinalType || type.IsBitVectorType) {
        return new LiteralExpr(new Token(), BigInteger.Parse(value));
      }
      if (type.IsRealType) {
        return GetRealExpr(value, type, type);
      }
      if (type.IsStringType) {
        return new StringLiteralExpr(new Token(), StripString(value), false);
      }

      return new IdentifierExpr(new Token(), value);
    }

  }
}