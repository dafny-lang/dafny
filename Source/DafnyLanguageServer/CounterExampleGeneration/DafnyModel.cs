// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration {

  /// <summary>
  /// A wrapper around Boogie's Model class that allows extracting
  /// types and values of Elements representing Dafny variables. The three core
  /// methods are: GetDafnyType, CanonicalName, and GetExpansion
  /// </summary>
  public class DafnyModel {
    private DafnyOptions options;
    public readonly Model Model;
    public readonly List<DafnyModelState> States = new();
    public static readonly UserDefinedType UnknownType =
      new(new Token(), "?", null);
    private readonly DafnyFunc fSetSelect, fSeqLength, fSeqIndex, fBox,
      fDim, fIndexField, fMultiIndexField, fDtype, fCharToInt, fTag, fBv, 
      fChar, fNull, fSetUnion, fSetIntersection, fSetDifference, fSetUnionOne,
      fSetEmpty, fSeqEmpty, fSeqBuild, fSeqAppend, fSeqDrop, fSeqTake,
      fSeqUpdate, fSeqCreate, fReal, fU2Real, fBool, fU2Bool, fInt, fU2Int,
      fMapDomain, fMapElements, fMapBuild, fIs, fIsBox, fTChar, fTReal, fTBool, fTInt;
    private readonly Dictionary<Model.Element, Model.FuncTuple> datatypeValues = new();

    // maps a numeric type (int, real, bv4, etc.) to the set of integer
    // values of that type that appear in the model. 
    private readonly Dictionary<Type, HashSet<int>> reservedNumerals = new();
    // set of all UTF values for characters that appear in the model
    private readonly HashSet<int> reservedChars = new();
    private bool isTrueReserved; // True if "true" appears anywhere in the model
    // maps an element representing a primitive to its string representation
    private readonly Dictionary<Model.Element, string> reservedValuesMap = new();
    // maps width to a unique object representing bitvector type of such width 
    private readonly Dictionary<int, BitvectorType> bitvectorTypes = new();

    // the model will begin assigning characters starting from this utf value
    private const int FirstCharacterUtfValue = 65; // 'A'
    private static readonly Regex BvTypeRegex = new("^bv[0-9]+Type$");
    private static readonly Regex UnderscoreRemovalRegex = new("__");

    class DafnyFunc {

      private readonly Model.Func func;
      private readonly int tyArgs;
      public DafnyFunc(DafnyModel model, DafnyOptions options, string name, int arity, int tyArgs) {
        var extraTypeArguments = options.TypeEncodingMethod switch {
          CoreOptions.TypeEncoding.Arguments => 1,
          _ => 0
        };
        this.tyArgs = extraTypeArguments * tyArgs;
        func = model.Model.MkFunc(name, arity + this.tyArgs);
      }

      private Model.FuncTuple ConvertFuncTuple(Model.FuncTuple tuple) {
        if (tuple == null) {
          return null;
        }
        return new Model.FuncTuple(func, tuple.Result, tuple.Args[tyArgs..]);
      }

      public Model.FuncTuple AppWithResult(Model.Element element) {
        return ConvertFuncTuple(func.AppWithResult(element));
      }

      public IEnumerable<Model.FuncTuple> Apps => func.Apps.Select(ConvertFuncTuple);

      public Model.Element GetConstant() {
        return func.GetConstant();
      }
      
      public Model.Element OptEval(Model.Element element) {
        if (element == null) {
          return null;
        }
        var app = func.AppWithArg(tyArgs, element);
        if (app == null) {
          return null;
        }
        return app.Result;
      }
      
      public Model.Element OptEval(Model.Element first, Model.Element second) {
        if (first == null || second == null) {
          return null;
        }
        var app = func.AppsWithArgs(tyArgs, first, tyArgs+1, second);
        if (app == null || !app.Any()) {
          return null;
        }
        return app.First().Result;
      }

      public IEnumerable<Model.FuncTuple> AppsWithArg(int i, Model.Element element) {
        return func.AppsWithArg(i + tyArgs, element).Select(ConvertFuncTuple);
      }

      public IEnumerable<Model.FuncTuple> AppsWithArgs(int i0, Model.Element element0, int i1, Model.Element element1) {
        return func.AppsWithArgs(i0 + tyArgs, element0, i1 + tyArgs, element1).Select(ConvertFuncTuple);
      }
      
      /// <summary>
      /// Create a new function that merges together the applications of all the
      /// functions that have a certain arity and whose name matches the
      /// "^MapType[0-9]*Select$" pattern. This has previously been done by
      /// Boogie's Model Parser as a preprocessing step but has been deprecated
      /// since 2.9.2
      /// </summary>
      internal static DafnyFunc MergeFunctions(DafnyModel model, List<string> names, int arity) {
        var name = "[" + arity + "]";
        if (model.Model.HasFunc(name)) {
          // Coming up with a new name if the ideal one is reserved
          int id = 0;
          while (model.Model.HasFunc(name + "#" + id)) {
            id++;
          }
          name += "#" + id;
        }
        var result = new DafnyFunc(model, model.options, name, arity, 0);
        foreach (var func in model.Model.Functions) {
          if (!names.Contains(func.Name) || func.Arity == null || func.Arity < arity) {
            continue;
          }
          // this removes type arguments when TypeEncodingMethod == Bpl.CoreOptions.TypeEncoding.Arguments
          int offset = func.Arity.Value - arity; 
          foreach (var app in func.Apps) {
            result.func.AddApp(app.Result, app.Args[offset..]);
          }
          result.func.Else ??= func.Else;
        }
        return result;
      }
    }

    public DafnyModel(Model model, DafnyOptions options) {
      Model = model;
      this.options = options;
      fSetSelect = DafnyFunc.MergeFunctions(this, new List<string> {"MapType0Select", "MapType1Select"}, 2);
      fSeqLength = new DafnyFunc(this, options, "Seq#Length", 1, 1);
      fSeqBuild = new DafnyFunc(this, options, "Seq#Build", 2, 1);
      fSeqAppend = new DafnyFunc(this, options, "Seq#Append", 2, 1);
      fSeqDrop = new DafnyFunc(this, options, "Seq#Drop", 2, 1);
      fSeqTake = new DafnyFunc(this, options, "Seq#Take", 2, 1);
      fSeqIndex = new DafnyFunc(this, options, "Seq#Index", 2, 1);
      fSeqUpdate = new DafnyFunc(this, options, "Seq#Update", 3, 1);
      fSeqCreate = new DafnyFunc(this, options, "Seq#Create", 4, 0);
      fSeqEmpty = new DafnyFunc(this, options, "Seq#Empty", 1, 0);
      fSetEmpty = new DafnyFunc(this, options, "Set#Empty", 1, 0);
      fSetUnion = new DafnyFunc(this, options, "Set#Union", 2, 1);
      fSetUnionOne = new DafnyFunc(this, options, "Set#UnionOne", 2, 1);
      fSetIntersection = new DafnyFunc(this, options, "Set#Intersection", 2, 1);
      fSetDifference = new DafnyFunc(this, options, "Set#Difference", 2, 1);
      fMapDomain = new DafnyFunc(this, options, "Map#Domain", 1, 2);
      fMapElements = new DafnyFunc(this, options, "Map#Elements", 1, 2);
      fMapBuild = new DafnyFunc(this, options, "Map#Build", 3, 2);
      fIs = new DafnyFunc(this, options, "$Is", 2, 1);
      fIsBox = new DafnyFunc(this, options, "$IsBox", 2, 1);
      fBox = new DafnyFunc(this, options, "$Box", 1, 1);
      fDim = new DafnyFunc(this, options, "FDim", 1, 1);
      fIndexField = new DafnyFunc(this, options, "IndexField", 1, 0);
      fMultiIndexField = new DafnyFunc(this, options, "MultiIndexField", 2, 0);
      fDtype = new DafnyFunc(this, options, "dtype", 1, 0);
      fNull = new DafnyFunc(this, options, "null", 0, 0);
      fCharToInt = new DafnyFunc(this, options, "char#ToInt", 1, 0);
      fChar = new DafnyFunc(this, options, "charType", 0, 0);
      fReal = new DafnyFunc(this, options, "realType", 0, 0);
      fU2Real = new DafnyFunc(this, options, "U_2_real", 1, 0);
      fBool = new DafnyFunc(this, options, "boolType", 0, 0);
      fU2Bool = new DafnyFunc(this, options, "U_2_bool", 1, 0);
      fInt = new DafnyFunc(this, options, "intType", 0, 0);
      fU2Int = new DafnyFunc(this, options, "U_2_int", 1, 0);
      fTag = new DafnyFunc(this, options, "Tag", 1, 0);
      fBv = new DafnyFunc(this, options, "TBitvector", 1, 0);
      fTChar = new DafnyFunc(this, options, "TChar", 0, 0);
      fTInt = new DafnyFunc(this, options, "TInt", 0, 0);
      fTReal = new DafnyFunc(this, options, "TReal", 0, 0);
      fTBool = new DafnyFunc(this, options, "TBool", 0, 0);
      InitDataTypes();
      RegisterReservedChars();
      RegisterReservedInts();
      RegisterReservedBools();
      RegisterReservedReals();
      RegisterReservedBitVectors();
      foreach (var s in model.States) {
        var sn = new DafnyModelState(this, s);
        States.Add(sn);
      }
    }

    /// <summary>
    /// Extract and parse the first Dafny model recorded in the model view file.
    /// </summary>
    public static DafnyModel ExtractModel(DafnyOptions options, string mv) {
      const string begin = "*** MODEL";
      const string end = "*** END_MODEL";
      int beginIndex = mv.IndexOf(begin, StringComparison.Ordinal);
      int endIndex = mv.IndexOf(end, StringComparison.Ordinal);
      var modelString = mv.Substring(beginIndex, endIndex + end.Length - beginIndex);
      var model = Model.ParseModels(new StringReader(modelString)).First();
      return new DafnyModel(model, options);
    }

    /// <summary>
    /// Collect the array dimensions from the various array.Length functions,
    /// and collect all known datatype values
    /// </summary>
    private void InitDataTypes() {
      const string datatypeConstructorPrefix = "#";
      const string reservedVariablePrefix = "##";
      const string accessorString = ".";
      foreach (var fn in Model.Functions) {
        if (fn.Name.StartsWith(datatypeConstructorPrefix) &&
            !fn.Name.StartsWith(reservedVariablePrefix) &&
            fn.Name.Contains(accessorString)) {
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Result;
            datatypeValues[elt] = tpl;
          }
        }
      }
    }

    /// <summary> Register all char values specified by the model </summary>
    private void RegisterReservedChars() {
      foreach (var app in fCharToInt.Apps) {
        if (int.TryParse(((Model.Integer)app.Result).Numeral,
              out var UTFCode) && UTFCode is <= char.MaxValue and >= 0) {
          reservedChars.Add(UTFCode);
        }
      }
    }

    /// <summary>
    /// Return the character representation of a UTF code understood by Dafny
    /// This is either the character itself, if it is a parsable ASCII,
    /// Escaped character, for the cases specified in Dafny manual,
    /// Or escaped UTF code otherwise
    /// </summary>
    private string PrettyPrintChar(int UTFCode) {
      switch (UTFCode) {
        case 0:
          return "'\\0'";
        case 9:
          return "'\\t'";
        case 10:
          return "'\\n'";
        case 13:
          return "'\\r'";
        case 34:
          return "'\\\"'";
        case 39:
          return "'\\\''";
        case 92:
          return "'\\\\'";
        default:
          if ((UTFCode >= 32) && (UTFCode <= 126)) {
            return $"'{Convert.ToChar(UTFCode)}'";
          }
          return $"'\\u{UTFCode:X4}'";
      }
    }

    /// <summary> Registered all int values specified by the model </summary>
    private void RegisterReservedInts() {
      reservedNumerals[Type.Int] = new();
      foreach (var app in fU2Int.Apps) {
        if (app.Result is Model.Integer integer && int.TryParse(integer.Numeral, out int value)) {
          reservedNumerals[Type.Int].Add(value);
        }
      }
    }

    /// <summary> Registered all bool values specified by the model </summary>
    private void RegisterReservedBools() {
      foreach (var app in fU2Bool.Apps) {
        isTrueReserved |= ((Model.Boolean)app.Result).Value;
      }
    }

    /// <summary> Registered all real values specified by the model </summary>
    private void RegisterReservedReals() {
      reservedNumerals[Type.Real] = new();
      foreach (var app in fU2Real.Apps) {
        var valueAsString = app.Result.ToString()?.Split(".")[0] ?? "";
        if ((app.Result is Model.Real) && int.TryParse(valueAsString, out int value)) {
          reservedNumerals[Type.Real].Add(value);
        }
      }
    }

    /// <summary> Registered all bv values specified by the model </summary>
    private void RegisterReservedBitVectors() {
      var bvFuncName = new Regex("^U_2_bv[0-9]+$");
      foreach (var func in Model.Functions) {
        if (!bvFuncName.IsMatch(func.Name)) {
          continue;
        }

        int width = int.Parse(func.Name[6..]);
        if (!bitvectorTypes.ContainsKey(width)) {
          bitvectorTypes[width] = new BitvectorType(options, width);
        }

        var type = bitvectorTypes[width];

        if (!reservedNumerals.ContainsKey(type)) {
          reservedNumerals[type] = new();
        }

        foreach (var app in func.Apps) {
          if (int.TryParse((app.Result as Model.BitVector).Numeral,
                out var value)) {
            reservedNumerals[type].Add(value);
          }
        }
      }
    }

    /// <summary>
    /// Return True iff the variable name is referring to a variable that has
    /// a direct analog in Dafny source (i.e. not $Heap, $_Frame, $nw, etc.)
    /// </summary>
    public static bool IsUserVariableName(string name) =>
      !name.StartsWith("$") && !name.Contains("##") && !name.Contains("$");

    public bool ElementIsNull(Model.Element element) => element == fNull.GetConstant();

    /// <summary>
    /// Return the name of the 0-arity function that maps to the element if such
    /// a function exists. Return null otherwise. If multiple options exist,
    /// return those that start with "T" or "_", which signifies a type
    /// </summary>
    private static string GetTrueTypeName(Model.Element element) {
      string name = null;
      if (element == null) {
        return null;
      }
      foreach (var funcTuple in element.Names) {
        if (funcTuple.Func.Arity != 0) {
          continue;
        }
        if ((name == null) || name.Contains("$") || name.StartsWith("#") || name.Contains("@")) { // 2nd case is type param
          name = funcTuple.Func.Name;
        } else if (!funcTuple.Func.Name.Contains("$") && !funcTuple.Func.Name.StartsWith("#") && !funcTuple.Func.Name.Contains("@")) {
          return null;
        }
      }
      return name;
    }

    /// <summary> Get the Dafny type of an element </summary>
    internal Type GetDafnyType(Model.Element element) {
      switch (element.Kind) {
        case Model.ElementKind.Boolean:
          return Type.Bool;
        case Model.ElementKind.Integer:
          return Type.Int;
        case Model.ElementKind.Real:
          return Type.Real;
        case Model.ElementKind.BitVector:
          return new BitvectorType(options, ((Model.BitVector)element).Size);
        case Model.ElementKind.Uninterpreted:
          return GetDafnyType(element as Model.Uninterpreted);
        case Model.ElementKind.DataValue:
          if (((Model.DatatypeValue)element).ConstructorName is "-" or "/") {
            return GetDafnyType(
              ((Model.DatatypeValue)element).Arguments.First());
          }
          return UnknownType; // This shouldn't be reachable.
        default:
          return UnknownType;
      }
    }

    /// <summary>
    /// Return all elements x that satisfy ($Is element x)
    /// </summary>
    private List<Model.Element> GetIsResults(Model.Element element) {
      List<Model.Element> result = new();
      Dictionary<string, Model.Element> typeNameToElement = new Dictionary<string, Model.Element>();
      foreach (var tuple in fIs.AppsWithArg(0, element)) {
        if (((Model.Boolean)tuple.Result).Value) {
          // The conditions below ensure a non-nullable type is preferred
          var typeName = GetTrueTypeName(tuple.Args[1]);
          if (typeName != null) {
            if (typeName.EndsWith("?") && typeNameToElement.ContainsKey(typeName[..^1])) {
              continue;
            }
            if (!typeName.EndsWith("?") && typeNameToElement.ContainsKey(typeName + "?")) {
              result.Remove(typeNameToElement[typeName + "?"]);
            }
          }
          result.Add(tuple.Args[1]);
        }
      }
      return result;
    }

    /// <summary> Get the Dafny type of an Uninterpreted element </summary>
    private Type GetDafnyType(Model.Uninterpreted element) {
      List<Model.Element> isOfType = GetIsResults(element);
      if (isOfType.Count > 0) { 
        return ReconstructType(isOfType.First()); // TODO: How to choose the right one?
      }
      var seqOperation = fSeqAppend.AppWithResult(element);
      seqOperation ??= fSeqDrop.AppWithResult(element);
      seqOperation ??= fSeqTake.AppWithResult(element);
      seqOperation ??= fSeqUpdate.AppWithResult(element);
      if (seqOperation != null) {
        return GetDafnyType(seqOperation.Args[0]); // TODO not sure about the index
      }
      seqOperation = fSeqBuild.AppWithResult(element);
      if (seqOperation != null) {
        return new SeqType(GetDafnyType(Unbox(seqOperation.Args[1])));
      }
      seqOperation = fSeqCreate.AppWithResult(element);
      seqOperation ??= fSeqEmpty.AppWithResult(element);
      if (seqOperation != null) {
        return new SeqType(ReconstructType(seqOperation.Args.First()));
      }
      var setOperation = fSetUnion.AppWithResult(element);
      setOperation ??= fSetIntersection.AppWithResult(element);
      setOperation ??= fSetDifference.AppWithResult(element);
      if (setOperation != null) {
        return GetDafnyType(setOperation.Args[0]); // TODO not sure about the index
      }
      setOperation = fSetUnionOne.AppWithResult(element);
      if (setOperation != null) {
        return new SetType(true, GetDafnyType(Unbox(setOperation.Args[1])));
      }
      setOperation = fSetEmpty.AppWithResult(element);
      if (setOperation != null) {
        return new SetType(true, ReconstructType(setOperation.Args.First()));
      }
      var mapOperation = fMapBuild.AppWithResult(element);
      if (mapOperation != null) {
        return GetDafnyType(mapOperation.Args.First());
      }
      var typeElement = fDtype.OptEval(element);
      if (typeElement != null) {
        return ReconstructType(typeElement);
      }
      // case var bv when BvTypeRegex.IsMatch(bv):
      // return new BitvectorType(options, int.Parse(bv[2..^4])); Bitvector types
      var unboxedTypes = fIsBox.AppsWithArg(0, element)
        .Where(tuple => ((Model.Boolean)tuple.Result).Value)
        .Select(tuple => tuple.Args[1]).ToList();
      if (unboxedTypes.Count == 1) {
        return ReconstructType(unboxedTypes[0]);
      }
      if (fCharToInt.OptEval(element) != null) {
        return Type.Char;
      }
      return UnknownType;
    }

    /// <summary>
    /// Reconstruct Dafny type from an element that represents a type in Z3
    /// </summary>
    private Type ReconstructType(Model.Element typeElement) {
      if (typeElement == null) {
        return UnknownType;
      }
      var fullName = GetTrueTypeName(typeElement);
      if (fullName != null && fullName.Length > 7 && fullName[..7].Equals("Tclass.")) {
        return new UserDefinedType(new Token(), fullName[7..], null);
      }
      switch (fullName) {
        case "TInt":
          return Type.Int;
        case "TBool":
          return Type.Bool;
        case "TReal":
          return Type.Real;
        case "TChar":
          return Type.Char;
      }
      if (fBv.AppWithResult(typeElement) != null) {
        return new BitvectorType(options, ((Model.Integer)fBv.AppWithResult(typeElement).Args[0]).AsInt());
      }

      Type fallBackType = UnknownType; // to be returned in the event all else fails
      if (fullName != null) { // this means this is a type variable
        fallBackType = new UserDefinedType(new Token(), fullName, null);
      }
      var tagElement = fTag.OptEval(typeElement);
      if (tagElement == null) {
        return fallBackType;
      }
      var tagName = GetTrueTypeName(tagElement);
      if (tagName == null || (tagName.Length < 10 && tagName != "TagSeq" &&
                              tagName != "TagSet" &&
                              tagName != "TagBitVector" &&
                              tagName != "TagMap")) {
        return fallBackType;
      }
      var typeArgs = Model.GetFunc("T" + tagName.Substring(3))?.
        AppWithResult(typeElement)?.
        Args.Select(ReconstructType).ToList();
      if (typeArgs == null) {
        return new UserDefinedType(new Token(), tagName.Substring(9), null);
      }

      switch (tagName) {
        case "TagSeq":
          return new SeqType(typeArgs.First());
        case "TagMap":
          return new Microsoft.Dafny.MapType(true, typeArgs[0], typeArgs[1]);
        case "TagSet":
          return new SetType(true, typeArgs.First());
        default:
          tagName = tagName.Substring(9);
          if (tagName.StartsWith("_System.___hFunc") ||
              tagName.StartsWith("_System.___hTotalFunc") ||
              tagName.StartsWith("_System.___hPartialFunc")) {
            return new ArrowType(new Token(), typeArgs.SkipLast(1).ToList(),
              typeArgs.Last());
          }
          return new UserDefinedType(new Token(), tagName, typeArgs);
      }
    }

    /// <summary>
    /// Extract the string representation of the element.
    /// Return "" if !IsPrimitive(elt, state) unless elt is a datatype,
    /// in which case return the corresponding constructor name.
    /// </summary>
    public string CanonicalName(Model.Element elt, Type type) {
      if (elt == null || (type is UserDefinedType userDefinedType && userDefinedType.Name == UnknownType.Name)) {
        return "?";
      }
      if (elt == fNull.GetConstant()) {
        return "null";
      }
      if (elt is Model.Integer or Model.Boolean or Model.Real) {
        return elt.ToString();
      }
      if (elt is Model.BitVector vector) {
        return vector.Numeral;
      }
      var primitiveType = GetIsResults(elt).FirstOrDefault();
      if (type is BitvectorType bitvectorType) { // TODO: What if it is a type synonym?
        int width = bitvectorType.Width;
        var funcName = "U_2_bv" + width;
        if (!bitvectorTypes.ContainsKey(width)) {
          bitvectorTypes[width] = new BitvectorType(options, width);
          reservedNumerals[bitvectorTypes[width]] = new HashSet<int>();
        }
        if (!Model.HasFunc(funcName)) {
          return GetUnreservedNumericValue(elt, bitvectorTypes[width]);
        }
        if (Model.GetFunc(funcName).OptEval(elt) != null) {
          return (Model.GetFunc(funcName).OptEval(elt) as Model.Number)?.Numeral;
        }
        return GetUnreservedNumericValue(elt, bitvectorTypes[width]);
      }
      if (elt.Kind == Model.ElementKind.DataValue) {
        if (((Model.DatatypeValue)elt).ConstructorName == "-") {
          return "-" + CanonicalName(((Model.DatatypeValue)elt).Arguments.First(), type);
        }
        if (((Model.DatatypeValue)elt).ConstructorName == "/") {
          return CanonicalName(((Model.DatatypeValue)elt).Arguments.First(), type) +
                 "/" + CanonicalName(((Model.DatatypeValue)elt).Arguments[1], type);
        }
      }
      if (datatypeValues.TryGetValue(elt, out var fnTuple)) {
        return fnTuple.Func.Name.Split(".").Last();
      }
      if (primitiveType == fChar.GetConstant() || primitiveType == fTChar.GetConstant() || fCharToInt.OptEval(elt) != null) {
        if (fCharToInt.OptEval(elt) != null) {
          if (int.TryParse(((Model.Integer)fCharToInt.OptEval(elt)).Numeral,
                out var UTFCode) && UTFCode is <= char.MaxValue and >= 0) {
            return PrettyPrintChar(UTFCode);
          }
        }
        return GetUnreservedCharValue(elt);
      }
      if (primitiveType == fReal.GetConstant() || primitiveType == fTReal.GetConstant()) {
        if (fU2Real.OptEval(elt) != null) {
          return CanonicalName(fU2Real.OptEval(elt), type);
        }
        return GetUnreservedNumericValue(elt, Type.Real);
      }
      if (primitiveType == fBool.GetConstant() || primitiveType == fTBool.GetConstant()) {
        if (fU2Bool.OptEval(elt) != null) {
          return CanonicalName(fU2Bool.OptEval(elt), type);
        }
        return GetUnreservedBoolValue(elt);
      }
      if (primitiveType == fInt.GetConstant() || primitiveType == fTInt.GetConstant()) {
        if (fU2Int.OptEval(elt) != null) {
          return CanonicalName(fU2Int.OptEval(elt), type);
        }
        return GetUnreservedNumericValue(elt, Type.Int);
      }
      return "";
    }

    /// <summary>
    /// Find a char value that is different from any other value
    /// of that type in the entire model. Reserve that value for given element
    /// </summary>
    private string GetUnreservedCharValue(Model.Element element) {
      if (reservedValuesMap.TryGetValue(element, out var reservedValue)) {
        return reservedValue;
      }
      int i = FirstCharacterUtfValue;
      while (reservedChars.Contains(i)) {
        i++;
      }
      reservedValuesMap[element] = PrettyPrintChar(i);
      reservedChars.Add(i);
      return reservedValuesMap[element];
    }

    /// <summary>
    /// Find a bool value that is different from any other value
    /// of that type in the entire model (if possible).
    /// Reserve that value for given element
    /// </summary>
    private string GetUnreservedBoolValue(Model.Element element) {
      if (reservedValuesMap.TryGetValue(element, out var reservedValue)) {
        return reservedValue;
      }
      if (!isTrueReserved) {
        isTrueReserved = true;
        reservedValuesMap[element] = true.ToString().ToLower();
      } else {
        reservedValuesMap[element] = false.ToString().ToLower();
      }
      return reservedValuesMap[element];
    }

    /// <summary>
    /// Find a value of the given numericType that is different from
    /// any other value of that type in the entire model.
    /// Reserve that value for given element
    /// </summary>
    public string GetUnreservedNumericValue(Model.Element element, Type numericType) {
      if (reservedValuesMap.TryGetValue(element, out var reservedValue)) {
        return reservedValue;
      }
      int i = 0;
      while (reservedNumerals[numericType].Contains(i)) {
        i++;
      }
      if (numericType == Type.Real) {
        reservedValuesMap[element] = i + ".0";
      } else {
        reservedValuesMap[element] = i.ToString();
      }
      reservedNumerals[numericType].Add(i);
      return reservedValuesMap[element];
    }

    /// <summary>
    /// Return a set of variables associated with an element. These could be
    /// values of fields for objects, values at certain positions for
    /// sequences, etc.
    /// </summary>
    public IEnumerable<DafnyModelVariable> GetExpansion(DafnyModelState state, DafnyModelVariable var) {
      HashSet<DafnyModelVariable> result = new();
      if (var.Element.Kind != Model.ElementKind.Uninterpreted) {
        return result;  // primitive types can't have fields
      }

      if (datatypeValues.TryGetValue(var.Element, out var fnTuple)) {
        // Elt is a datatype value
        var destructors = GetDestructorFunctions(var.Element).OrderBy(f => f.Name).ToList();
        if (destructors.Count > fnTuple.Args.Length) {
          // Try to filter out predicate functions
          // (that follow a format very similar to that of destructor names)
          destructors = destructors.Where(destructor =>
              fnTuple.Args.Any(arg => destructor.OptEval(var.Element) == arg))
            .ToList();
        }
        if (destructors.Count == fnTuple.Args.Length) {
          // we know all destructor names
          foreach (var func in destructors) {
            result.Add(DafnyModelVariableFactory.Get(state, Unbox(func.OptEval(var.Element)),
              func.Name.Split(".").Last(), var));
          }
        } else {
          // we don't now destructor names, so we use indices instead
          for (int i = 0; i < fnTuple.Args.Length; i++) {
            result.Add(DafnyModelVariableFactory.Get(state, Unbox(fnTuple.Args[i]),
              "[" + i + "]", var));
          }
        }
        return result;
      }

      var seqLen = fSeqLength.OptEval(var.Element);
      if (seqLen != null) { // Elt is a sequence
        var length = DafnyModelVariableFactory.Get(state, seqLen, "Length", var);
        result.Add(length);
        (var as SeqVariable)?.SetLength(length);

        // Sequences can be constructed with the build operator:
        List<Model.Element> elements = new();

        var substring = var.Element;
        while (fSeqBuild.AppWithResult(substring) != null) {
          elements.Insert(0, Unbox(fSeqBuild.AppWithResult(substring).Args[1]));
          substring = fSeqBuild.AppWithResult(substring).Args[0];
        }
        for (int i = 0; i < elements.Count; i++) {
          var e = DafnyModelVariableFactory.Get(state, Unbox(elements[i]), "[" + i + "]", var);
          result.Add(e);
          (var as SeqVariable)?.AddAtIndex(e, i.ToString());
        }
        if (elements.Count > 0) {
          return result;
        }

        // Otherwise, sequences can be reconstructed index by index, ensuring indices are in ascending order.
        // NB: per https://github.com/dafny-lang/dafny/issues/3048 , not all indices may be parsed as a BigInteger,
        // so ensure we do not try to sort those numerically.
        var intIndices = new List<(Model.Element, BigInteger)>();
        var otherIndices = new List<(Model.Element, String)>();
        foreach (var tpl in fSeqIndex.AppsWithArg(0, var.Element)) {
          var asString = tpl.Args[1].ToString();
          if (BigInteger.TryParse(asString, out var bi)) {
            intIndices.Add((Unbox(tpl.Result), bi));
          } else {
            otherIndices.Add((Unbox(tpl.Result), asString));
          }
        }

        var sortedIndices = intIndices
          .OrderBy(p => p.Item2)
          .Select(p => (p.Item1, p.Item2.ToString()))
          .Concat(otherIndices);

        foreach (var (res, idx) in sortedIndices) {
          var e = DafnyModelVariableFactory.Get(state, res, "[" + idx + "]", var);
          result.Add(e);
          (var as SeqVariable)?.AddAtIndex(e, idx);
        }

        return result;
      }
      foreach (var tpl in fSetSelect.AppsWithArg(0, var.Element)) {
        var setElement = tpl.Args[1];
        var containment = tpl.Result;
        if (containment.Kind != Model.ElementKind.Boolean) {
          continue;
        }
        result.Add(DafnyModelVariableFactory.Get(state, Unbox(setElement),
          ((Model.Boolean)containment).ToString(), var));
      }
      if (result.Count != 0) { // Elt is a set
        return result;
      }

      var mapDomain = fMapDomain.OptEval(var.Element);
      var mapElements = fMapElements.OptEval(var.Element);
      var mapBuildStartPoint = var.Element;
      var mapBuild = fMapBuild.AppWithResult(var.Element);
      while (mapBuild != null) {
        var pairId = var.Children.Count.ToString();
        var key = DafnyModelVariableFactory.Get(state, Unbox(mapBuild.Args[1]), pairId, var);
        var value = DafnyModelVariableFactory.Get(state, Unbox(mapBuild.Args[2]), pairId, var);
        result.Add(key);
        result.Add(value);
        ((MapVariable)var).AddMapping(key, value);
        mapDomain = fMapDomain.OptEval(mapBuild.Args[0]);
        mapElements = fMapElements.OptEval(mapBuild.Args[0]);
        if (mapBuild.Args[0] == mapBuildStartPoint) {
          break; // can happen when constructing maps with single application
        }
        mapBuild = fMapBuild.AppWithResult(mapBuild.Args[0]);
      }
      if (mapDomain != null && mapElements != null) {
        foreach (var app in fSetSelect.AppsWithArg(0, mapDomain)) {
          if (!((Model.Boolean)app.Result).Value) {
            continue;
          }
          var pairId = var.Children.Count.ToString();
          var key = DafnyModelVariableFactory.Get(state, Unbox(app.Args[1]), pairId, var);
          result.Add(key);
          var valueElement = fSetSelect.OptEval(mapElements, app.Args[1]);
          if (valueElement == null) {
            ((MapVariable)var).AddMapping(key, null);
          } else {
            var value = DafnyModelVariableFactory.Get(state, Unbox(valueElement), pairId, var);
            result.Add(value);
            ((MapVariable)var).AddMapping(key, value);
          }
        }
      }

      // Elt is an array or an object:
      var heap = state.State.TryGet("$Heap");
      if (heap == null) {
        return result;
      }
      var constantFields = GetDestructorFunctions(var.Element).OrderBy(f => f.Name).ToList();
      foreach (var field in constantFields) {
        result.Add(DafnyModelVariableFactory.Get(state, Unbox(field.OptEval(var.Element)),
          field.Name.Split(".").Last(), var));
      }
      var fields = fSetSelect.AppsWithArgs(0, heap, 1, var.Element);
      if (fields == null || !fields.Any()) {
        return result;
      }
      foreach (var tpl in fSetSelect.AppsWithArg(0, fields.ToList()[0].Result)) {
        foreach (var fieldName in GetFieldNames(tpl.Args[1])) {
          if (fieldName != "alloc") {
            result.Add(DafnyModelVariableFactory.Get(state, Unbox(tpl.Result), fieldName, var));
          }
        }
      }
      return result;
    }

    /// <summary>
    /// Return all functions mapping an object to a destructor value.
    /// </summary>
    private List<Model.Func> GetDestructorFunctions(Model.Element element) {
      var possibleTypeIdentifiers = GetIsResults(element);
      if (fDtype.OptEval(element) != null) {
        possibleTypeIdentifiers.Add(fDtype.OptEval(element));
      }
      var possiblyNullableTypes = possibleTypeIdentifiers
        .Select(isResult => ReconstructType(isResult) as UserDefinedType)
        .Where(type => type != null && type.Name != UnknownType.Name);
      var types = possiblyNullableTypes.Select(type => DafnyModelTypeUtils.GetNonNullable(type) as UserDefinedType);
      List<Model.Func> result = new();
      var builtInDatatypeDestructor = new Regex("^.*[^_](__)*_q$");
      foreach (var app in element.References) {
        if (app.Func.Arity != 1 || app.Args[0] != element ||
            !types.Any(type => app.Func.Name.StartsWith(type.Name + ".")) ||
            builtInDatatypeDestructor.IsMatch(app.Func.Name.Split(".").Last())) {
          continue;
        }
        result.Add(app.Func);
      }
      return result;
    }

    private const string PleaseEnableModelCompressFalse =
      "Please enable /proverOpt:O:model_compress=false (for z3 version < 4.8.7)" +
      " or /proverOpt:O:model.compact=false (for z3 version >= 4.8.7)," +
      " otherwise you'll get unexpected values.";

    /// <summary>
    /// Return the name of the field represented by the given element.
    /// Special care is required if the element represents an array index
    /// </summary>
    private List<string> GetFieldNames(Model.Element elt) {
      if (elt == null) {
        return new List<string>();
      }
      var dims = fDim.OptEval(elt)?.AsInt();
      if (dims is null or 0) { // meaning elt is not an array index
        return elt.Names.Where(tuple =>
          tuple.Func.Arity == 0 && !tuple.Func.Name.Contains("$"))
          .Select(tuple => UnderscoreRemovalRegex
            .Replace(tuple.Func.Name.Split(".").Last(), "_"))
          .ToList();
      }
      // Reaching this code means elt is an index into an array
      var indices = new Model.Element[(int)dims];
      for (int i = (int)dims; 0 <= --i;) {
        Model.FuncTuple dimTuple;
        if (i == 0) {
          dimTuple = fIndexField.AppWithResult(elt);
          if (dimTuple == null) {
            options.OutputWriter.WriteLine(PleaseEnableModelCompressFalse);
            continue;
          }
          indices[i] = dimTuple.Args[0];
        } else {
          dimTuple = fMultiIndexField.AppWithResult(elt);
          if (dimTuple == null) {
            options.OutputWriter.WriteLine(PleaseEnableModelCompressFalse);
            continue;
          }
          indices[i] = dimTuple.Args[1];
          elt = dimTuple.Args[0];
        }
      }
      return new List<string>() {
        "[" + string.Join(",",
          indices.ToList().ConvertAll(element => element == null ? "null" : element.ToString())) + "]"
      };
    }

    /// <summary> Unboxes an element, if possible </summary>
    private Model.Element Unbox(Model.Element elt) {
      var unboxed = fBox.AppWithResult(elt);
      return unboxed != null ? unboxed.Args[0] : elt;
    }
  }
}
