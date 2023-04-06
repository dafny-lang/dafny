// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyServer.CounterexampleGeneration {

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
    private readonly Model.Func fSetSelect, fSeqLength, fSeqIndex, fBox,
      fDim, fIndexField, fMultiIndexField, fDtype, fCharToInt, fTag, fBv, fType,
      fChar, fNull, fSetUnion, fSetIntersection, fSetDifference, fSetUnionOne,
      fSetEmpty, fSeqEmpty, fSeqBuild, fSeqAppend, fSeqDrop, fSeqTake,
      fSeqUpdate, fSeqCreate, fReal, fU2Real, fBool, fU2Bool, fInt, fU2Int,
      fMapDomain, fMapElements, fMapBuild, fIs, fIsBox;
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


    public DafnyModel(Model model, DafnyOptions options) {
      Model = model;
      this.options = options;
      fSetSelect = MergeMapSelectFunctions(2);
      fSeqLength = model.MkFunc("Seq#Length", 1);
      fSeqBuild = model.MkFunc("Seq#Build", 2);
      fSeqAppend = model.MkFunc("Seq#Append", 2);
      fSeqDrop = model.MkFunc("Seq#Drop", 2);
      fSeqTake = model.MkFunc("Seq#Take", 2);
      fSeqIndex = model.MkFunc("Seq#Index", 2);
      fSeqUpdate = model.MkFunc("Seq#Update", 3);
      fSeqCreate = model.MkFunc("Seq#Create", 4);
      fSeqEmpty = model.MkFunc("Seq#Empty", 1);
      fSetEmpty = model.MkFunc("Set#Empty", 1);
      fSetUnion = model.MkFunc("Set#Union", 2);
      fSetUnionOne = model.MkFunc("Set#UnionOne", 2);
      fSetIntersection = model.MkFunc("Set#Intersection", 2);
      fSetDifference = model.MkFunc("Set#Difference", 2);
      fMapDomain = model.MkFunc("Map#Domain", 1);
      fMapElements = model.MkFunc("Map#Elements", 1);
      fMapBuild = model.MkFunc("Map#Build", 3);
      fIs = model.MkFunc("$Is", 2);
      fIsBox = model.MkFunc("$IsBox", 2);
      fBox = model.MkFunc("$Box", 1);
      fDim = model.MkFunc("FDim", 1);
      fIndexField = model.MkFunc("IndexField", 1);
      fMultiIndexField = model.MkFunc("MultiIndexField", 2);
      fDtype = model.MkFunc("dtype", 1);
      fNull = model.MkFunc("null", 0);
      fCharToInt = model.MkFunc("char#ToInt", 1);
      fType = model.MkFunc("type", 1);
      fChar = model.MkFunc("charType", 0);
      fReal = model.MkFunc("realType", 0);
      fU2Real = model.MkFunc("U_2_real", 1);
      fBool = model.MkFunc("boolType", 0);
      fU2Bool = model.MkFunc("U_2_bool", 1);
      fInt = model.MkFunc("intType", 0);
      fU2Int = model.MkFunc("U_2_int", 1);
      fTag = model.MkFunc("Tag", 1);
      fBv = model.MkFunc("TBitvector", 1);
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

    /// <summary>
    /// Create a new function that merges together the applications of all the
    /// functions that have a certain arity and whose name matches the
    /// "^MapType[0-9]*Select$" pattern. This has previously been done by
    /// Boogie's Model Parser as a preprocessing step but has been deprecated
    /// since 2.9.2
    /// </summary>
    private Model.Func MergeMapSelectFunctions(int arity) {
      var name = "[" + arity + "]";
      if (Model.HasFunc(name)) {
        // Coming up with a new name if the ideal one is reserved
        int id = 0;
        while (Model.HasFunc(name + "#" + id)) {
          id++;
        }
        name += "#" + id;
      }
      var result = Model.MkFunc(name, arity);
      var mapTypeSelect = new Regex("^MapType[0-9]*Select$");
      foreach (var func in Model.Functions) {
        if (!mapTypeSelect.IsMatch(func.Name) ||
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
      !name.StartsWith("$") && !name.Contains("##");

    /// <summary>
    /// Return true iff element is a BitVector object (not to be confused an
    /// instance of Model.BitVector, which is a BitVector value)
    /// </summary>
    private static bool IsBitVectorObject(Model.Element element, DafnyModel model) =>
      BvTypeRegex.IsMatch(GetTrueName(model.fType.OptEval(element)) ?? "");

    /// <summary>
    /// Return True iff the given element has primitive type in Dafny or is null
    /// </summary>
    public static bool IsPrimitive(Model.Element element, DafnyModelState state) =>
      (element.Kind != Model.ElementKind.Uninterpreted
       || element == state.Model.fNull.GetConstant()
       || state.Model.fType.OptEval(element) == state.Model.fChar.GetConstant()
       || state.Model.fType.OptEval(element) == state.Model.fReal.GetConstant()
       || state.Model.fType.OptEval(element) == state.Model.fInt.GetConstant()
       || state.Model.fType.OptEval(element) == state.Model.fBool.GetConstant()
       || IsBitVectorObject(element, state.Model)) &&
      element.Kind != Model.ElementKind.Array &&
      (element.Kind != Model.ElementKind.DataValue ||
       ((Model.DatatypeValue)element).ConstructorName is "-" or "/");

    /// <summary>
    /// Return the name of the 0-arity function that maps to the element if such
    /// a function exists and is unique. Return null otherwise
    /// </summary>
    private static string GetTrueName(Model.Element element) {
      string name = null;
      if (element == null) {
        return null;
      }

      foreach (var funcTuple in element.Names) {
        if (funcTuple.Func.Arity != 0) {
          continue;
        }
        if ((name == null) || name.Contains("$")) { // 2nd case is type param
          name = funcTuple.Func.Name;
        } else if (!funcTuple.Func.Name.Contains("$")) {
          return null;
        }
      }
      return name;
    }

    /// <summary>
    /// Get Boogie type. This returns the Boogie type associated
    /// with the element
    /// </summary>
    private string GetBoogieType(Model.Element element) {
      var typeElement = fType.OptEval(element);
      if (typeElement == null) {
        return null;
      }
      var name = GetTrueName(typeElement);
      if (Model.TryGetFunc("SeqTypeInv0")?.OptEval(typeElement) != null) {
        return "SeqType";
      }
      if (Model.TryGetFunc("MapType0TypeInv0")?.OptEval(typeElement) != null) {
        return "SetType";
      }
      if (Model.TryGetFunc("MapTypeInv0")?.OptEval(typeElement) != null) {
        return "MapType";
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
      foreach (var tuple in fIs.AppsWithArg(0, element)) {
        if (((Model.Boolean)tuple.Result).Value) {
          result.Add(tuple.Args[1]);
        }
      }
      return result;
    }

    /// <summary> Get the Dafny type of an Uninterpreted element </summary>
    private Type GetDafnyType(Model.Uninterpreted element) {
      var boogieType = GetBoogieType(element);
      List<Model.Element> isOfType;
      List<Type> typeArgs = new();
      switch (boogieType) {
        case "intType":
          return Type.Int;
        case "realType":
          return Type.Real;
        case "charType":
          return Type.Char;
        case "boolType":
          return Type.Bool;
        case "SeqType":
          isOfType = GetIsResults(element);
          foreach (var isType in isOfType) {
            if (isType.Names.Any(app => app.Func.Name == "TSeq")) {
              return ReconstructType(isType);
            }
          }
          var seqOperation = fSeqAppend.AppWithResult(element);
          seqOperation ??= fSeqDrop.AppWithResult(element);
          seqOperation ??= fSeqTake.AppWithResult(element);
          seqOperation ??= fSeqUpdate.AppWithResult(element);
          if (boogieType == "SeqType" && seqOperation != null) {
            foreach (var arg in seqOperation.Args) {
              if (arg == element || GetBoogieType(arg) != "SeqType") {
                continue;
              }
              return GetDafnyType(arg);
            }
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
          return new SeqType(UnknownType);
        case "SetType":
          isOfType = GetIsResults(element);
          foreach (var isType in isOfType) {
            if (isType.Names.Any(app => app.Func.Name == "TSet")) {
              return ReconstructType(isType);
            }
          }
          var setOperation = fSetUnion.AppWithResult(element);
          setOperation ??= fSetIntersection.AppWithResult(element);
          setOperation ??= fSetDifference.AppWithResult(element);
          if (boogieType == "SetType" && setOperation != null) {
            foreach (var arg in setOperation.Args) {
              if (arg == element || GetBoogieType(arg) != "SetType") {
                continue;
              }
              return GetDafnyType(arg);
            }
          }
          setOperation = fSetUnionOne.AppWithResult(element);
          if (setOperation != null) {
            return new SetType(true, GetDafnyType(Unbox(setOperation.Args[1])));
          }
          setOperation = fSetEmpty.AppWithResult(element);
          if (setOperation != null) {
            return new SetType(true, ReconstructType(setOperation.Args.First()));
          }
          return new SetType(true, UnknownType);
        case "DatatypeTypeType":
          isOfType = GetIsResults(element);
          if (isOfType.Count > 0) {
            return new DafnyModelTypeUtils.DatatypeType(
              (ReconstructType(isOfType[0]) as UserDefinedType) ?? UnknownType);
          }
          return new DafnyModelTypeUtils.DatatypeType(UnknownType);
        case "MapType":
          isOfType = GetIsResults(element);
          foreach (var isType in isOfType) {
            if (isType.Names.Any(app => app.Func.Name == "TMap")) {
              return ReconstructType(isType);
            }
          }
          var mapOperation = fMapBuild.AppWithResult(element);
          if (mapOperation != null) {
            return GetDafnyType(mapOperation.Args.First());
          }
          return new Microsoft.Dafny.MapType(true, UnknownType, UnknownType);
        case "refType":
          var typeElement = fDtype.OptEval(element);
          if (typeElement != null) {
            return ReconstructType(typeElement);
          }
          // if typeElement == null, this object has a null value
          isOfType = GetIsResults(element);
          if (isOfType.Count > 0) {
            return ReconstructType(isOfType[0]);
          }
          return UnknownType;
        case null:
          return UnknownType;
        case var bv when BvTypeRegex.IsMatch(bv):
          return new BitvectorType(options, int.Parse(bv[2..^4]));
        case "BoxType":
          var unboxedTypes = fIsBox.AppsWithArg(0, element)
            .Where(tuple => ((Model.Boolean)tuple.Result).Value)
            .Select(tuple => tuple.Args[1]).ToList();
          if (unboxedTypes.Count == 1) {
            return ReconstructType(unboxedTypes[0]);
          }
          return UnknownType;
        case "HandleTypeType":
          isOfType = GetIsResults(element);
          if (isOfType.Count > 0) {
            return ReconstructType(isOfType[0]);
          }
          return UnknownType;
        default:
          return UnknownType;
      }
    }

    /// <summary>
    /// Reconstruct Dafny type from an element that represents a type in Z3
    /// </summary>
    private Type ReconstructType(Model.Element typeElement) {
      if (typeElement == null) {
        return UnknownType;
      }
      var fullName = GetTrueName(typeElement);
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
      var tagName = GetTrueName(tagElement);
      if (tagName == null || (tagName.Length < 10 && tagName != "TagSeq" &&
                              tagName != "TagSet" &&
                              tagName != "TagBitVector" &&
                              tagName != "TagMap")) {
        return fallBackType;
      }
      var typeArgs = Model.GetFunc("T" + tagName.Substring(3))?.
        AppWithResult(typeElement)?.
        Args.Select(e =>
          GetBoogieType(e) == "DatatypeTypeType" ?
          new DafnyModelTypeUtils.DatatypeType((ReconstructType(e) as UserDefinedType) ?? UnknownType) :
          ReconstructType(e)).ToList();
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
    public string CanonicalName(Model.Element elt) {
      if (elt == null) {
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
      if (IsBitVectorObject(elt, this)) {
        var typeName = GetTrueName(fType.OptEval(elt));
        var funcName = "U_2_" + typeName[..^4];
        int width = int.Parse(typeName[2..^4]);
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
          return "-" + CanonicalName(((Model.DatatypeValue)elt).Arguments.First());
        }
        if (((Model.DatatypeValue)elt).ConstructorName == "/") {
          return CanonicalName(((Model.DatatypeValue)elt).Arguments.First()) +
                 "/" + CanonicalName(((Model.DatatypeValue)elt).Arguments[1]);
        }
      }
      if (datatypeValues.TryGetValue(elt, out var fnTuple)) {
        return fnTuple.Func.Name.Split(".").Last();
      }
      if (fType.OptEval(elt) == fChar.GetConstant()) {
        if (fCharToInt.OptEval(elt) != null) {
          if (int.TryParse(((Model.Integer)fCharToInt.OptEval(elt)).Numeral,
                out var UTFCode) && UTFCode is <= char.MaxValue and >= 0) {
            return PrettyPrintChar(UTFCode);
          }
        }
        return GetUnreservedCharValue(elt);
      }
      if (fType.OptEval(elt) == fReal.GetConstant()) {
        if (fU2Real.OptEval(elt) != null) {
          return CanonicalName(fU2Real.OptEval(elt));
        }
        return GetUnreservedNumericValue(elt, Type.Real);
      }
      if (fType.OptEval(elt) == fBool.GetConstant()) {
        if (fU2Bool.OptEval(elt) != null) {
          return CanonicalName(fU2Bool.OptEval(elt));
        }
        return GetUnreservedBoolValue(elt);
      }
      if (fType.OptEval(elt) == fInt.GetConstant()) {
        if (fU2Int.OptEval(elt) != null) {
          return CanonicalName(fU2Int.OptEval(elt));
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
    private List<Model.Func> GetDestructorFunctions(Model.Element datatypeElement) {
      var possiblyNullableTypes = GetIsResults(datatypeElement)
        .Select(isResult => ReconstructType(isResult) as UserDefinedType)
        .Where(type => type != null && type.Name != UnknownType.Name);
      var types = possiblyNullableTypes.Select(type => DafnyModelTypeUtils.GetNonNullable(type) as UserDefinedType);
      List<Model.Func> result = new();
      var builtInDatatypeDestructor = new Regex("^.*[^_](__)*_q$");
      foreach (var app in datatypeElement.References) {
        if (app.Func.Arity != 1 || app.Args[0] != datatypeElement ||
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
            Console.Out.WriteLine(PleaseEnableModelCompressFalse);
            continue;
          }
          indices[i] = dimTuple.Args[0];
        } else {
          dimTuple = fMultiIndexField.AppWithResult(elt);
          if (dimTuple == null) {
            Console.Out.WriteLine(PleaseEnableModelCompressFalse);
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
