// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace DafnyServer.CounterexampleGeneration {

  /// <summary>
  /// a wrapper around Boogie's Model class that
  /// defines Dafny specific functions and provides functionality for extracting
  /// types and values of Elements representing Dafny variables. The three core
  /// methods are: GetDafnyType, CanonicalName, and GetExpansion
  /// </summary>
  public class DafnyModel {

    public readonly Model Model;
    public readonly List<DafnyModelState> States = new();
    private readonly Model.Func fSetSelect, fSeqLength, fSeqIndex, fBox,
      fDim, fIndexField, fMultiIndexField, fDtype, fCharToInt, fTag, fBv, fType,
      fChar, fNull, fSetUnion, fSetIntersection, fSetDifference, fSetUnionOne,
      fSetEmpty, fSeqEmpty, fSeqBuild, fSeqAppend, fSeqDrop, fSeqTake,
      fSeqUpdate, fSeqCreate, fReal, fU2Real, fBool, fU2Bool, fInt, fU2Int,
      fMapDomain, fMapElements, fMapBuild;
    private readonly Dictionary<Model.Element, Model.Element[]> arrayLengths = new();
    private readonly Dictionary<Model.Element, Model.FuncTuple> datatypeValues = new();
    private readonly Dictionary<Model.Element, string> localValue = new();
    // Maps an element's id to another unique id. This can be used to
    // distinguish between basic-typed variables for which the model does not
    // specify values. This mapping makes ids shorter since there are fewer such
    // elements than there are elements in general.
    private readonly Dictionary<int, int> shortElementIds = new();


    public DafnyModel(Model model) {
      Model = model;
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
      InitArraysAndDataTypes();
      foreach (var s in model.States) {
        var sn = new DafnyModelState(this, s);
        States.Add(sn);
      }
    }

    /// <summary>
    /// Extract and parse the first Dafny model recorded in the model view file.
    /// </summary>
    public static DafnyModel ExtractModel(string mv) {
      const string begin = "*** MODEL";
      const string end = "*** END_MODEL";
      var beginIndex = mv.IndexOf(begin, StringComparison.Ordinal);
      var endIndex = mv.IndexOf(end, StringComparison.Ordinal);
      var modelString = mv.Substring(beginIndex, endIndex + end.Length - beginIndex);
      var model = Model.ParseModels(new StringReader(modelString)).First();
      return new DafnyModel(model);
    }

    /// <summary>
    /// Collect the array dimensions from the various array.Length functions,
    /// and collect all known datatype values
    /// </summary>
    private void InitArraysAndDataTypes() {
      foreach (var fn in Model.Functions) {
        if (Regex.IsMatch(fn.Name, "^_System.array[0-9]*.Length[0-9]*$")) {
          var j = fn.Name.IndexOf('.', 13);
          var dims = j == 13 ? 1 : int.Parse(fn.Name.Substring(13, j - 13));
          var idx = j == 13 ? 0 : int.Parse(fn.Name[(j + 7)..]);
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Args[0];
            var len = tpl.Result;
            if (!arrayLengths.TryGetValue(elt, out var ar)) {
              ar = new Model.Element[dims];
              arrayLengths.Add(elt, ar);
            }
            Contract.Assert(ar[idx] == null);
            ar[idx] = len;
          }
        } else if (fn.Name.StartsWith("#") && fn.Name.IndexOf('.') != -1 && fn.Name[1] != '#') {
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Result;
            datatypeValues.Add(elt, tpl);
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
        var id = 0;
        while (Model.HasFunc(name + "#" + id)) {
          id++;
        }
        name += "#" + id;
      }
      var result = Model.MkFunc(name, arity);
      foreach (var func in Model.Functions) {
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
      Regex.IsMatch(GetTrueName(model.fType.OptEval(element))
                    ?? "", "^bv[0-9]+Type$");

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
        if (name == null) {
          name = funcTuple.Func.Name;
        } else {
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
      var typeElement = Model.GetFunc("type").OptEval(element);
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
    internal DafnyModelType GetDafnyType(Model.Element element) {
      switch (element.Kind) {
        case Model.ElementKind.Boolean:
          return new DafnyModelType("bool");
        case Model.ElementKind.Integer:
          return new DafnyModelType("int");
        case Model.ElementKind.Real:
          return new DafnyModelType("real");
        case Model.ElementKind.BitVector:
          return new DafnyModelType("bv" + ((Model.BitVector)element).Size);
        case Model.ElementKind.Uninterpreted:
          return GetDafnyType(element as Model.Uninterpreted);
        case Model.ElementKind.DataValue:
          if (((Model.DatatypeValue)element).ConstructorName is "-" or "/") {
            return GetDafnyType(
              ((Model.DatatypeValue)element).Arguments.First());
          }
          return new DafnyModelType("?"); // This shouldn't be reachable.
        default:
          return new DafnyModelType("?");
      }
    }

    /// <summary>
    /// Return all elements x that satisfy ($Is element x)
    /// </summary>
    private List<Model.Element> GetIsResults(Model.Element element) {
      List<Model.Element> result = new();
      foreach (var tuple in Model.GetFunc("$Is").AppsWithArg(0, element)) {
        if (((Model.Boolean)tuple.Result).Value) {
          result.Add(tuple.Args[1]);
        }
      }
      return result;
    }

    /// <summary> Get the Dafny type of an Uninterpreted element </summary>
    private DafnyModelType GetDafnyType(Model.Uninterpreted element) {
      var boogieType = GetBoogieType(element);
      List<Model.Element> isOfType;
      List<DafnyModelType> typeArgs = new();
      switch (boogieType) {
        case "intType":
        case "realType":
        case "charType":
        case "boolType":
          return new DafnyModelType(boogieType.Substring(0, boogieType.Length - 4));
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
            typeArgs.Add(GetDafnyType(Unbox(seqOperation.Args[1])));
            return new DafnyModelType("seq", typeArgs);
          }
          seqOperation = fSeqCreate.AppWithResult(element);
          seqOperation ??= fSeqEmpty.AppWithResult(element);
          if (seqOperation != null) {
            typeArgs.Add(ReconstructType(seqOperation.Args.First()));
            return new DafnyModelType("seq", typeArgs);
          }
          typeArgs.Add(new("?"));
          return new DafnyModelType("seq", typeArgs);
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
            typeArgs.Add(GetDafnyType(Unbox(setOperation.Args[1])));
            return new DafnyModelType("set", typeArgs);
          }
          setOperation = fSetEmpty.AppWithResult(element);
          if (setOperation != null) {
            typeArgs.Add(ReconstructType(setOperation.Args.First()));
            return new DafnyModelType("set", typeArgs);
          }
          typeArgs.Add(new("?"));
          return new DafnyModelType("set", typeArgs);
        case "DatatypeTypeType":
          isOfType = GetIsResults(element);
          if (isOfType.Count > 0) {
            return ReconstructType(isOfType[0]);
          }
          return new DafnyModelType("?");
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
          return new DafnyModelType("map", new List<DafnyModelType> { new("?"), new("?") });
        case "refType":
          return ReconstructType(fDtype.OptEval(element));
        case null:
          return new DafnyModelType("?");
        case var bv when new Regex("^bv[0-9]+Type$").IsMatch(bv):
          return new DafnyModelType(bv.Substring(0, bv.Length - 4));
        default:
          return new DafnyModelType("?");
      }
    }

    /// <summary>
    /// Reconstruct Dafny type from an element that represents a type in Z3
    /// </summary>
    private DafnyModelType ReconstructType(Model.Element typeElement) {
      if (typeElement == null) {
        return new DafnyModelType("?");
      }
      var fullName = GetTrueName(typeElement);
      if (fullName != null && fullName.Length > 7) {
        return new DafnyModelType(fullName.Substring(7));
      }
      if (fullName is "TInt" or "TReal" or "TChar" or "TBool") {
        return new DafnyModelType(fullName.Substring(1).ToLower());
      }
      if (fBv.AppWithResult(typeElement) != null) {
        return new DafnyModelType("bv" + ((Model.Integer)fBv.AppWithResult(typeElement).Args[0]).AsInt());
      }
      var tagElement = fTag.OptEval(typeElement);
      if (tagElement == null) {
        return new DafnyModelType("?");
      }
      var tagName = GetTrueName(tagElement);
      if (tagName == null || (tagName.Length < 10 && tagName != "TagSeq" &&
                              tagName != "TagSet" &&
                              tagName != "TagBitVector" &&
                              tagName != "TagMap")) {
        return new DafnyModelType("?");
      }
      var typeArgs = Model.GetFunc("T" + tagName.Substring(3))?.
        AppWithResult(typeElement)?.
        Args.ToList();
      tagName = tagName switch {
        "TagSeq" => "seq",
        "TagMap" => "map",
        "TagSet" => "set",
        _ => tagName.Substring(9)
      };
      if (typeArgs == null) {
        return new DafnyModelType(tagName);
      }
      return new DafnyModelType(tagName, typeArgs.ConvertAll(ReconstructType));
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
        return vector.AsInt().ToString();
      }
      if (IsBitVectorObject(elt, this)) {
        var typeName = GetTrueName(fType.OptEval(elt));
        var funcName = "U_2_" + typeName[..^4];
        if (!Model.HasFunc(funcName)) {
          return "?#" + GetShortElementId(elt);
        }
        if (Model.GetFunc(funcName).OptEval(elt) != null) {
          return Model.GetFunc(funcName).OptEval(elt).AsInt().ToString();
        }
        return "?#" + GetShortElementId(elt);
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
        int utfCode;
        if (fCharToInt.OptEval(elt) != null) {
          utfCode = ((Model.Integer)fCharToInt.OptEval(elt)).AsInt();
          return "'" + char.ConvertFromUtf32(utfCode) + "'";
        }
        return "?#" + GetShortElementId(elt);
      }
      if (fType.OptEval(elt) == fReal.GetConstant()) {
        if (fU2Real.OptEval(elt) != null) {
          return CanonicalName(fU2Real.OptEval(elt));
        }
        return "?#" + GetShortElementId(elt);
      }
      if (fType.OptEval(elt) == fBool.GetConstant()) {
        if (fU2Bool.OptEval(elt) != null) {
          return CanonicalName(fU2Bool.OptEval(elt));
        }
        return "?#" + GetShortElementId(elt);
      }
      if (fType.OptEval(elt) == fInt.GetConstant()) {
        if (fU2Int.OptEval(elt) != null) {
          return CanonicalName(fU2Int.OptEval(elt));
        }
        return "?#" + GetShortElementId(elt);
      }
      return "";
    }

    private int GetShortElementId(Model.Element element) {
      if (!shortElementIds.ContainsKey(element.Id)) {
        shortElementIds[element.Id] = shortElementIds.Count;
      }
      return shortElementIds[element.Id];
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
        var destructors = GetDestructorFunctions(var.Element, var.Type.Name);
        if (destructors.Count == fnTuple.Args.Length) {
          // we know all destructor names
          foreach (var func in destructors) {
            result.Add(DafnyModelVariableFactory.Get(state, Unbox(func.OptEval(var.Element)),
              func.Name.Split(".").Last(), var));
          }
        } else {
          // we don't now destructor names, so we use indices instead
          for (var i = 0; i < fnTuple.Args.Length; i++) {
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
        // Sequence can be constructed with build operator:
        List<Model.Element> elements = new();
        var substring = var.Element;
        while (fSeqBuild.AppWithResult(substring) != null) {
          elements.Insert(0, Unbox(fSeqBuild.AppWithResult(substring).Args[1]));
          substring = fSeqBuild.AppWithResult(substring).Args[0];
        }
        for (var i = 0; i < elements.Count; i++) {
          var e = DafnyModelVariableFactory.Get(state, Unbox(elements[i]), "[" + i + "]", var);
          result.Add(e);
          (var as SeqVariable)?.AddAtIndex(e, i);
        }
        if (elements.Count > 0) {
          return result;
        }
        // Otherwise, sequence can be reconstructed index by index:
        foreach (var tpl in fSeqIndex.AppsWithArg(0, var.Element)) {
          var e = DafnyModelVariableFactory.Get(state, Unbox(tpl.Result),
            "[" + tpl.Args[1] + "]", var);
          result.Add(e);
          (var as SeqVariable)?.AddAtIndex(e, (tpl.Args[1] as Model.Integer)?.AsInt());
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
      var mapBuild = fMapBuild.AppWithResult(var.Element);
      while (mapBuild != null) {
        var key = DafnyModelVariableFactory.Get(state, Unbox(mapBuild.Args[1]), "", var);
        var value = DafnyModelVariableFactory.Get(state, Unbox(mapBuild.Args[2]), "", var);
        result.Add(key);
        result.Add(value);
        ((MapVariable)var).AddMapping(key, value);
        mapDomain = fMapDomain.OptEval(mapBuild.Args[0]);
        mapElements = fMapElements.OptEval(mapBuild.Args[0]);
        if (fMapBuild.AppWithResult(mapBuild.Args[0]) == mapBuild) {
          break; // can happen when constructing maps with single application
        }
        mapBuild = fMapBuild.AppWithResult(mapBuild.Args[0]);
      }
      if (mapDomain != null && mapElements != null) {
        foreach (var app in fSetSelect.AppsWithArg(0, mapDomain)) {
          if (!((Model.Boolean)app.Result).Value) {
            continue;
          }
          var key = DafnyModelVariableFactory.Get(state, Unbox(app.Args[1]), "", var);
          result.Add(key);
          var valueElement = fSetSelect.OptEval(mapElements, app.Args[1]);
          if (valueElement == null) {
            ((MapVariable)var).AddMapping(key, null);
          } else {
            var value = DafnyModelVariableFactory.Get(state, Unbox(valueElement), "", var);
            result.Add(value);
            ((MapVariable)var).AddMapping(key, value);
          }
        }
      }

      if (arrayLengths.TryGetValue(var.Element, out var lengths)) {
        // Elt is an array
        var i = 0;
        foreach (var len in lengths) {
          var name = lengths.Length == 1 ? "Length" : "Length" + i;
          result.Add(DafnyModelVariableFactory.Get(state, len, name, var));
          i++;
        }
      }
      // Elt is an array or an object:
      var heap = state.State.TryGet("$Heap");
      if (heap == null) {
        return result;
      }
      var instances = fSetSelect.AppsWithArgs(0, heap, 1, var.Element);
      if (instances == null || !instances.Any()) {
        return result;
      }
      foreach (var tpl in fSetSelect.AppsWithArg(0, instances.ToList()[0].Result)) {
        var fieldName = GetFieldName(tpl.Args[1]);
        if (fieldName != "alloc") {
          result.Add(DafnyModelVariableFactory.Get(state, Unbox(tpl.Result), fieldName, var));
        }
      }
      return result;
    }

    /// <summary>
    /// Return all functions that map the datatype object to a particular
    /// destructor value.
    /// </summary>
    private static List<Model.Func> GetDestructorFunctions(Model.Element datatype, string type) {
      List<Model.Func> result = new();
      foreach (var app in datatype.References) {
        if (app.Func.Arity != 1 || app.Args[0] != datatype ||
            !app.Func.Name.StartsWith(type + ".") ||
            Regex.IsMatch(app.Func.Name.Split(".").Last(), "^.*[^_](__)*_q$")) {
          // the regex is for built-in datatype destructors
          continue;
        }
        result.Add(app.Func);
      }
      return result;
    }

    /// <summary>
    /// Return the name of the field represented by the given element.
    /// Special care is required if the element represents an array index
    /// </summary>
    private string GetFieldName(Model.Element elt) {
      var dims = fDim.OptEval(elt)?.AsInt();
      if (dims is null or 0) { // meaning elt is not an array index
        var fieldName = GetTrueName(elt);
        if (fieldName == null) {
          return elt.ToString();
        }
        return fieldName.Split(".").Last();
      }
      // Reaching this code means elt is an index into an array
      var indices = new Model.Element[(int)dims];
      for (var i = (int)dims; 0 <= --i;) {
        Model.FuncTuple dimTuple;
        if (i == 0) {
          dimTuple = fIndexField.AppWithResult(elt);
          indices[i] = dimTuple.Args[0];
        } else {
          dimTuple = fMultiIndexField.AppWithResult(elt);
          indices[i] = dimTuple.Args[1];
          elt = dimTuple.Args[0];
        }
      }
      return "[" + string.Join(",", indices.ToList().
        ConvertAll(element => element.ToString())) + "]";
    }

    /// <summary> Unboxes an element, if possible </summary>
    private Model.Element Unbox(Model.Element elt) {
      var unboxed = fBox.AppWithResult(elt);
      return unboxed != null ? unboxed.Args[0] : elt;
    }

    public void RegisterLocalValue(string name, Model.Element elt) {
      if (localValue.TryGetValue(elt, out var curr) &&
          CompareFieldNames(name, curr) >= 0) {
        return;
      }
      localValue[elt] = name;
    }

    private static ulong GetNumber(string s, int beg) {
      ulong res = 0;
      while (beg < s.Length) {
        var c = s[beg];
        if ('0' <= c && c <= '9') {
          res *= 10;
          res += (uint)c - '0';
        }
        beg++;
      }
      return res;
    }

    private static int CompareFieldNames(string f1, string f2) {
      var len = Math.Min(f1.Length, f2.Length);
      var numberPos = -1;
      for (var i = 0; i < len; ++i) {
        var c1 = f1[i];
        var c2 = f2[i];
        if ('0' <= c1 && c1 <= '9' && '0' <= c2 && c2 <= '9') {
          numberPos = i;
          break;
        }
        if (c1 != c2) {
          break;
        }
      }
      if (numberPos >= 0) {
        var v1 = GetNumber(f1, numberPos);
        var v2 = GetNumber(f2, numberPos);
        if (v1 < v2) {
          return -1;
        }
        if (v1 > v2) {
          return 1;
        }
      }
      return string.CompareOrdinal(f1, f2);
    }
  }
}
