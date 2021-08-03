// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace DafnyServer.CounterExampleGeneration {

  public class DafnyModel {
  
    public readonly Model Model;
    public readonly List<DafnyModelState> States = new();
    private readonly Model.Func fSetSelect, fSeqLength, fSeqIndex, fBox, 
      fDim, fIndexField, fMultiIndexField, fDtype, fCharToInt, fTag, fBv, fType,
      fChar, fNull, fSetUnion, fSetIntersection, fSetDifference, fSeqBuild,
      fSeqAppend, fSeqDrop, fSeqTake, fSeqUpdate, fSeqCreate, fReal, fU2Real,
      fBool, fU2Bool, fInt, fU2Int;
    private readonly Dictionary<Model.Element, Model.Element[]> arrayLengths = new();
    private readonly Dictionary<Model.Element, Model.FuncTuple> datatypeValues = new();
    private readonly Dictionary<Model.Element, string> localValue = new();


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
      fSetUnion = model.MkFunc("Set#Union", 2);
      fSetIntersection = model.MkFunc("Set#Intersection", 2);
      fSetDifference = model.MkFunc("Set#Difference", 2);
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
      InitArraysAndDatatypes();
      foreach (var s in model.States) {
        var sn = new DafnyModelState(this, s);
        States.Add(sn);
      }
      InitCharValues();
    }

    /// <summary>
    /// Collect the array dimensions from the various array.Length functions,
    /// and collect all known datatype values
    /// </summary>
    private void InitArraysAndDatatypes() {
      foreach (var fn in Model.Functions) {
        if (Regex.IsMatch(fn.Name, "^_System.array[0-9]*.Length[0-9]*$")) {
          var j = fn.Name.IndexOf('.', 13);
          var dims = j == 13 ? 1 : int.Parse(fn.Name.Substring(13, j - 13));
          var idx = j == 13 ? 0 : int.Parse(fn.Name.Substring(j + 7));
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
        }
        else if (fn.Name.StartsWith("#") && fn.Name.IndexOf('.') != -1 && fn.Name[1] != '#') {
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Result;
            datatypeValues.Add(elt, tpl);
          }
        }
      }
    }

    private void InitCharValues() {
      foreach (var state in States) {
        state.SetupUniqueIds(fCharToInt.Name, fCharToInt.Apps.ToList()
          .ConvertAll(app => ((Model.Integer) app.Result).AsInt()));
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
       ((Model.DatatypeValue) element).ConstructorName is "-" or "/");
    
    /// <summary>
    /// Return the name of the 0-arity function that maps to the element if such
    /// a function exists and is unique. Return null otherwise
    /// </summary>
    private static string GetTrueName(Model.Element element) {
      string name = null;
      if (element == null)
        return null;
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
      if (name != null) {
        return name;
      }
      if (Model.GetFunc("SeqTypeInv0").OptEval(typeElement) != null) {
        return "SeqType";
      }
      if (Model.GetFunc("MapType0TypeInv0").OptEval(typeElement) != null) {
        return "SetType";
      }
      return null;
    }
    
    /// <summary> Get the Dafny type of an element </summary>
    internal string GetDafnyType(Model.Element element) {
      switch (element.Kind) {
        case Model.ElementKind.Boolean: 
          return "bool";
        case Model.ElementKind.Integer:
          return "int";
        case Model.ElementKind.Real:
          return "real";
        case Model.ElementKind.BitVector:
          return "bv" + ((Model.BitVector) element).Size;
        case Model.ElementKind.Uninterpreted:
          return GetDafnyType(element as Model.Uninterpreted);
        case Model.ElementKind.DataValue:
          if (((Model.DatatypeValue) element).ConstructorName is "-" or "/") {
            return GetDafnyType(
              ((Model.DatatypeValue) element).Arguments.First());
          }
          return "?"; // This shouldn't be reachable.
        default:
          return "?";
      }
    }

    /// <summary>
    /// Return all elements x that satisfy ($Is element x)
    /// </summary>
    private List<Model.Element> GetIsResults(Model.Element element) {
      List<Model.Element> result = new();
      foreach (var tuple in Model.GetFunc("$Is").AppsWithArg(0, element)) {
        if (((Model.Boolean) tuple.Result).Value) {
          result.Add(tuple.Args[1]);
        }
      }
      return result;
    }

    /// <summary> Get the Dafny type of an Uninterpreted element </summary>
    private string GetDafnyType(Model.Uninterpreted element) {
      var boogieType = GetBoogieType(element);
      switch (boogieType) {
        case "intType": case "realType": case "charType": case "boolType":
          return boogieType.Substring(0, boogieType.Length - 4);
        case "SeqType":
        case "SetType":
        case "DatatypeTypeType":
          var isOfType = GetIsResults(element);
          if (isOfType.Count > 0) {
            return ReconstructType(isOfType[0]);
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
          seqOperation = fSeqCreate.AppWithResult(element);
          if (seqOperation != null) {
            return "seq<" + ReconstructType(seqOperation.Args.First()) + ">";
          }
          return "?";
        case "refType":
          return ReconstructType(fDtype.OptEval(element));
        case null:
          return "?";
        case var bv when new Regex("^bv[0-9]+Type$").IsMatch(bv):
          return bv.Substring(0, bv.Length - 4);
        default:
          return "?";
      }
    }

    /// <summary>
    /// Reconstruct Dafny type from an element that represents a type in Z3
    /// </summary>
    private string ReconstructType(Model.Element typeElement) {
      if (typeElement == null) {
        return "?";
      }
      var fullName = GetTrueName(typeElement);
      if (fullName != null && fullName.Length > 7) {
        return fullName.Substring(7); 
      }
      if (fullName is "TInt" or "TReal" or "TChar" or "TBool") {
        return fullName.Substring(1).ToLower();
      }
      if (fBv.AppWithResult(typeElement) != null) {
        return "bv" + ((Model.Integer) fBv.AppWithResult(typeElement).Args[0]).AsInt();
      }
      var tagElement = fTag.OptEval(typeElement);
      if (tagElement == null) {
        return "?";
      }
      var tagName = GetTrueName(tagElement);
      if (tagName == null || tagName.Length < 10 && tagName != "TagSeq" &&
                              tagName != "TagSet" &&
                              tagName != "TagBitVector") {
        return "?";
      }
      var typeArgs = Model.GetFunc("T" + tagName.Substring(3))?.
        AppWithResult(typeElement)?.
        Args.ToList();
      tagName = tagName switch {
        "TagSeq" => "seq",
        "TagSet" => "set",
        _ => tagName.Substring(9)
      };
      if (typeArgs == null) {
        return tagName;
      }
      return tagName + "<" + String.Join(",", typeArgs.ConvertAll(t => ReconstructType(t))) + ">";
    }
    
    /// <summary>
    /// Extract the string representation of the element.
    /// Returns "" if !IsPrimitive(elt, state)
    /// </summary>
    public string CanonicalName(Model.Element elt, DafnyModelState state) {
      if (elt == null) {
        return "?";
      }
      if (elt == fNull.GetConstant()) {
        return "null";
      }
      if (elt is Model.Integer or Model.Boolean or Model.BitVector or Model.Real) {
        return elt.ToString();
      }
      if (IsBitVectorObject(elt, this)) {
        var typeName = GetTrueName(fType.OptEval(elt));
        var funcName = "U_2_" + typeName[..^4];
        if (!Model.HasFunc(funcName)) {
          return "?";
        }
        if (Model.GetFunc(funcName).OptEval(elt) != null) {
          return Model.GetFunc(funcName).OptEval(elt).ToString();
        }
        return "?";
      }
      if (elt.Kind == Model.ElementKind.DataValue) {
        if (((Model.DatatypeValue) elt).ConstructorName == "-") {
          return "-" + CanonicalName(((Model.DatatypeValue) elt).Arguments.First(), state);
        }
        if (((Model.DatatypeValue) elt).ConstructorName == "/") {
          return CanonicalName(((Model.DatatypeValue) elt).Arguments.First(), state) + 
                 "/" + CanonicalName(((Model.DatatypeValue) elt).Arguments[1], state);
        }
      }
      if (datatypeValues.TryGetValue(elt, out var fnTuple)) {
        return fnTuple.Func.Name.Split(".").Last();
      }
      if (fType.OptEval(elt) == fChar.GetConstant()) {
        int utfCode;
        if (fCharToInt.OptEval(elt) != null) {
          utfCode = ((Model.Integer) fCharToInt.OptEval(elt)).AsInt();
        } else {
          // 33 is UTF for '!' that, aside from space, is first non-control char
          utfCode = state.GetUniqueId(elt, fCharToInt.Name, 33); 
        }
        try {
          return "'" + char.ConvertFromUtf32(utfCode) + "'";
        } catch (ArgumentOutOfRangeException) {
          return "?#" + utfCode;
        }
      }
      if (fType.OptEval(elt) == fReal.GetConstant()) {
        if (fU2Real.OptEval(elt) != null) {
          return CanonicalName(fU2Real.OptEval(elt), state);
        }
        return "0.0";
      }
      if (fType.OptEval(elt) == fBool.GetConstant()) {
        if (fU2Bool.OptEval(elt) != null) {
          return CanonicalName(fU2Bool.OptEval(elt), state);
        }
        return "false";
      }
      if (fType.OptEval(elt) == fInt.GetConstant()) {
        if (fU2Int.OptEval(elt) != null) {
          return CanonicalName(fU2Int.OptEval(elt), state);
        }
        return "0";
      }
      return "";
    }

    /// <summary>
    /// Return a set of variables associated with an element. These could be
    /// values of fields for objects, values at certain positions for
    /// sequences, etc.
    /// </summary>
    public IEnumerable<DafnyModelVariable> GetExpansion(DafnyModelState dafnyModelState, DafnyModelVariable var) {
      List<DafnyModelVariable> result = new ();
      if (var.Element.Kind != Model.ElementKind.Uninterpreted) {
        return result;  // primitive types can't have fields
      }
      if (datatypeValues.TryGetValue(var.Element, out var fnTuple)) {
        // Elt is a datatype value
        var i = 0;
        foreach (var arg in fnTuple.Args) {
          result.Add(DafnyModelVariable.Get(dafnyModelState, 
            Unbox(arg), 
            GetDestructorName(var.Element, arg) ?? "[" + i + "]", 
            var));
          i++;
        }
        return result;
      }
      var seqLen = fSeqLength.OptEval(var.Element);
      if (seqLen != null) { // Elt is a sequence
        result.Add(DafnyModelVariable.Get(dafnyModelState, seqLen, "Length", var));
        // Sequence can be constructed with build operator:
        List<Model.Element> elements = new();
        var substring = var.Element;
        while (fSeqBuild.AppWithResult(substring) != null) {
          elements.Insert(0, Unbox(fSeqBuild.AppWithResult(substring).Args[1]));
          substring = fSeqBuild.AppWithResult(substring).Args[0];
        }
        for (int i = 0; i < elements.Count; i++) {
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(elements[i]), "[" + i + "]", var));
        }
        if (elements.Count > 0) {
          return result;
        }
        // Otherwise, sequence can be reconstructed index by index:
        foreach (var tpl in fSeqIndex.AppsWithArg(0, var.Element)) {
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result),
            "[" + tpl.Args[1] + "]", var));
        }
        return result;
      }
      foreach (var tpl in fSetSelect.AppsWithArg(0, var.Element)) {
        var setElement = tpl.Args[1];
        var containment = tpl.Result;
        if (containment.Kind != Model.ElementKind.Boolean) {
          continue;
        }
        result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(setElement), 
          ((Model.Boolean)containment).ToString(), var));
      }
      if (result.Count != 0) { // Elt is a set
        return result;
      }
      if (arrayLengths.TryGetValue(var.Element, out var lengths)) {
        // Elt is an array
        var i = 0;
        foreach (var len in lengths) {
          var name = lengths.Length == 1 ? "Length" : "Length" + i;
          result.Add(DafnyModelVariable.Get(dafnyModelState, len, name, var));
          i++;
        }
      }
      // Elt is an array or an object:
      var heap = dafnyModelState.State.TryGet("$Heap");
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
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result), fieldName, var));
        }
      }
      return result;
    }

    /// <summary>
    /// Search for a function that maps the datatype object to a particular
    /// destructor value. Extract the name of the destructor.
    /// </summary>
    private static string GetDestructorName(Model.Element datatype,
      Model.Element destructor) {
      string name = null;
      foreach (var app in destructor.Names) {
        if (app.Func.Arity != 1 || app.Args[0] != datatype || !app.Func.Name.Contains(".")) {
          continue;
        }
        if (name != null) {
          return null;  // name must be unique
        }
        name = app.Func.Name;
      }
      return name?.Split(".").Last();
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
      var indices = new Model.Element[(int) dims];
      for (var i = (int) dims; 0 <= --i;) {
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
      return "[" + String.Join(",", indices.ToList().
        ConvertAll(x => x.ToString())) + "]";
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
