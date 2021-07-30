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
      fChar, fNull;
    private readonly Dictionary<Model.Element, Model.Element[]> arrayLengths = new();
    private readonly Dictionary<Model.Element, Model.FuncTuple> datatypeValues = new();
    private readonly Dictionary<Model.Element, string> localValue = new();
    private readonly HashSet<int> charCodes = new(); // TODO: move to DMState
    

    public DafnyModel(Model model) {
      Model = model;
      fSetSelect = MergeMapSelectFunctions(2);
      fSeqLength = model.MkFunc("Seq#Length", 1);
      fSeqIndex = model.MkFunc("Seq#Index", 2);
      fBox = model.MkFunc("$Box", 1);
      fDim = model.MkFunc("FDim", 1);
      fIndexField = model.MkFunc("IndexField", 1);
      fMultiIndexField = model.MkFunc("MultiIndexField", 2);
      fDtype = model.MkFunc("dtype", 1);
      fNull = model.MkFunc("null", 0);
      fCharToInt = model.MkFunc("char#ToInt", 1);
      fType = model.MkFunc("type", 1);
      fChar = model.MkFunc("charType", 0);
      fTag = model.MkFunc("Tag", 1);
      fBv = model.MkFunc("TBitvector", 1);
      
      InitCharCodes();

      // collect the array dimensions from the various array.Length functions, and
      // collect all known datatype values
      foreach (var fn in model.Functions) {
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
      
      foreach (var s in model.States) {
        var sn = new DafnyModelState(this, s);
        States.Add(sn);
      }
    }

    private void InitCharCodes() {
      foreach (var app in fCharToInt.Apps)
        charCodes.Add(((Model.Integer) app.Result).AsInt());
    }

    /// <summary>
    /// Creates a new function that merges together the applications of all the
    /// functions that have a certain arity and whose name matches the
    /// "^MapType[0-9]*Select$" pattern. This has previously been done by
    /// Boogie's Model Parser as a preprocessing step but has been deprecated
    /// since 2.9.2
    /// </summary>
    private Model.Func MergeMapSelectFunctions(int arity) {
      var id = arity - 1;
      // Need to make sure the name of the new function is unique
      while (Model.HasFunc("[" + ++id + "]")) { }
      var result = Model.MkFunc("[" + id + "]", arity);
      foreach (var func in Model.Functions) {
        if (!Regex.IsMatch(func.Name, "^MapType[0-9]*Select$") ||
            func.Arity != arity) continue;
        foreach (var app in func.Apps) {
          result.AddApp(app.Result, app.Args);
        }
        result.Else ??= func.Else;
      }
      return result;
    }

    public string GetUserVariableName(string name) {
      if (name.StartsWith("$")) // this covers $Heap and $_Frame and $nw...
        return null;
      if (name.Contains("##"))  // a temporary variable of the translation
        return null;
      return name;
    }
    
    public static bool IsPrimitive(Model.Element element, DafnyModelState state) =>
      (element.Kind != Model.ElementKind.Uninterpreted 
       || element == state.Model.fNull.GetConstant()
       || state.Model.fType.AppWithArg(0, element)?.Result == state.Model.fChar.GetConstant()) && 
      element.Kind != Model.ElementKind.Array && 
      (element.Kind != Model.ElementKind.DataValue || 
       ((Model.DatatypeValue) element).ConstructorName == "-");
    
    /// <summary>
    /// Return the name of the 0-arity function that maps to the element if such
    /// a function exists and is unique. Return null otherwise
    /// </summary>
    private static string GetTrueName(Model.Element element) {
      string name = null;
      foreach (var funcTuple in element.Names) {
        if (funcTuple.Func.Arity != 0)
          continue;
        if (name == null)
          name = funcTuple.Func.Name;
        else
          return null;
      }
      return name;
    }

    /// <summary>Get Boogie type. This returns the Boogie type associated
    /// with the element </summary>
    private string GetBoogieType(Model.Element element) {
      var typeElement = Model.GetFunc("type").OptEval(element);
      if (typeElement == null)
        return null;
      var name = GetTrueName(typeElement);
      if (name != null)
        return name;
      if (Model.GetFunc("SeqTypeInv0").OptEval(typeElement) != null)
        return "SeqType";
      if (Model.GetFunc("MapType0TypeInv0").OptEval(typeElement) != null)  // TODO: Not sure about this
        return "SetType";
      return null;
    }
    
    /// <summary> Get the Dafny type of the element </summary>
    /// <returns></returns>
    internal string GetDafnyType(Model.Element element) {
      switch (element.Kind) {
        case Model.ElementKind.Boolean: 
          return "bool";
        case Model.ElementKind.Integer:
          return "int";
        case Model.ElementKind.Real:
          return "real";
        case Model.ElementKind.BitVector:
          return "bv" + ((Model.BitVector) element).Size; //TODO: test this
        case Model.ElementKind.Uninterpreted:
          return GetDafnyType(element as Model.Uninterpreted);
        case Model.ElementKind.DataValue:
          if (((Model.DatatypeValue) element).ConstructorName == "-")
            return GetDafnyType(((Model.DatatypeValue) element).Arguments.First());
          return "?"; // TODO: Not sure if this can happen
        case Model.ElementKind.Array: // TODO
        default:
          return "?";
      }
    }

    /// <summary>
    /// Return all elements x that satisfy ($Is element x)
    /// </summary>
    private List<Model.Element> GetIsResults(Model.Element element) {
      List<Model.Element> result = new();
      foreach (var tuple in Model.GetFunc("$Is").AppsWithArg(0, element))
        if (((Model.Boolean) tuple.Result).Value) {
          result.Add(tuple.Args[1]);
        }
      return result;
    }

    /// <summary> Get the Dafny type of an Uninterpreted element </summary>
    private string GetDafnyType(Model.Uninterpreted element) {
      // TODO: make uses of OptEval and AppWithArg consistent
      var boogieType = GetBoogieType(element);
      switch (boogieType) {
        case "intType": case "realType": case "charType": case "boolType":
          return boogieType.Substring(0, boogieType.Length - 4);
        case "SeqType":
        case "SetType":
        case "DatatypeTypeType":
          return ReconstructType(GetIsResults(element)?[0]);
        case "refType":
          return ReconstructType(fDtype.OptEval(element));
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
      if (typeElement == null)
        return "?";
      var fullName = GetTrueName(typeElement);
      if (fullName != null && fullName.Length > 7)
        return fullName.Substring(7);
      if (fullName is "TInt" or "TReal" or "TChar" or "TBool")
        return fullName.Substring(1).ToLower(); // TODO: what about sequences and bitVectors?
      if (fBv.AppWithResult(typeElement) != null)
        return "bv" + ((Model.Integer)fBv.AppWithResult(typeElement).Args[0]).AsInt();
      var tagElement = fTag.OptEval(typeElement);
      if (tagElement == null)
        return "?";
      var tagName = GetTrueName(tagElement);
      if (tagName == null || (tagName.Length < 10 && tagName != "TagSeq" && tagName != "TagSet" && tagName != "TagBitVector"))
        return "?";
      var typeArgs = Model.GetFunc("T" + tagName.Substring(3))?.
        AppWithResult(typeElement)?.
        Args.ToList();
      tagName = tagName switch {
        "TagSeq" => "seq",
        "TagSet" => "set",
        _ => tagName.Substring(9)
      };
      if (typeArgs == null)
        return tagName;
      return tagName + "<" + String.Join(",", typeArgs.ConvertAll(t => ReconstructType(t))) + ">";
    }
    
    public string CanonicalName(Model.Element elt) {
      if (elt == null) return "?";
      if (elt is Model.Integer or Model.Boolean or Model.BitVector) {
        return elt.ToString();
      }
      Model.FuncTuple fnTuple;
      if (datatypeValues.TryGetValue(elt, out fnTuple)) {
        // elt is s a datatype value, make its name be the name of the datatype constructor
        var nm = fnTuple.Func.Name;
        if (fnTuple.Func.Arity == 0)
          return nm;
        return nm + "(...)";
      }
      var seqLen = fSeqLength.AppWithArg(0, elt);
      if (seqLen != null) { // elt is a sequence
        return string.Format("[Length {0}]", seqLen.Result.AsInt());
      }

      if (elt == fNull.GetConstant())
        return "null";

      var tp = fDtype.TryEval(elt);
      if (tp != null) {
        foreach (var app in tp.References) {
          if (app.Args.Length == 0 && app.Func.Name.StartsWith("class.")) {
            return app.Func.Name.Substring(6);
          }
        }
      }

      if (fType.AppWithArg(0, elt)?.Result == fChar.GetConstant()) {
        var utfCode = 33; // TODO: use a constant here
        if (fCharToInt.AppWithArg(0, elt) != null)
          utfCode = ((Model.Integer) fCharToInt.AppWithArg(0, elt).Result).AsInt();
        else {
          while (charCodes.Contains(utfCode)) {
            utfCode++;
          }
        }
        return "'" + char.ConvertFromUtf32(utfCode) + "'";
      }
      if (localValue.TryGetValue(elt, out var res))
        return res;
      return "?";
    }

    public IEnumerable<DafnyModelVariable> GetExpansion(DafnyModelState dafnyModelState, DafnyModelVariable var) {
      List<DafnyModelVariable> result = new ();

      if (var.Element.Kind != Model.ElementKind.Uninterpreted)
        return result;

      // Perhaps elt is a known datatype value
      if (datatypeValues.TryGetValue(var.Element, out var fnTuple)) {
        // elt is a datatype value
        var i = 0;
        foreach (var arg in fnTuple.Args) {
          result.Add(DafnyModelVariable.Get(dafnyModelState, arg, "[" + i + "]", var));
          i++;
        }
        return result;
      }

      // Perhaps elt is a sequence
      var seqLen = fSeqLength.AppWithArg(0, var.Element);
      if (seqLen != null) {
        // elt is a sequence TODO: string equality comparison
        foreach (var tpl in fSeqIndex.AppsWithArg(0, var.Element))
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result), "[" + tpl.Args[1] + "]", var));
        return result;
      }

      // Perhaps elt is a set
      foreach (var tpl in fSetSelect.AppsWithArg(0, var.Element)) {
        var setElement = tpl.Args[1];
        var containment = tpl.Result;
        result.Add(DafnyModelVariable.Get(dafnyModelState, containment, "["+Unbox(setElement)+"]", var));
      }
      if (result.Count != 0)
        return result;  // elt is a set

      // It seems elt is an object or array
      if (arrayLengths.TryGetValue(var.Element, out var lengths)) {
        var i = 0;
        foreach (var len in lengths) {
          var name = lengths.Length == 1 ? "Length" : "Length" + i;
          result.Add(DafnyModelVariable.Get(dafnyModelState, len, name, var));
          i++;
        }
      }
      var heap = dafnyModelState.State.TryGet("$Heap");
      if (heap == null)
        return result;
      var instances = fSetSelect.AppsWithArgs(0, heap, 1, var.Element);
      if (instances == null || (!instances.Any()))
        return result;
      foreach (var tpl in fSetSelect.AppsWithArg(0, instances.ToList()[0].Result)) {
        var field = new FieldName(tpl.Args[1], this);
        if (field.NameFormat != "alloc")
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result), "." + field.NameFormat, var));
      }
      return result;
    }

    class FieldName
    {
      private readonly int dims;
      public readonly string NameFormat;

      public FieldName(Model.Element elt, DafnyModel dm) {
        var field = elt;
        var tpl = dm.fDim.AppWithArg(0, elt);
        if (tpl != null) {
          dims = tpl.Result.AsInt();
          var nameArgs = new Model.Element[dims];
          for (var i = dims; 0 <= --i;) {
            if (i == 0) {
              tpl = dm.fIndexField.AppWithResult(elt);
              nameArgs[i] = tpl.Args[0];
            }
            else {
              tpl = dm.fMultiIndexField.AppWithResult(elt);
              nameArgs[i] = tpl.Args[1];
              elt = tpl.Args[0];
            }
          }
        }
        // now for the name
        if (dims == 0) {
          NameFormat = field.ToString();
          foreach (var n in field.Names) {
            NameFormat = n.Func.Name;
            var dot = NameFormat.LastIndexOf('.');
            if (0 <= dot)
              NameFormat = NameFormat.Substring(dot + 1);
            break;
          }
        }
        else {
          NameFormat = "[";
          var sep = "";
          for (var i = 0; i < dims; i++) {
            NameFormat += sep + "%" + i;
            sep = ",";
          }
          NameFormat += "]";
        }
      }
    }

    private Model.Element Unbox(Model.Element elt) {
      var unboxed = fBox.AppWithResult(elt);
      return unboxed != null ? unboxed.Args[0] : elt;
    }
    
    public void RegisterLocalValue(string name, Model.Element elt) {
      if (localValue.TryGetValue(elt, out var curr) && CompareFieldNames(name, curr) >= 0)
        return;
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
        if (c1 != c2)
          break;
      }
      if (numberPos >= 0) {
        var v1 = GetNumber(f1, numberPos);
        var v2 = GetNumber(f2, numberPos);
        if (v1 < v2) return -1;
        if (v1 > v2) return 1;
      }
      return string.CompareOrdinal(f1, f2);
    }
  }
}
