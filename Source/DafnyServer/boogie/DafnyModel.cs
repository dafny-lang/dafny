// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.ModelViewer.Dafny {

public class DafnyModel {
    public List<DafnyModelState> states = new();
    public readonly Model model;
    internal readonly Model.Func f_set_select, f_seq_length, f_seq_index, f_box, 
      f_dim, f_index_field, f_multi_index_field, f_dtype, f_null, f_char_to_int,
      f_type, f_char, f_tag, f_bv;
    private readonly Dictionary<Model.Element, Model.Element[]> ArrayLengths = new();
    private readonly Dictionary<Model.Element, Model.FuncTuple> DatatypeValues = new();
    private readonly Dictionary<Model.Element, string> localValue = new();

    private readonly HashSet<int> charCodes = new(); //TODO: move this to state level

    private bool UseLocalsForCanonicalNames => false;

    public DafnyModel(Model model, ViewOptions viewOpts) {
      this.model = model;
      f_set_select = MergeMapSelectFunctions(2);
      f_seq_length = model.MkFunc("Seq#Length", 1);
      f_seq_index = model.MkFunc("Seq#Index", 2);
      f_box = model.MkFunc("$Box", 1);
      f_dim = model.MkFunc("FDim", 1);
      f_index_field = model.MkFunc("IndexField", 1);
      f_multi_index_field = model.MkFunc("MultiIndexField", 2);
      f_dtype = model.MkFunc("dtype", 1);
      f_null = model.MkFunc("null", 0);
      f_char_to_int = model.MkFunc("char#ToInt", 1);
      f_type = model.MkFunc("type", 1);
      f_char = model.MkFunc("charType", 0);
      f_tag = model.MkFunc("Tag", 1);
      f_bv = model.MkFunc("TBitvector", 1);
      
      InitCharCodes();

      // collect the array dimensions from the various array.Length functions, and
      // collect all known datatype values
      foreach (var fn in model.Functions) {
        if (Regex.IsMatch(fn.Name, "^_System.array[0-9]*.Length[0-9]*$")) {
          int j = fn.Name.IndexOf('.', 13);
          int dims = j == 13 ? 1 : int.Parse(fn.Name.Substring(13, j - 13));
          int idx = j == 13 ? 0 : int.Parse(fn.Name.Substring(j + 7));
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Args[0];
            var len = tpl.Result;
            Model.Element[] ar;
            if (!ArrayLengths.TryGetValue(elt, out ar)) {
              ar = new Model.Element[dims];
              ArrayLengths.Add(elt, ar);
            }
            Contract.Assert(ar[idx] == null);
            ar[idx] = len;
          }
        }
        else if (fn.Name.StartsWith("#") && fn.Name.IndexOf('.') != -1 && fn.Name[1] != '#') {
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Result;
            DatatypeValues.Add(elt, tpl);
          }
        }
      }
    }

    private void InitCharCodes() {
      foreach (var app in f_char_to_int.Apps)
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
      var name = "[" + arity + "]";
      if (model.HasFunc(name)) {
        // Coming up with a new name if the ideal one is reserved
        var id = 0;
        while (model.HasFunc(name + "#" + id)) {
          id++;
        }
        name += "#" + id;
      }
      var result = model.MkFunc(name, arity);
      foreach (var func in model.Functions) {
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

    public IEnumerable<DafnyModelState> States => states;

    public string GetUserVariableName(string name) {
      if (name.StartsWith("$")) // this covers $Heap and $_Frame and $nw...
        return null;
      if (name.Contains("##"))  // a temporary variable of the translation
        return null;
      return name;
    }
    
    /// <summary>
    /// Return the name of the 0-arity function that maps to the element if such
    /// a function exists and is unique. Return null otherwise
    /// </summary>
    private string GetTrueName(Model.Element element) {
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
      Model.Element typeElement = model.GetFunc("type").OptEval(element);
      if (typeElement == null)
        return null;
      string name = GetTrueName(typeElement);
      if (name != null)
        return name;
      if (model.GetFunc("SeqTypeInv0").OptEval(typeElement) != null)
        return "SeqType";
      if (model.GetFunc("MapType0TypeInv0").OptEval(typeElement) != null)  // TODO: Not sure about this
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
        case Model.ElementKind.Array: 
        default:
          return "?";
      }
    }

    /// <summary>
    /// Return all elements x that satisfy ($Is element x)
    /// </summary>
    private List<Model.Element> GetIsResults(Model.Element element) {
      List<Model.Element> result = new();
      foreach (var tuple in model.GetFunc("$Is").AppsWithArg(0, element))
        if (((Model.Boolean) tuple.Result).Value) {
          result.Add(tuple.Args[1]);
        }
      return result;
    }

    /// <summary> Get the Dafny type of an Uninterpreted element </summary>
    private string GetDafnyType(Model.Uninterpreted element) {
      // TODO: make uses of OptEval and AppWithArg consistent
      string boogieType = GetBoogieType(element);
      switch (boogieType) {
        case "intType": case "realType": case "charType": case "boolType":
          return boogieType.Substring(0, boogieType.Length - 4);
        case "SeqType":
        case "SetType":
        case "DatatypeTypeType":
          return ReconstructType(GetIsResults(element)?[0]);
        case "refType":
          return ReconstructType(f_dtype.OptEval(element));
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
      string fullName = GetTrueName(typeElement);
      if (fullName != null && fullName.Length > 7)
        return fullName.Substring(7);
      if (fullName is "TInt" or "TReal" or "TChar" or "TBool")
        return fullName.Substring(1).ToLower(); // TODO: what about sequences and bitVectors?
      if (f_bv.AppWithResult(typeElement) != null)
        return "bv" + ((Model.Integer)f_bv.AppWithResult(typeElement).Args[0]).AsInt();
      Model.Element tagElement = f_tag.OptEval(typeElement);
      if (tagElement == null)
        return "?";
      string tagName = GetTrueName(tagElement);
      if (tagName == null || (tagName.Length < 10 && tagName != "TagSeq" && tagName != "TagSet" && tagName != "TagBitVector"))
        return "?";
      Model.Element[] typeArgs = model.GetFunc("T" + tagName.Substring(3))?.
        AppWithResult(typeElement)?.
        Args;
      if (tagName == "TagSeq")
        tagName = "seq";
      else if (tagName == "TagSet")
        tagName = "set";
      else
        tagName = tagName.Substring(9);
      if (typeArgs == null)
        return tagName;
      return tagName + "<" + String.Join(",", typeArgs.Map(t => ReconstructType(t))) + ">";
    }
    
    public string CanonicalName(Model.Element elt) {
      string res;
      if (elt == null) return "?";
      if (elt is Model.Integer or Model.Boolean or Model.BitVector) {
        return elt.ToString();
      }
      Model.FuncTuple fnTuple;
      if (DatatypeValues.TryGetValue(elt, out fnTuple)) {
        // elt is s a datatype value, make its name be the name of the datatype constructor
        string nm = fnTuple.Func.Name;
        if (fnTuple.Func.Arity == 0)
          return nm;
        return nm + "(...)";
      }
      var seqLen = f_seq_length.AppWithArg(0, elt);
      if (seqLen != null) { // elt is a sequence
        return string.Format("[Length {0}]", seqLen.Result.AsInt());
      }

      if (elt == f_null.GetConstant())
        return "null";

      var tp = f_dtype.TryEval(elt);
      if (tp != null) {
        foreach (var app in tp.References) {
          if (app.Args.Length == 0 && app.Func.Name.StartsWith("class.")) {
            return app.Func.Name.Substring(6);
          }
        }
      }

      if (f_type.AppWithArg(0, elt)?.Result == f_char.GetConstant()) {
        int utfCode = 33; // TODO: use a constant here
        if (f_char_to_int.AppWithArg(0, elt) != null)
          utfCode = ((Model.Integer) f_char_to_int.AppWithArg(0, elt).Result).AsInt();
        else {
          while (charCodes.Contains(utfCode)) {
            utfCode++;
          }
        }
        return "'" + Char.ConvertFromUtf32(utfCode) + "'";
      }

      if (UseLocalsForCanonicalNames) {
        if (localValue.TryGetValue(elt, out res))
          return res;
      }
      return "?";
    }

    public IEnumerable<DafnyModelVariable> GetExpansion(DafnyModelState dafnyModelState, DafnyModelVariable var) {
      List<DafnyModelVariable> result = new ();

      if (var.element.Kind != Model.ElementKind.Uninterpreted)
        return result;

      // Perhaps elt is a known datatype value
      Model.FuncTuple fnTuple;
      if (DatatypeValues.TryGetValue(var.element, out fnTuple)) {
        // elt is a datatype value
        int i = 0;
        foreach (var arg in fnTuple.Args) {
          result.Add(DafnyModelVariable.Get(dafnyModelState, arg, "[" + i + "]", var));
          i++;
        }
        return result;
      }

      // Perhaps elt is a sequence
      var seqLen = f_seq_length.AppWithArg(0, var.element);
      if (seqLen != null) {
        // elt is a sequence TODO: string equality comparison
        foreach (var tpl in f_seq_index.AppsWithArg(0, var.element))
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result), "[" + tpl.Args[1] + "]", var));
        return result;
      }

      // Perhaps elt is a set
      foreach (var tpl in f_set_select.AppsWithArg(0, var.element)) {
        var setElement = tpl.Args[1];
        var containment = tpl.Result;
        result.Add(DafnyModelVariable.Get(dafnyModelState, containment, "["+Unbox(setElement)+"]", var));
      }
      if (result.Count != 0)
        return result;  // elt is a set

      // It seems elt is an object or array
      Model.Element[] lengths;
      if (ArrayLengths.TryGetValue(var.element, out lengths)) {
        int i = 0;
        foreach (var len in lengths) {
          var name = lengths.Length == 1 ? "Length" : "Length" + i;
          result.Add(DafnyModelVariable.Get(dafnyModelState, len, name, var));
          i++;
        }
      }
      var heap = dafnyModelState.State.TryGet("$Heap");
      if (heap == null)
        return result;
      var instances = f_set_select.AppsWithArgs(0, heap, 1, var.element);
      if (instances == null || (!instances.Any()))
        return result;
      foreach (var tpl in f_set_select.AppsWithArg(0, instances.ToList()[0].Result)) {
        var field = new FieldName(tpl.Args[1], this);
        if (field.NameFormat != "alloc")
          result.Add(DafnyModelVariable.Get(dafnyModelState, Unbox(tpl.Result), "." + field.NameFormat, var));
      }
      return result;
    }

    class FieldName
    {
      public readonly Model.Element Field;
      public readonly int Dims;
      public readonly string NameFormat;
      public readonly Model.Element[] NameArgs;

      public FieldName(Model.Element elt, DafnyModel dm) {
        Field = elt;
        NameArgs = new Model.Element[Dims];
        var tpl = dm.f_dim.AppWithArg(0, elt);
        if (tpl != null) {
          Dims = tpl.Result.AsInt();
          NameArgs = new Model.Element[Dims];
          for (int i = Dims; 0 <= --i;) {
            if (i == 0) {
              tpl = dm.f_index_field.AppWithResult(elt);
              NameArgs[i] = tpl.Args[0];
            }
            else {
              tpl = dm.f_multi_index_field.AppWithResult(elt);
              NameArgs[i] = tpl.Args[1];
              elt = tpl.Args[0];
            }
          }
        }
        // now for the name
        if (Dims == 0) {
          NameFormat = Field.ToString();
          foreach (var n in Field.Names) {
            NameFormat = n.Func.Name;
            int dot = NameFormat.LastIndexOf('.');
            if (0 <= dot)
              NameFormat = NameFormat.Substring(dot + 1);
            break;
          }
        }
        else {
          NameFormat = "[";
          string sep = "";
          for (int i = 0; i < Dims; i++) {
            NameFormat += sep + "%" + i;
            sep = ",";
          }
          NameFormat += "]";
        }
      }
    }

    Model.Element Unbox(Model.Element elt) {
      var unboxed = f_box.AppWithResult(elt);
      if (unboxed != null)
        return unboxed.Args[0];
      return elt;
    }
    
    public void RegisterLocalValue(string name, Model.Element elt) {
      string curr;
      if (localValue.TryGetValue(elt, out curr) && CompareFieldNames(name, curr) >= 0)
        return;
      localValue[elt] = name;
    }

    static ulong GetNumber(string s, int beg) {
      ulong res = 0;
      while (beg < s.Length)
      {
        var c = s[beg];
        if ('0' <= c && c <= '9')
        {
          res *= 10;
          res += (uint)c - '0';
        }
        beg++;
      }
      return res;
    }

    public int CompareFieldNames(string f1, string f2) {
      var len = Math.Min(f1.Length, f2.Length);
      var numberPos = -1;
      for (int i = 0; i < len; ++i) {
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

    public class SourceLocation {
      public string Filename;
      public string AddInfo;
      public int Line;
      public int Column;
    }

    // example parsed token: @"c:\users\foo\bar.c(12,10) : random string"
    // the ": random string" part is optional
    public SourceLocation TryParseSourceLocation(string name) {
      var par = name.LastIndexOf('(');
      if (par <= 0) return null;

      var res = new SourceLocation() { Filename = name.Substring(0, par) };

      var words = name.Substring(par + 1).Split(',', ')', ':').Where(x => x != "").ToArray();
      if (words.Length < 2) return null;

      if (!int.TryParse(words[0], out res.Line) || !int.TryParse(words[1], out res.Column)) return null;

      var colon = name.IndexOf(':', par);
      if (colon > 0)
        res.AddInfo = name.Substring(colon + 1).Trim();
      else
        res.AddInfo = "";

      return res;
    }

    static char[] dirSeps = { '\\', '/' };
    public string ShortenToken(string tok, int fnLimit, bool addAddInfo) {
      var loc = TryParseSourceLocation(tok);

      if (loc != null)
      {
        var fn = loc.Filename;
        var idx = fn.LastIndexOfAny(dirSeps);
        if (idx > 0)
          fn = fn.Substring(idx + 1);
        if (fn.Length > fnLimit)
        {
          fn = fn.Substring(0, fnLimit) + "..";
        }
        var addInfo = addAddInfo ? loc.AddInfo : "";
        if (addInfo != "")
          addInfo = ":" + addInfo;
        return string.Format("{0}({1},{2}){3}", fn, loc.Line, loc.Column, addInfo);
      }
      return tok;
    }
  }
}
