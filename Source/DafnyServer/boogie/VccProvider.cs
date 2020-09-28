using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer.Vcc
{
  public class Provider : ILanguageProvider
  {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m)
    {
      return m.TryGetFunc("$is_ghost_field") != null && m.TryGetFunc("$fk_vol_version") != null;
    }

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      var vm = new VccModel(m, opts);
      return vm;
    }
  }

  enum DataKind
  {
    Flat,
    PhysPtr,
    SpecPtr,
    Object,
    Ptrset,
    Map
  }

  class VccModel : LanguageModel
  {
    public readonly Model.Func f_ptr_to, f_phys_ptr_cast, f_spec_ptr_cast, f_mathint, f_local_value_is, f_spec_ptr_to, f_heap, f_select_field,
                               f_select_value, f_field, f_field_type, f_int_to_ptr, f_ptr_to_int, f_ptr, f_map_t, f_select_ptr,
                               f_owners, f_closed, f_roots, f_timestamps, f_select_bool, f_select_int, f_is_null, f_good_state,
                               f_int_to_version, f_int_to_ptrset, f_set_in0, f_is_ghost_field, f_is_phys_field, f_idx,
                               f_is_sequential_field, f_is_volatile_field, f_type_project_0, f_array, f_active_option, f_int_to_field,
                               f_blob_type, f_array_emb, f_addr, f_address_root, f_base, f_field_arr_size, f_field_arr_root, f_field_arr_index,
                               f_dot, f_prim_emb;
    public readonly Model.Element tp_object, tp_mathint, tp_bool, tp_state, tp_ptrset, tp_heaptp;
    public readonly Model.Element elt_me, elt_null;
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    Dictionary<Model.Element, string> literalName = new Dictionary<Model.Element, string>();
    Dictionary<Model.Element, Model.Element> guessedType = new Dictionary<Model.Element, Model.Element>();
    public List<StateNode> states = new List<StateNode>();
    public Dictionary<string, string> localVariableNames = new Dictionary<string, string>();

    Dictionary<Model.Element, string> datatypeLongName = new Dictionary<Model.Element, string>();

    Dictionary<int, string> fileNameMapping = new Dictionary<int, string>();

    public const string selfMarker = "\\self";
    public const int maxDatatypeNameLength = 5;

    public VccModel(Model m, ViewOptions opts)
      : base(m, opts)
    {
      f_ptr_to = m.MkFunc("$ptr_to", 1);
      f_spec_ptr_to = m.MkFunc("$spec_ptr_to", 1);
      f_phys_ptr_cast = m.MkFunc("$phys_ptr_cast", 2);
      f_spec_ptr_cast = m.MkFunc("$spec_ptr_cast", 2);
      f_mathint = m.MkFunc("^^mathint", 0);
      f_local_value_is = m.MkFunc("$local_value_is", 5);
      f_heap = m.MkFunc("$heap", 1);
      f_select_field = m.MkFunc("Select_[$field][$ptr]$int", 2);
      f_select_value = m.MkFunc("Select_[$ptr]$int", 2);
      f_select_ptr = m.MkFunc("Select_[$ptr]$ptr", 2);
      f_select_int = m.MkFunc("Select_[$ptr]$int", 2);
      f_select_bool = m.MkFunc("Select_[$ptr]$bool", 2);
      f_owners = m.MkFunc("$f_owner", 1);
      f_closed = m.MkFunc("$f_closed", 1);
      f_roots = m.MkFunc("$roots", 1);
      f_timestamps = m.MkFunc("$f_timestamp", 1);
      f_active_option = m.MkFunc("$f_active_option", 1);
      f_field = m.MkFunc("$field", 1);
      f_field_type = m.MkFunc("$field_type", 1);
      f_int_to_ptr = m.MkFunc("$int_to_ptr", 1);
      f_ptr_to_int = m.MkFunc("$ptr_to_int", 1);
      f_ptr = m.MkFunc("$ptr", 2);
      f_dot = m.MkFunc("$dot", 2);
      f_map_t = m.MkFunc("$map_t", 2);
      f_is_null = m.MkFunc("$is_null", 1);
      f_good_state = m.MkFunc("$good_state", 1);
      f_int_to_version = m.MkFunc("$int_to_version", 1);
      f_int_to_ptrset = m.MkFunc("$int_to_ptrset", 1);
      f_int_to_field = m.MkFunc("$int_to_field", 1);
      f_set_in0 = m.MkFunc("$set_in0", 2);
      f_is_ghost_field = m.MkFunc("$is_ghost_field", 1);
      f_is_phys_field = m.MkFunc("$is_phys_field", 1);
      f_idx = m.MkFunc("$idx", 2);
      f_is_sequential_field = m.MkFunc("$is_sequential_field", 1);
      f_is_volatile_field = m.MkFunc("$is_volatile_field", 1);
      f_type_project_0 = m.MkFunc("$type_project_0", 1);
      f_array = m.MkFunc("$array", 2);
      f_blob_type = m.MkFunc("$blob_type", 1);
      f_array_emb = m.MkFunc("$array_emb", 2);
      f_addr = m.MkFunc("$addr", 1);
      f_base = m.MkFunc("$base", 1);
      f_prim_emb = m.MkFunc("$prim_emb", 1);
      f_address_root = m.MkFunc("$address_root", 2);
      f_field_arr_index = m.MkFunc("$field_arr_index", 1);
      f_field_arr_size = m.MkFunc("$field_arr_size", 1);
      f_field_arr_root = m.MkFunc("$field_arr_root", 1);

      tp_bool = m.GetFunc("^^bool").GetConstant();
      tp_mathint = m.GetFunc("^^mathint").GetConstant();
      tp_object = m.GetFunc("^^object").GetConstant();
      tp_state = m.GetFunc("^$#state_t").GetConstant();
      tp_ptrset = m.GetFunc("^$#ptrset").GetConstant();

      tp_heaptp = m.MkFunc("$heap_type", 0).GetConstant();

      elt_me = m.GetFunc("$me").GetConstant();
      elt_null = m.GetFunc("$null").GetConstant();

      literalName[elt_me] = "\\me";
      literalName[elt_null] = "NULL";
      foreach (var tpl in f_phys_ptr_cast.Apps)
      {
        if (tpl.Args[0] == elt_null)
          literalName[tpl.Result] = "(" + TypeName(tpl.Args[1]) + "*)NULL";
      }
      foreach (var tpl in f_spec_ptr_cast.Apps)
      {
        if (tpl.Args[0] == elt_null)
          literalName[tpl.Result] = "(" + TypeName(tpl.Args[1]) + "^)NULL";
      }
      foreach (var fn in model.Functions)
      {
        if (fn.Arity == 0 && fn.Name.StartsWith("l#"))
          literalName[fn.GetConstant()] = ":" + fn.Name.Substring(2);
      }

      DecodeFileNames();
      ComputeLocalVariableNames();

      foreach (var s in m.States)
      {
        var sn = new StateNode(this, s);
        sn.SetupVars();
        states.Add(sn);
      }

      var allStates = states.ToArray();
      if (allStates.Length == 1 && allStates[0].vars.Count == 0)
      {
        throw new Exception("This VCC model doesn't contain any variables. Was it saved with the -bvd option?");
      }
      states.Clear();
      var i = 0;
      while (i < allStates.Length)
      {
        var lastGoodName = allStates[i].State.Name;

        var userVars = new HashSet<string>(allStates[i].State.Variables.Where(localVariableNames.ContainsKey));
        i++;
        while (i < allStates.Length)
        {
          foreach (var v in allStates[i].State.Variables)
          {
            if (v == "$s" || userVars.Contains(v)) goto stop;
            if (localVariableNames.ContainsKey(v))
              userVars.Add(v);
          }

          var curName = TryParseSourceLocation(allStates[i].State.Name);
          if (!IsBadName(curName))
            lastGoodName = allStates[i].State.Name;
          i++;
        }

        stop:

        var lastState = allStates[i - 1];
        lastState.capturedStateName = lastGoodName;
        lastState.index = states.Count;
        states.Add(lastState);
        lastState.SetupVars();
      }

      foreach (var s in states)
      {
        var elt = s.State.TryGet("$s");
        if (elt != null)
          literalName[elt] = "\\state'" + s.index;
      }

      GenerateSourceLocations(states);
    }


    bool IsBadName(SourceLocation l)
    {
      return l == null || l.Filename.StartsWith("<");
    }

    private void ComputeLocalVariableNames()
    {
      var vars = model.States.SelectMany(s => s.Variables).Where(v => v != null).Distinct();
      Func<string, string> simpleName = s => { string dummy; return GetUserVariableNameCore(s, out dummy); };
      var userVars = vars.Where(s => simpleName(s) != null);
      var conflictsName = Conflicts(userVars, simpleName).ToArray();
      Func<string, string> qName = s => { string kind, n = GetUserVariableNameCore(s, out kind); return n + " (" + kind + ")"; };
      var conflictsKind = Conflicts(conflictsName, qName).ToArray();

      var conflictsNameH = new HashSet<string>(conflictsName);
      var conflictsKindH = new HashSet<string>(conflictsKind);

      foreach (var v in userVars)
      {
        if (conflictsKindH.Contains(v)) continue;
        if (conflictsNameH.Contains(v))
          localVariableNames[v] = qName(v);
        else
          localVariableNames[v] = simpleName(v);
      }

      var idx = 0;
      foreach (var v in conflictsKind)
      {
        localVariableNames[v] = string.Format("{0} #{1}", qName(v), idx++);
      }
    }

    static IEnumerable<A> Conflicts<A, B>(IEnumerable<A> input, Func<A, B> f)
    {
      var revMap = new Dictionary<B, A>();
      var reported = new HashSet<A>();

      foreach (var k in input)
      {
        if (reported.Contains(k)) continue;
        var v = f(k);
        A tmp;
        if (revMap.TryGetValue(v, out tmp) && !tmp.Equals(k))
        {
          if (!reported.Contains(tmp))
          {
            yield return tmp;
            reported.Add(tmp);
          }
          yield return k;
          reported.Add(k);
        }
        else
        {
          revMap[v] = k;
        }
      }
    }

    #region Function name scoring
    static string[][] prefixes = new string[][] {
      new string[] { "F#", "$eq.$map", "Q#", },
      new string[] { "F#lambda", },
      new string[] { "$int_to_", "lambda@", "distinct-aux-f", "Select_","Store_", "$select.", "$store.", },
    };

    static string[][] totals = new string[][] {
      new string[] {
      "$current_timestamp",
      "$full_stop", "$function_entry", "$ptr_to_i4",
      "$ptr_to_i8", "$ptr_to_u4", "$ptr_to_u8",
      "$span", "$sizeof", "$in_domain",
      "$inv2",
      "$is_claimable",
      "$set_cardinality", "$set_difference", "$set_union",
      "$thread_local", "$unchecked", "$writes_at",
      "$array_range", "$arrays_disjoint",
      "$byte_ptr_subtraction",
      },

      new string[] {
      "$addr", "$dot", "$emb0", "$fetch_from_domain", "$in_range_phys_ptr",
      "$in_range_spec_ptr", "$is_sequential_field", "$is_volatile_field",
      "$is_ghost_field", "$is_phys_field", "$is_math_type", "$invok_state",
      "$is_primitive",
      "$spec_ptr_cast",
      "$phys_ptr_cast",
      "$is_null",
      "$in_domain_lab",
      "$inv_lab",
      "$set_in0",
      },

      new string[] {
      "$_pow2", "$as_composite_field", "$as_field_with_type", "$as_in_range_t",
      "$as_primitive_field", "$base", "$call_transition", "tickleBool", "Ctor",
      "$mv_state", "$field", "$field_arr_root", "$field_kind", "$field_offset",
      "$field_parent_type", "$field_type", "$file_name_is", "$good_state",
      "$good_state_ext", "$function_arg_type", "$has_field_at0", "$map_domain",
      "$map_range", "$map_t", "$ptr_to", "$ptr_to_i1", "$ptr_to_i2",
      "$ptr_to_u1", "$ptr_to_u2", "$is_unwrapped", "$is_unwrapped_dynamic",
      "$heap", "$closed", "$owner", "$owns", "$modifies", "$post_unwrap",
      "$pow2", "$pre_unwrap", "$ptr", "$is", "$in_range_t", "$roots",
      "$timestamp", "$type_branch", "$type_code_is", "$type_project_0",
      "$typemap", "$set_in_pos", "$updated_owns", "$ver_domain", "$vs_state",
      "$set_singleton",
      "$f_owner", "$f_closed", "$f_timestamps",
      "$local_value_is",
      "$field_arr_ctor",
      "$idx",
      },
    };

    string[] state_props = new string[] { };

    Dictionary<string, int> functionScores = new Dictionary<string, int>();

    int FunctionScore(string name)
    {
      if (functionScores.Count == 0)
      {
        for (int i = 0; i < totals.Length; ++i)
          foreach (var s in totals[i])
            functionScores[s] = i;
      }

      int res;
      if (functionScores.TryGetValue(name, out res))
        return res;

      res = -1;
      if (name[0] == '$' && name.EndsWith("_to_int"))
        res = 1;
      else if (name.EndsWith("#frame"))
        res = 2;
      else if (name.Contains("#limited#"))
        res = 2;
      else
      {
        for (int i = 0; i < prefixes.Length; ++i)
          foreach (var p in prefixes[i])
            if (name.StartsWith(p))
            {
              res = i;
              //goto stop;
            }
        //stop: ;
      }

      if (res == -1)
        res = 1; // default

      functionScores[name] = res;
      return res;
    }
    #endregion

    private void DecodeFileNames()
    {
      var fis = model.GetFunc("$file_name_is");
      foreach (var f in model.Functions)
      {
        if (f.Arity == 0 && f.Name.StartsWith("#file^"))
        {
          var sb = new StringBuilder();
          var idx = 6;
          var name = f.Name;
          while (idx < name.Length)
          {
            if (name[idx] == '?')
            {
              var c = (char)Int32.Parse(name.Substring(idx + 1, 2), System.Globalization.NumberStyles.HexNumber);
              sb.Append(c);
              idx += 3;
            }
            else
            {
              sb.Append(name[idx++]);
            }
          }
          name = sb.ToString();

          foreach (var app in fis.AppsWithArg(1, f.GetConstant()))
            fileNameMapping[app.Args[0].AsInt()] = name;
        }
      }
    }

    private Model.Element DecodeDT(string dt)
    {
      if (dt.StartsWith("dt"))
      {
        var tpName = dt.Replace("dt", "#distTp");
        var f = model.TryGetFunc(tpName);
        if (f != null)
        {
          return f.GetConstant();
          //var res = f_type_project_0.TryEval(ptr);
          //if (res != null)
          //  tp = res;
        }
      }
      return null;
    }

    private string DecodeToken(string name, ref Model.Element tp)
    {
      var idx = name.LastIndexOf("$");
      if (idx < 0) return null;
      var words = name.Substring(idx + 1).Split('.', '^', '!', '#', '@');
      if (words.Length > 3)
        tp = DecodeDT(words[3]);
      return string.Format("{0}({1},{2})", fileNameMapping[int.Parse(words[0])], words[1], words[2]);
    }

    public string GetUserVariableName(string name)
    {
      string res;
      localVariableNames.TryGetValue(name, out res);
      return res;
    }


    string GetUserVariableNameCore(string name, out string kind)
    {
      if (name.StartsWith("L#"))
      {
        kind = "local";
        return name.Substring(2);
      }

      if (name.StartsWith("P#"))
      {
        kind = "in-param";
        return name.Substring(2);
      }

      if (name.StartsWith("OP#"))
      {
        kind = "out-param";
        return name.Substring(3);
      }

      if (name.StartsWith("SL#"))
      {
        kind = "spec local";
        return name.Substring(3);
      }

      if (name.StartsWith("SP#"))
      {
        kind = "spec in-param";
        return name.Substring(3);
      }

      if (name.StartsWith("local."))
      {
        kind = "param copied to local";
        return name.Substring(6);
      }

      if (name.StartsWith("addr."))
      {
        kind = "stack-allocated struct";
        return name.Substring(5);
      }

      if (name == "$result")
      {
        kind = "function return value";
        return "\\result";
      }

      if (name.StartsWith("res__") && viewOpts.ViewLevel >= 1)
      {
        kind = "call result";
        return name;
      }

      if (name == "$s" && viewOpts.ViewLevel >= 1)
      {
        kind = "current state";
        return "\\now";
      }

      kind = null;
      return null;
    }


    private string LiteralName(Model.Element elt)
    {
      string r;

      if (literalName.TryGetValue(elt, out r))
        return r;

      r = TryTypeName(elt);
      if (r != null)
      {
        literalName[elt] = r;
        return r;
      }

      var i = elt as Model.Integer;
      if (i != null)
        return AsPow2(i);

      var bv = elt as Model.BitVector;
      if (bv != null)
        return bv.Numeral + "bv" + bv.Size.ToString();

      return null;
    }

    public Model.Element LocalType(string localName)
    {
      string dummy;
      var v = GetUserVariableNameCore(localName, out dummy);
      if (v == null) v = localName;
      var c = model.TryGetFunc("#loc." + v);
      if (c != null)
      {
        var localIs = f_local_value_is.AppWithArg(2, c.GetConstant());
        if (localIs != null)
          return localIs.Args[4];
      }
      foreach (var s in model.States.Reverse())
      {
        var val = s.TryGet(localName);
        var tp = GuessType(val);
        if (tp != tp_mathint)
          return tp;
      }
      return tp_mathint;
    }

    public Model.Element Image(Model.Element elt, Model.Func f)
    {
      var r = f.AppWithResult(elt);
      if (r != null)
        return r.Args[0];
      return null;
    }

    string TypeNameCore(Model.Element elt)
    {
      var deref = Image(elt, f_ptr_to);
      if (deref != null)
        return TypeName(deref) + "*";
      deref = Image(elt, f_spec_ptr_to);
      if (deref != null)
        return TypeName(deref) + "^";
      deref = Image(elt, f_blob_type);
      if (deref != null)
        return "_(blob " + CanonicalName(deref) + ")";
      var mapt = f_map_t.AppWithResult(elt);
      if (mapt != null)
        return string.Format("{1}[{0}]", TypeName(mapt.Args[0]), TypeName(mapt.Args[1]));

      var arr = f_array.AppWithResult(elt);
      if (arr != null)
      {
        return string.Format("{0}[{1}]", TypeName(arr.Args[0]), arr.Args[1].ToString());
      }

      foreach (var app in elt.Names)
        if (app.Func.Arity == 0 && app.Func.Name.StartsWith("^"))
        {
          var n = app.Func.Name.Substring(1);
          switch (n)
          {
            case "^i1": return "int8_t";
            case "^u1": return "uint8_t";
            case "^i2": return "int16_t";
            case "^u2": return "uint16_t";
            case "^i4": return "int32_t";
            case "^u4": return "uint32_t";
            case "^i8": return "int64_t";
            case "^u8": return "uint64_t";
            case "^bool": return "bool";
            default:
              var pref = "_vcc_math_type_";
              if (n.StartsWith(pref)) n = n.Substring(pref.Length);
              return n;
          }
        }

      return null;
    }

    public string TypeName(Model.Element elt)
    {
      var r = TryTypeName(elt);
      if (r == null)
        return elt.ToString();
      else return r;
    }

    public string TryTypeName(Model.Element elt)
    {
      string res;
      if (!typeName.TryGetValue(elt, out res))
      {
        typeName[elt] = elt.ToString(); // avoid infinite recursion
        res = TypeNameCore(elt);
        typeName[elt] = res;
      }
      return res;
    }

    public static readonly string[] synthethic_fields = new string[] { "$f_owns", "$f_ref_cnt", "$f_vol_version", "$f_root", "$f_group_root", "$f_active_option" };

    public string ConstantFieldName(Model.Element elt)
    {
      string res;
      IsConstantField(elt, out res);
      return res;
    }

    public bool IsConstantField(Model.Element elt)
    {
      string dummy;
      return IsConstantField(elt, out dummy);
    }

    public bool IsConstantField(Model.Element elt, out string theName)
    {
      var bestScore = int.MinValue;
      string bestName = null;

      foreach (var t in elt.Names)
      {
        var score = int.MinValue;
        string name = null;
        if (t.Args.Length == 0)
        {
          name = t.Func.Name;
          score = 0;
          var dotIdx = name.IndexOf('.');
          if (dotIdx > 0)
          {
            score += 10;
            name = name.Substring(dotIdx + 1);
          }
          if (name.Contains('#')) score -= 1;
        }
        else if (t.Func.Name.StartsWith("$f_") && synthethic_fields.Contains(t.Func.Name))
        {
          name = string.Format("{0}<{1}>", t.Func.Name.Substring(3).Replace("root", "alloc_root"), TypeName(t.Args[0]));
          score = 6;
        }
        else if (t.Func == f_array_emb)
        {
          name = string.Format("[0] (of {0}[{1}])", TypeName(t.Args[0]), t.Args[1].ToString());
          score = 5;
        }
        if (score > bestScore)
        {
          bestScore = score;
          bestName = name;
        }
      }

      theName = bestName;
      return bestScore >= 5;
    }

    bool IsSomeState(Model.Element elt)
    {
      var tp = GuessType(elt);
      return tp == tp_state || tp == tp_heaptp;
    }

    bool IsThisState(Model.Element st, Model.Element elt)
    {
      return elt == st || elt == f_heap.TryEval(st);
    }

    Model.Element GuessType(Model.Element element)
    {
      Model.Element res;
      if (!guessedType.TryGetValue(element, out res))
      {
        res = GuessTypeCore(element);
        guessedType[element] = res;
      }
      return res;
    }

    Model.Element GuessTypeCore(Model.Element element)
    {
      if (element is Model.Boolean)
        return tp_bool;

      var fld = f_field.TryEval(element);
      if (fld != null)
      {
        var tp = f_field_type.TryEval(fld);
        if (tp != null)
        {
          var ptp = f_ptr_to.TryEval(tp);
          if (ptp != null)
            return ptp;
          ptp = f_spec_ptr_to.TryEval(tp);
          if (ptp != null)
            return ptp;
        }
        return tp_object;
      }

      foreach (var tpl in element.References)
      {
        if (element == tpl.Result)
        {
          if (tpl.Func == f_ptr)
            return tp_object;
          if (tpl.Func == f_heap)
            return tp_heaptp;
        }

        if (tpl.Args.Length >= 1 && tpl.Args[0] == element)
        {
          if (tpl.Func == f_heap || tpl.Func == f_closed || tpl.Func == f_good_state)
            return tp_state;
        }

        if (tpl.Func == f_select_bool)
          if (tpl.Args[0] == element)
            return tp_ptrset;
          else if (tpl.Args[1] == element)
            return tp_object;

        var fname = tpl.Func.Name;

        if (tpl.Args.Length == 2 && tpl.Args[0] == element && fname.StartsWith("$select.$map_t"))
        {
          var mt = model.TryGetFunc("MT#" + fname);
          if (mt != null && mt.Arity == 0)
            return mt.GetConstant();
          var t1 = GuessType(tpl.Args[1]);
          var t2 = GuessType(tpl.Result);
          var t = f_map_t.TryEval(t1, t2);
          if (t != null)
            return t;
        }

        var tpName = DataTypeName(element, tpl);
        if (tpName != null)
        {
          var tp = model.TryGetFunc("^$#" + tpName);
          if (tp != null)
            return tp.GetConstant();
        }
      }

      return tp_mathint;
    }

    string DataTypeName(Model.Element elt, Model.FuncTuple tpl)
    {
      var fname = tpl.Func.Name;
      if (tpl.Args.Length == 1 && tpl.Args[0] == elt && fname.StartsWith("RF#"))
      {
        var fldName = tpl.Func.Name.Substring(3);
        var idx = fldName.LastIndexOf('.');
        if (idx > 0)
        {
          return fldName.Substring(0, idx).Replace("_vcc_math_type_", "");
        }
      }

      if (tpl.Args.Length == 1 && tpl.Args[0] == elt && (fname.StartsWith("DSZ#") || fname.StartsWith("RSZ#") || fname.StartsWith("DGH#")))
      {
        return fname.Substring(4).Replace("_vcc_math_type_", "");
      }
      return null;
    }

    public DataKind GetKind(Model.Element tp, out Model.FuncTuple tpl)
    {
      tpl = null;

      if (tp == tp_object)
        return DataKind.Object;
      else if (tp == tp_ptrset)
        return DataKind.Ptrset;

      tpl = f_ptr_to.AppWithResult(tp);
      if (tpl != null) return DataKind.PhysPtr;
      tpl = f_spec_ptr_to.AppWithResult(tp);
      if (tpl != null) return DataKind.SpecPtr;
      tpl = f_map_t.AppWithResult(tp);
      if (tpl != null) return DataKind.Map;

      return DataKind.Flat;
    }

    public DataKind GetKind(Model.Element tp)
    {
      Model.FuncTuple dummy;
      return GetKind(tp, out dummy);
    }


    public Model.Element WrapForUse(Model.Element elt, Model.Element tp)
    {
      Model.FuncTuple tpl;
      var kind = GetKind(tp, out tpl);

      if (kind == DataKind.Flat)
      {
        if (elt.Kind == Model.ElementKind.Integer)
        {
          var tpname = TypeName(tp);
          if (tpname.StartsWith("$")) tpname = tpname.Substring(1);
          if (tpname.StartsWith("#"))
          {
            foreach (var tupl in elt.References)
            {
              if (tupl.Args.Length == 1 && tupl.Args[0] == elt && tupl.Func.Name.StartsWith("$int_to_") && tupl.Func.Name.EndsWith(tpname))
              {
                return tupl.Result;
              }
            }
          }
        }
        return elt;
      }

      if (kind == DataKind.Map)
      {
        if (elt.Kind == Model.ElementKind.Integer)
        {
          Model.Element theMap = null;
          foreach (var conv in model.Functions)
            // really, we should reconstruct the name of this function, but this is painful
            if (conv.Arity == 1 && conv.Name.StartsWith("$int_to_map_t"))
            {
              var app = conv.AppWithArg(0, elt);
              if (app != null)
              {
                theMap = app.Result;
                break;
              }
            }
          if (theMap == null) return elt;
          return theMap;
        }
        return elt;
      }
      else if (kind == DataKind.Ptrset)
      {
        var tmp = f_int_to_ptrset.TryEval(elt);
        if (tmp != null)
          return tmp;
        return elt;
      }

      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr || kind == DataKind.Object)
      {
        if (elt.Kind == Model.ElementKind.Integer)
        {
          var tmp = f_int_to_ptr.TryEval(elt);
          if (tmp != null)
            elt = tmp;
        }
      }

      if (kind == DataKind.Object)
        return elt;

      if (kind == DataKind.PhysPtr)
        return Util.OrElse(f_phys_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      if (kind == DataKind.SpecPtr)
        return Util.OrElse(f_spec_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      Util.Assert(false);
      return elt;
    }

    void AddSpecialField(StateNode state, Model.Element elt, List<ElementNode> res, string name, Model.Func select_map)
    {
      if (elt == null) return;

      var map = state.State.TryGet("$s");
      if (map != null)
        map = select_map.TryEval(map);
      if (map != null)
      {
        var model = elt.Model;
        Model.Element val = f_select_bool.TryEval(map, elt);
        Model.Element tp = tp_bool;
        if (val == null)
        {
          val = f_select_ptr.TryEval(map, elt);
          tp = tp_object;
        }
        if (val == null)
        {
          val = f_select_int.TryEval(map, elt);
          tp = tp_mathint;
        }
        if (val != null)
        {
          res.Add(new FieldNode(state, new EdgeName(name), val, tp) { Category = NodeCategory.MethodologyProperty });
        }
      }
    }

    void AddPointerFunction(StateNode state, Model.Element elt, List<ElementNode> res, string name, Model.Func fn, Model.Element tp)
    {
      if (elt == null) return;

      var val = fn.TryEval(elt);
      if (val != null)
      {
        res.Add(new FieldNode(state, new EdgeName(name), val, tp) { Category = NodeCategory.MethodologyProperty });
      }
    }

    void AddPtrType(StateNode state, Model.Element elt, List<ElementNode> res)
    {
      var f = f_field.TryEval(elt);
      if (f == null) return;

      var tp = f_field_type.TryEval(f);

      var seq = "";

      var is_seq = f_is_sequential_field.TryEval(f) as Model.Boolean;
      var is_vol = f_is_volatile_field.TryEval(f) as Model.Boolean;

      if (is_seq != null && is_vol != null && is_seq.Value == is_vol.Value)
      {
        seq = " (volatile/sequential mismatch)";
      }
      else if ((is_seq != null && is_seq.Value) || (is_vol != null && !is_vol.Value))
      {
        seq = " (sequential)";
      }
      else if ((is_seq != null && !is_seq.Value) || (is_vol != null && is_vol.Value))
      {
        seq = " (volatile)";
      }

      if (tp != null || seq != "")
      {
        res.Add(new FieldNode(state, new EdgeName("\\typeof" + seq), tp, tp_mathint) { Category = NodeCategory.MethodologyProperty });
      }
    }

    string SkolemName(Model.Func f, ref Model.Element tp)
    {
      if (f.Name.IndexOf('!') > 0)
      {
        var tok = DecodeToken(f.Name, ref tp);
        if (tok != null)
        {
          var baseName = f.Name.Substring(0, f.Name.LastIndexOf('$'));
          if (baseName.StartsWith("Q#"))
            baseName = baseName.Substring(2);
          return string.Format("{0}@{1}", baseName, ShortenToken(tok, 10, false));
        }
      }
      return null;
    }

    string GlobalName(Model.Func f, ref Model.Element tp)
    {
      if (f.Name.StartsWith("G#"))
      {
        var idx = f.Name.LastIndexOf("#dt");
        if (idx < 0) return null;
        var name = f.Name.Substring(2, idx - 2);
        tp = DecodeDT(f.Name.Substring(idx + 1));
        return string.Format("::{0}", name);
      }
      return null;
    }


    public IEnumerable<ElementNode> CommonNodes(StateNode state)
    {
      var skolems = new List<ElementNode>();

      Model.Element tp = null;

      foreach (var f in model.Functions)
      {
        if (f.Arity != 0) continue;
        var s = SkolemName(f, ref tp);
        if (s == null)
          s = GlobalName(f, ref tp);
        if (s != null)
        {
          if (tp == null)
            tp = GuessType(f.GetConstant());
          var val = WrapForUse(f.GetConstant(), tp);
          skolems.Add(new VariableNode(state, s, val, tp));
        }
      }

      return skolems;
    }

    private Model.Element GuessPtrTo(Model.Element tp)
    {
      var p = f_ptr_to.TryEval(tp);
      if (p != null) return p;
      p = f_spec_ptr_to.TryEval(tp);
      if (p != null) return p;
      var nm = model.MkFunc("*ptrto_" + TypeName(tp), 0).GetConstant();
      f_ptr_to.AddApp(nm, tp);
      return f_ptr_to.TryEval(tp);
    }

    private Model.Element PtrTo(Model.Element tp, Model.Func f_ptr_to)
    {
      var p = f_ptr_to.TryEval(tp);
      if (p != null) return p;
      var nm = model.MkFunc("*" + f_ptr_to.Name + "_" + TypeName(tp), 0).GetConstant();
      f_ptr_to.AddApp(nm, tp);
      return f_ptr_to.TryEval(tp);
    }

    private bool IsArrayField(Model.Element ptr)
    {
      return ptr != null && f_idx.TryEval(ptr, model.TryMkElement("0")) != null;
    }

    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt, Model.Element tp)
    {
      List<ElementNode> result = new List<ElementNode>();
      Model.FuncTuple tpl;

      if (elt == null) return result;

      var kind = GetKind(tp, out tpl);
      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr || kind == DataKind.Object)
      {
        var heap = state.State.TryGet("$s");
        if (heap != null)
          heap = f_heap.TryEval(heap);
        var addresses = new HashSet<Model.Element>();

        if (heap != null)
        {
          var basePtr = f_base.TryEval(elt);
          foreach (var fld in f_select_field.AppsWithArg(0, heap))
          {
            var val = f_select_value.TryEval(fld.Result, elt);
            if (val != null)
            {
              var field = fld.Args[1];
              if (!IsConstantField(field) && viewOpts.ViewLevel <= 2)
                continue;
              var addr = f_dot.TryEval(elt, field);
              if (addr != null) addresses.Add(addr);
              var node = ComputeUnionActiveOption(state, elt, val, field);
              if (node != null)
                result.Add(node);
              else
                BuildFieldNode(result, state, addr, field, val, addr);
            }
          }
          //result.Sort(CompareFields);
        }

        {
          foreach (var app in f_idx.AppsWithArg(0, elt))
          {
            var addr = app.Result;
            Model.Element val = null, atp = tp;

            addresses.Add(addr);

            foreach (var papp in f_dot.AppsWithResult(addr))
            {
              var tmp = f_select_value.OptEval(f_select_field.OptEval(heap, papp.Args[1]), papp.Args[0]);
              if (tmp != null)
              {
                val = tmp;
                var tt = f_field_type.TryEval(papp.Args[1]);
                if (tt != null) atp = tt;
              }
            }

            if (val != null)
              val = WrapForUse(val, atp);
            result.Add(new MapletNode(state, new EdgeName(this, "[%0]", app.Args[1]), val, atp) { Category = NodeCategory.Maplet });
            if (addr != null)
              result.Add(new MapletNode(state, new EdgeName(this, "&[%0]", app.Args[1]), addr, GuessPtrTo(atp)) { Category = NodeCategory.Maplet });
          }
        }

        foreach (var ptr in f_dot.AppsWithArg(0, elt))
        {
          if (addresses.Contains(ptr.Result)) continue;
          var fld = ptr.Args[1];
          var idx = f_field_arr_index.TryEval(fld);
          if (idx != null)
          {
            var xtp = f_field_type.TryEval(fld);
            result.Add(new MapletNode(state, new EdgeName(this, "&[%0] of %1", idx, f_field_arr_size.TryEval(fld)), ptr.Result, GuessPtrTo(xtp)) { Category = NodeCategory.Maplet });
          }
          if (!IsConstantField(ptr.Args[1])) continue;
          BuildFieldNode(result, state, ptr.Result, ptr.Args[1], null, ptr.Result);
        }

        AddSpecialField(state, elt, result, "\\closed", f_closed);
        AddSpecialField(state, elt, result, "\\owner", f_owners);
        AddSpecialField(state, elt, result, "\\root", f_roots);
        AddSpecialField(state, elt, result, "\\timestamp", f_timestamps);
        AddPointerFunction(state, elt, result, "\\embedding", f_prim_emb, tp_object);
        AddPointerFunction(state, elt, result, "\\addr", f_addr, tp_mathint);

        if (viewOpts.ViewLevel >= 1)
        {
          AddPtrType(state, elt, result);
          AddCasts(state, elt, result);
          var sets = new SetsNode(state, elt);
          if (!sets.IsEmpty)
            result.Add(sets);
        }

      }
      else if (kind == DataKind.Map)
      {
        var elTp = tpl.Args[1];
        foreach (var sel in model.Functions)
          if (sel.Arity == 2 && sel.Name.StartsWith("$select.$map_t"))
          {
            foreach (var app in sel.AppsWithArg(0, elt))
            {
              var val = WrapForUse(app.Result, elTp);
              var edgname = new EdgeName(this, "[%0]", app.Args[1]);
              result.Add(new MapletNode(state, edgname, val, elTp) { Category = NodeCategory.Maplet });
            }
          }
      }
      else if (kind == DataKind.Ptrset)
      {
        foreach (var sel in f_select_bool.AppsWithArg(0, elt))
        {
          var edgname = new EdgeName(this, "[%0]", sel.Args[1]);
          result.Add(new MapletNode(state, edgname, sel.Result, tp_bool) { Category = NodeCategory.Maplet });
        }
      }
      else if (kind == DataKind.Flat)
      {
        foreach (var tupl in elt.References)
        {
          if (tupl.Args.Length == 1 && tupl.Args[0] == elt)
          {
            var fname = tupl.Func.Name;
            var idx = fname.LastIndexOf('.');
            if (fname.StartsWith("RF#") && idx > 0)
            {
              fname = fname.Substring(idx + 1);
            }
            else if (fname.StartsWith("DP#p"))
            {
              fname = fname.Substring(4);
              idx = fname.IndexOf('#');
              if (idx > 0)
                fname = fname.Substring(idx + 1) + "#" + fname.Substring(0, idx);
            }
            else
            {
              fname = null;
            }

            if (fname != null)
              result.Add(new FieldNode(state, new EdgeName(fname), tupl.Result, GuessType(tupl.Result)) { Category = NodeCategory.SpecField });
          }
        }
      }

      if (!(elt is Model.Boolean))
      {
        var curState = state.State.TryGet("$s");

        foreach (var tupl in elt.References)
        {
          {
            var seenSelf = false;
            var seenState = false;
            var seenThisState = false;
            var args = tupl.Args;
            for (int i = 0; i < args.Length; ++i)
            {
              if (args[i] == elt) seenSelf = true;
              if (IsThisState(curState, args[i])) seenThisState = true;
              else if (IsSomeState(args[i])) seenState = true;
            }
            if (!seenSelf) continue; // not looking for aliases (maybe we should?)
            if (seenState && !seenThisState) continue;
          }

          var argsFmt = new StringBuilder();
          var name = tupl.Func.Name;

          var score = FunctionScore(name);
          if (score >= viewOpts.ViewLevel)
            continue;

          var retTp = GuessType(tupl.Result);
          var retVal = tupl.Result;

          var cat = NodeCategory.MethodologyProperty;
          if (name.StartsWith("F#"))
          {
            name = name.Substring(2);
            cat = NodeCategory.UserFunction;
          }

          if (name.StartsWith("DF#"))
          {
            name = name.Substring(3);
            cat = NodeCategory.UserFunction;
          }

          if (name.StartsWith("$eq.$"))
            name = "EQ";

          {
            Model.Element sktp = null;
            var sk = SkolemName(tupl.Func, ref sktp);
            if (sk != null)
            {
              name = sk;
              if (sktp != null)
                retVal = WrapForUse(tupl.Result, sktp);
              cat = NodeCategory.Maplet;
            }
          }

          {
            argsFmt.Append(name).Append("(");
            var args = new List<Model.Element>();
            foreach (var a in tupl.Args)
            {
              if (IsThisState(curState, a))
                argsFmt.Append("\\now, ");
              else if (a == elt)
                argsFmt.Append(selfMarker + ", ");
              else
              {
                argsFmt.AppendFormat("%{0}, ", args.Count);
                args.Add(a);
              }
            }
            argsFmt.Length -= 2;
            argsFmt.Append(")");
            var edgeName = new EdgeName(this, argsFmt.ToString(), args.ToArray());
            result.Add(new MapletNode(state, edgeName, retVal, retTp) { ViewLevel = score, Category = cat });
          }

        }
      }

      return result;
    }

    private FieldNode ComputeUnionActiveOption(StateNode state, Model.Element elt, Model.Element val, Model.Element field)
    {
      if (f_active_option.AppsWithResult(field).FirstOrDefault() != null)
      {
        var activeOpt = f_dot.OptEval(elt, f_int_to_field.OptEval(val));
        if (activeOpt != null)
        {
          var nm = ConstantFieldName(field);
          var fieldNode = new FieldNode(state, new EdgeName(nm), activeOpt, GuessType(activeOpt)) { Category = NodeCategory.MethodologyProperty };
          return fieldNode;
        }
      }
      return null;
    }

    private void AddCasts(StateNode state, Model.Element elt, List<ElementNode> result)
    {
      foreach (var app in f_phys_ptr_cast.AppsWithArg(0, elt))
      {
        if (app.Result != elt)
          result.Add(new MapletNode(state, new EdgeName(this, "(" + TypeName(app.Args[1]) + "*)..."), app.Result, PtrTo(app.Args[1], f_ptr_to)));
      }
      foreach (var app in f_spec_ptr_cast.AppsWithArg(0, elt))
      {
        if (app.Result != elt)
          result.Add(new MapletNode(state, new EdgeName(this, "(" + TypeName(app.Args[1]) + "^)..."), app.Result, PtrTo(app.Args[1], f_spec_ptr_to)));
      }
      var addr = f_addr.TryEval(elt);
      if (addr != null)
      {
        foreach (var app in f_blob_type.Apps)
        {
          var blob = f_address_root.TryEval(addr, app.Result);
          if (blob != null)
          {
            result.Add(new MapletNode(state, new EdgeName(this, TypeName(app.Result) + "..."), blob, app.Result));
          }
        }
      }
    }

    private void BuildFieldNode(List<ElementNode> result, StateNode state, Model.Element ptr, Model.Element field, Model.Element val, Model.Element addr)
    {
      var ftp = f_field_type.TryEval(field);
      if (val != null)
        val = WrapForUse(val, ftp);

      if (IsArrayField(ptr))
      {
        val = addr;
        addr = null;
        ftp = GuessPtrTo(ftp);
      }

      var nm = ConstantFieldName(field);
      var edgname = nm == null ? field.ToString() : nm;

      var cat = NodeCategory.PhysField;
      if (f_is_ghost_field.IsTrue(field))
        cat = NodeCategory.SpecField;
      if (nm != null && nm.Contains("<"))
        cat = NodeCategory.MethodologyProperty;

      var fieldNode = new FieldNode(state, new EdgeName(edgname), val, ftp) { Category = cat };
      result.Add(fieldNode);

      if (addr != null)
      {
        result.Add(new FieldNode(state, new EdgeName("&" + edgname), addr, GuessPtrTo(ftp)) { Category = cat });
      }
    }

    public override IEnumerable<IState> States
    {
      get
      {
        return states;
      }
    }

    private int DataTypeToString(StringBuilder sb, int level, Model.Element elt)
    {
      Model.FuncTuple ctor = null;
      int len = 1;
      string dataTypeType = null;
      foreach (var app in elt.References)
      {
        var n = app.Func.Name;
        if (app.Result == elt && n.StartsWith("DF#"))
        {
          ctor = app;
        }
        var tmp = DataTypeName(elt, app);
        if (tmp != null) dataTypeType = tmp;
      }

      if (dataTypeType != null)
      {
        if (ctor != null)
          sb.Append(ctor.Func.Name.Substring(3));
        else
          sb.Append(DataTypeShortName(elt, dataTypeType));
        if (ctor != null && ctor.Args.Length > 0)
        {
          if (level <= 0) sb.Append("(...)");
          else
          {
            sb.Append("(");
            for (int i = 0; i < ctor.Args.Length; ++i)
            {
              if (i != 0) sb.Append(", ");
              len += DataTypeToString(sb, level - 1, ctor.Args[i]);
            }
            sb.Append(")");
          }
        }
      }
      else
      {
        sb.Append(CanonicalName(elt));
      }
      return len;
    }

    private string DataTypeShortName(Model.Element elt, string tp)
    {
      var baseName = tp;

      var hd = model.MkFunc("DGH#" + tp, 1).TryEval(elt);
      if (hd != null)
      {
        foreach (var nm in hd.References)
        {
          if (nm.Func.Arity == 0 && nm.Func.Name.StartsWith("DH#"))
            baseName = nm.Func.Name.Substring(3);
        }
      }

      return baseName;
    }

    private string CanonicalBaseNameCore(string name, Model.Element elt, bool doDatatypes, ref NameSeqSuffix suff)
    {
      var vm = this;

      if (name.Contains("[") || name.Contains("'"))
        name = "";

      if (name != "")
        return name;

      var isNull = false;
      foreach (var tpl in elt.References)
      {
        var fn = tpl.Func;
        if (fn.Name.StartsWith("$select.$map_t") && fn.Arity == 2 && tpl.Args[0] == elt)
          return "map";
        if (fn.Name.StartsWith("$int_to_map_t") && tpl.Result == elt)
          return "map";

        if (fn.Arity >= 1 && tpl.Args[0] == elt)
        {
          if (fn == f_select_bool)
            return "ptrset";
        }

        if (tpl.Result == elt)
          if (fn == f_int_to_version)
            return "version";

        if (fn == f_is_null && tpl.Result == model.True)
          isNull = true;

        var dtpName = DataTypeName(elt, tpl);
        if (dtpName != null)
        {
          var sb = new StringBuilder();
          string prev = null;
          datatypeLongName[elt] = "*SELF*"; // in case we recurse (but this shouldn't happen)
          for (int lev = 0; lev < 10; lev++)
          {
            sb.Length = 0;
            var len = DataTypeToString(sb, lev, elt);
            if (prev == null || len <= maxDatatypeNameLength)
              prev = sb.ToString();
          }

          datatypeLongName[elt] = prev;
          suff = NameSeqSuffix.WhenNonZero;
          return prev;
        }
      }

      var fld = vm.f_field.TryEval(elt);
      if (fld != null)
      {
        var tp = vm.f_field_type.TryEval(fld);
        if (tp != null)
        {
          var n = vm.TryTypeName(tp);
          if (n != null)
          {
            if (isNull)
              return "(" + n + "*)NULL";
            return n;
          }
        }
      }

      return "";
    }

    protected override string CanonicalBaseName(Model.Element elt, out NameSeqSuffix suff)
    {
      var lit = this.LiteralName(elt);
      if (lit != null)
      {
        suff = NameSeqSuffix.None;
        return lit;
      }
      if (datatypeLongName.TryGetValue(elt, out lit))
      {
        suff = NameSeqSuffix.WhenNonZero;
        return lit;
      }

      var name = base.CanonicalBaseName(elt, out suff);
      name = CanonicalBaseNameCore(name, elt, true, ref suff);

      return name;
    }

    public override string PathName(IEnumerable<IDisplayNode> path)
    {
      var sb = new StringBuilder();
      foreach (var d in path)
      {
        var name = d.Name;
        if (name == "") continue; // can that happen?
        if (name.Contains("(") && name.Contains(selfMarker))
        {
          var repl = name.Replace(selfMarker, sb.ToString());
          sb.Length = 0;
          sb.Append(repl);
        }
        else
        {
          if (sb.Length > 0 && name[0] != '[')
            sb.Append("->");
          sb.Append(d.Name);
        }
      }

      return sb.ToString();
    }
  }

  class StateNode : NamedState
  {
    internal VccModel vm;
    internal List<VariableNode> vars;
    internal List<ElementNode> commons;
    internal int index;
    internal string capturedStateName;

    public StateNode(VccModel parent, Model.CapturedState s)
      : base(s, parent)
    {
      this.capturedStateName = s.Name;
      this.vm = parent;
    }

    internal void SetupVars()
    {
      if (vars != null) return;
      vars = new List<VariableNode>();

      var names = Util.Empty<string>();

      if (vm.states.Count > 0)
      {
        var prev = vm.states.Last();
        names = prev.vars.Map(v => v.realName);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names)
      {
        var localName = vm.GetUserVariableName(v);
        if (localName != null)
        {
          var tp = vm.LocalType(v);
          var val = state.TryGet(v);
          val = vm.WrapForUse(val, tp);
          var vn = new VariableNode(this, v, val, tp) { ShortName = localName };
          vn.updatedHere = vm.states.Count > 0 && curVars.ContainsKey(v);
          if (curVars.ContainsKey(v))
            vm.RegisterLocalValue(vn.Name, val);
          vars.Add(vn);
        }
      }

      vm.Flush(vars);

      commons = new List<ElementNode>();
      commons.AddRange(vm.CommonNodes(this));
    }

    public override IEnumerable<IDisplayNode> Nodes
    {
      get
      {
        return vars.Concat(commons);
      }
    }

    public override string CapturedStateName
    {
      get
      {
        return this.capturedStateName;
      }
    }
  }

  class ElementNode : DisplayNode
  {
    protected StateNode stateNode;
    protected Model.Element tp;
    protected VccModel vm { get { return stateNode.vm; } }

    public ElementNode(StateNode st, EdgeName name, Model.Element elt, Model.Element tp)
      : base(st.vm, name, elt)
    {
      this.stateNode = st;
      this.tp = tp;
    }

    protected override void ComputeChildren()
    {
      children.AddRange(vm.GetExpansion(stateNode, element, tp));
    }

    public override string ToolTip
    {
      get
      {
        var sb = new StringBuilder();
        if (tp != null)
          sb.AppendFormat("Type: {0}\n", vm.TypeName(tp));
        var i = element as Model.Integer;
        if (i != null)
        {
          var n = System.Numerics.BigInteger.Parse(i.Numeral);
          sb.AppendFormat("Value: {0} (0x{1:x})\n", n, n);
        }
        else if (element != null)
        {
          sb.AppendFormat("Value: {0}\n", element);
        }
        return sb.ToString();
      }
    }
  }

  class SetsNode : ElementNode
  {
    List<Model.Element> refs = new List<Model.Element>();

    public SetsNode(StateNode par, Model.Element elt)
      : base(par, new EdgeName("\\in ..."), null, null)
    {
      children = new List<IDisplayNode>();
      foreach (var app in vm.f_select_bool.AppsWithArg(1, elt))
      {
        children.Add(
          new MapletNode(par, new EdgeName(vm, VccModel.selfMarker + " \\in %0", app.Args[0]), app.Result, vm.tp_bool) { Category = NodeCategory.MethodologyProperty });
        refs.Add(app.Args[0]);
      }
      Category = NodeCategory.MethodologyProperty;
    }

    public override IEnumerable<Model.Element> References
    {
      get
      {
        return refs;
      }
    }

    public bool IsEmpty { get { return children.Count == 0; } }
  }


  class FieldNode : ElementNode
  {
    public FieldNode(StateNode par, EdgeName realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
    }
  }

  class MapletNode : ElementNode
  {
    public MapletNode(StateNode par, EdgeName realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
    }
  }

  class VariableNode : ElementNode
  {
    public bool updatedHere;
    public string realName;

    public VariableNode(StateNode par, string realName, Model.Element elt, Model.Element tp)
      : base(par, new EdgeName(realName), elt, tp)
    {
      this.realName = realName;
    }

    public override string ShortName
    {
      set { this.name = new EdgeName(value); }
      get { return this.name.ToString(); }
    }
  }
}
