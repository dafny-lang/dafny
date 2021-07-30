// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie.ModelViewer
{
  public enum NameSeqSuffix
  {
    None,
    WhenNonZero,
    Always
  }

  public abstract class LanguageModel
  {
    private readonly Dictionary<string, int> baseNameUse = new();
    private readonly Dictionary<Model.Element, string> canonicalName = new();
    private readonly Dictionary<Model.Element, string> localValue = new();
    public readonly Model model;

    private bool UseLocalsForCanonicalNames => false;

    private readonly ViewOptions viewOpts;
    public LanguageModel(Model model, ViewOptions opts)
    {
      this.model = model;
      viewOpts = opts;
    }

    // Elements (other than integers and Booleans) get canonical names of the form
    // "<base>'<idx>", where <base> is returned by this function, and <idx> is given
    // starting with 0, and incrementing when there are conflicts between bases.
    //
    // This function needs to return an appropriate base name for the element. It is given
    // the element.
    //
    // A reasonable strategy is to check if it's a name of the local, and if so return it,
    // and otherwise use the type of element (e.g., return "seq" for elements representing
    // sequences). It is also possible to return "" in such cases.
    //
    // The suff output parameter specifies whether the number sequence suffix should be
    // always added, only when it's non-zero, or never.
    protected virtual string CanonicalBaseName(Model.Element elt, out NameSeqSuffix suff)
    {
      string res;
      if (elt is Model.Integer || elt is Model.Boolean)
      {
        suff = NameSeqSuffix.None;
        return elt.ToString();
      }
      suff = NameSeqSuffix.Always;
      if (UseLocalsForCanonicalNames)
      {
        if (localValue.TryGetValue(elt, out res))
          return res;
      }
      return "";
    }

    public void RegisterLocalValue(string name, Model.Element elt)
    {
      string curr;
      if (localValue.TryGetValue(elt, out curr) && CompareFieldNames(name, curr) >= 0)
        return;
      localValue[elt] = name;
    }

    protected string AppendSuffix(string baseName, int id)
    {
      return baseName + "'" + id;
    }

    public string CanonicalName(Model.Element elt)
    {
      string res;
      if (elt == null) return "?";
      if (canonicalName.TryGetValue(elt, out res)) return res;
      NameSeqSuffix suff;
      var baseName = CanonicalBaseName(elt, out suff);
      if (baseName == "")
        suff = NameSeqSuffix.Always;
      if (baseName == "null")
        return baseName;

      if (viewOpts.DebugMode && !(elt is Model.Boolean) && !(elt is Model.Number))
      {
        baseName += string.Format("({0})", elt);
        suff = NameSeqSuffix.WhenNonZero;
      }

      int cnt;
      if (!baseNameUse.TryGetValue(baseName, out cnt))
        cnt = -1;
      cnt++;

      if (suff == NameSeqSuffix.Always || (cnt > 0 && suff == NameSeqSuffix.WhenNonZero))
        res = AppendSuffix(baseName, cnt);
      else
        res = baseName;

      baseNameUse[baseName] = cnt;
      canonicalName.Add(elt, res);
      return res;
    }

    static ulong GetNumber(string s, int beg)
    {
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

    public int CompareFieldNames(string f1, string f2)
    {
      var len = Math.Min(f1.Length, f2.Length);
      var numberPos = -1;
      for (int i = 0; i < len; ++i)
      {
        var c1 = f1[i];
        var c2 = f2[i];
        if ('0' <= c1 && c1 <= '9' && '0' <= c2 && c2 <= '9')
        {
          numberPos = i;
          break;
        }
        if (c1 != c2)
          break;
      }

      if (numberPos >= 0)
      {
        var v1 = GetNumber(f1, numberPos);
        var v2 = GetNumber(f2, numberPos);

        if (v1 < v2) return -1;
        if (v1 > v2) return 1;
      }

      return string.CompareOrdinal(f1, f2);
    }

    public class SourceLocation
    {
      public string Filename;
      public string AddInfo;
      public int Line;
      public int Column;
    }

    // example parsed token: @"c:\users\foo\bar.c(12,10) : random string"
    // the ": random string" part is optional
    public SourceLocation TryParseSourceLocation(string name)
    {
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
    public string ShortenToken(string tok, int fnLimit, bool addAddInfo)
    {
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

  public class ViewOptions
  {
    // 0 - Normal
    // 1 - Expert
    // 2 - Everything
    // 3 - Include the kitchen sink
    public int ViewLevel = 1;
    public bool DebugMode;
  }

  public static class Util
  {

    public static IEnumerable<T> Empty<T>() { yield break; }

    public static IEnumerable<T> Map<S, T>(this IEnumerable<S> inp, Func<S, T> conv)
    {
      foreach (var s in inp) yield return conv(s);
    }
    
  }

}
