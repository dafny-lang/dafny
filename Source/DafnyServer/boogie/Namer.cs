using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Numerics;

namespace Microsoft.Boogie.ModelViewer
{
  public enum NameSeqSuffix
  {
    None,
    WhenNonZero,
    Always
  }

  public abstract class LanguageModel : ILanguageSpecificModel
  {
    protected Dictionary<string, int> baseNameUse = new Dictionary<string, int>();
    protected Dictionary<Model.Element, string> canonicalName = new Dictionary<Model.Element, string>();
    protected Dictionary<string, Model.Element> invCanonicalName = new Dictionary<string, Model.Element>();
    protected Dictionary<Model.Element, string> localValue = new Dictionary<Model.Element, string>();
    protected Dictionary<string, SourceViewState> sourceLocations = new Dictionary<string, SourceViewState>();
    public readonly Model model;

    protected virtual bool UseLocalsForCanonicalNames
    {
      get { return false; }
    }

    public readonly ViewOptions viewOpts;
    public LanguageModel(Model model, ViewOptions opts)
    {
      this.model = model;
      viewOpts = opts;
    }

    public string AsPow2(Model.Integer elt)
    {
      var n = BigInteger.Parse(elt.Numeral);
      var pow = new BigInteger(4096 * 4);
      var k = 14;
      var neg = false;

      if (n < 0)
      {
        n = -n;
        neg = true;
      }

      while (k < 150)
      {
        var diff = pow / 1000;
        if (pow - diff < n && n < pow + diff)
        {
          diff = n - pow;
          var res = string.Format("2^{0}{1}{2}", k, diff >= 0 ? "+" : "", diff);
          if (neg) res = "-(" + res + ")";
          return res;
        }
        if (n < pow) break;
        k++;
        pow *= 2;
      }

      return elt.ToString();
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

    public virtual void RegisterLocalValue(string name, Model.Element elt)
    {
      string curr;
      if (localValue.TryGetValue(elt, out curr) && CompareFieldNames(name, curr) >= 0)
        return;
      localValue[elt] = name;
    }

    protected virtual string AppendSuffix(string baseName, int id)
    {
      return baseName + "'" + id.ToString();
    }

    public virtual string CanonicalName(Model.Element elt)
    {
      string res;
      if (elt == null) return "?";
      if (canonicalName.TryGetValue(elt, out res)) return res;
      NameSeqSuffix suff;
      var baseName = CanonicalBaseName(elt, out suff);
      if (baseName == "")
        suff = NameSeqSuffix.Always;

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
      invCanonicalName[res.Replace(" ", "")] = elt;
      return res;
    }

    public virtual Model.Element FindElement(string canonicalName)
    {
      Model.Element res;
      if (invCanonicalName.TryGetValue(canonicalName.Replace(" ", ""), out res))
        return res;
      return null;
    }

    public virtual string PathName(IEnumerable<IDisplayNode> path)
    {
      return path.Select(n => n.Name).Concat(".");
    }

    public abstract IEnumerable<IState> States { get; }

    /// <summary>
    /// Walks each input tree in BFS order, and force evaluation of Name and Value properties
    /// (to get reasonable numbering of canonical values).
    /// </summary>
    public void Flush(IEnumerable<IDisplayNode> roots)
    {
      var workList = new Queue<IDisplayNode>();

      Action<IEnumerable<IDisplayNode>> addList = (IEnumerable<IDisplayNode> nodes) =>
      {
        var ch = new Dictionary<string, IDisplayNode>();
        foreach (var x in nodes)
        {
          if (ch.ContainsKey(x.Name))
          {
            // throw new System.InvalidOperationException("duplicated model entry: " + x.Name);
          }
          ch[x.Name] = x;
        }
        foreach (var k in SortFields(nodes))
          workList.Enqueue(ch[k]);
      };

      addList(roots);

      var visited = new HashSet<Model.Element>();
      while (workList.Count > 0)
      {
        var n = workList.Dequeue();

        var dummy1 = n.Name;
        var dummy2 = n.Value;

        if (n.Element != null)
        {
          if (visited.Contains(n.Element))
            continue;
          visited.Add(n.Element);
        }

        addList(n.Children);
      }
    }

    #region field name sorting
    /*
    static bool HasSpecialChars(string s)
    {
      for (int i = 0; i < s.Length; ++i)
        switch (s[i]) {
          case '[':
          case '<':
          case '>':
          case ']': 
          case '#':
          case '\\':
          case '(':
          case ')':
            return true;
        }
      return false;
    }
     */

    static ulong GetNumber(string s, int beg)
    {
      ulong res = 0;
      while (beg < s.Length)
      {
        var c = s[beg];
        if ('0' <= c && c <= '9')
        {
          res *= 10;
          res += (uint)c - (uint)'0';
        }
        beg++;
      }
      return res;
    }

    public virtual int CompareFieldNames(string f1, string f2)
    {
      /*
      bool s1 = HasSpecialChars(f1);
      bool s2 = HasSpecialChars(f2);
      if (s1 && !s2)
        return 1;
      if (!s1 && s2)
        return -1; */
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
        else if (v1 > v2) return 1;
      }

      return string.CompareOrdinal(f1, f2);
    }

    public virtual int CompareFields(IDisplayNode n1, IDisplayNode n2)
    {
      var diff = (int)n1.Category - (int)n2.Category;
      if (diff != 0) return diff;
      else return CompareFieldNames(n1.Name, n2.Name);
    }

    public virtual IEnumerable<string> SortFields(IEnumerable<IDisplayNode> fields_)
    {
      var fields = new List<IDisplayNode>(fields_);
      fields.Sort(CompareFields);
      return fields.Select(f => f.Name);
    }
    #endregion

    #region Displaying source code
    class Position : IComparable<Position>
    {
      public int Line, Column, Index;
      public int CharPos;
      public string Name;

      public int CompareTo(Position other)
      {
        if (this.Line == other.Line)
          return this.Column - other.Column;
        return this.Line - other.Line;
      }
    }

    public class SourceLocation
    {
      public string Filename;
      public string AddInfo;
      public int Line;
      public int Column;
    }

    public SourceViewState GetSourceLocation(string name)
    {
      SourceViewState res;
      sourceLocations.TryGetValue(name, out res);
      return res;
    }

    // example parsed token: @"c:\users\foo\bar.c(12,10) : random string"
    // the ": random string" part is optional
    public virtual SourceLocation TryParseSourceLocation(string name)
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

    static char[] dirSeps = new char[] { '\\', '/' };
    public virtual string ShortenToken(string tok, int fnLimit, bool addAddInfo)
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
      else
      {
        return tok;
      }
    }

    protected virtual void RtfAppend(StringBuilder sb, char c, ref int pos)
    {
      pos++;
      switch (c)
      {
        case '\r': pos--; break;
        case '\\': sb.Append("\\\\"); break;
        case '\n': sb.Append("\\par\n"); break;
        case '{': sb.Append("\\{"); break;
        case '}': sb.Append("\\}"); break;
        default: sb.Append(c); break;
      }
    }

    protected virtual void RtfAppendStateIdx(StringBuilder sb, string label, ref int pos)
    {
      label += ".";
      pos += label.Length;
      sb.Append(@"{\sub\cf5\highlight4 ").Append(label).Append("}");
    }

    protected virtual void RtfAppendLineNo(StringBuilder sb, int num, ref int pos)
    {
      string n = string.Format("{0:0000}: ", num);
      pos += n.Length;
      sb.Append(@"{\cf6 ").Append(n).Append("}");
    }

    protected virtual void GenerateSourceLocations(IEnumerable<NamedState> states)
    {
      sourceLocations = new Dictionary<string, SourceViewState>();

      var files = new Dictionary<string, List<Position>>();
      var sIdx = -1;

      foreach (var s in states)
      {
        var sn = s.CapturedStateName;
        sIdx++;
        var loc = TryParseSourceLocation(sn);
        if (loc == null) continue;

        List<Position> positions;
        if (!files.TryGetValue(loc.Filename, out positions))
        {
          positions = new List<Position>();
          files[loc.Filename] = positions;
        }
        positions.Add(new Position() { Name = sn, Line = loc.Line, Column = loc.Column, Index = sIdx });
      }

      foreach (var kv in files)
      {
        var positions = kv.Value;
        positions.Sort();

        string content = "";
        if (System.IO.File.Exists(kv.Key))
        {
          try
          {
            content = System.IO.File.ReadAllText(kv.Key);
          }
          catch
          {
            continue;
          }
        }
        else
        {
          continue;
        }

        var pos = new Position() { Line = 1, Column = 1 };
        var currPosIdx = 0;
        var output = new StringBuilder();
        RtfAppendLineNo(output, pos.Line, ref pos.CharPos);

        foreach (var c in content)
        {
          if (c == '\n')
          {
            pos.Column = int.MaxValue; // flush remaining positions in this line
          }

          while (currPosIdx < positions.Count && pos.CompareTo(positions[currPosIdx]) >= 0)
          {
            positions[currPosIdx].CharPos = pos.CharPos;
            RtfAppendStateIdx(output, positions[currPosIdx].Index.ToString(), ref pos.CharPos);
            currPosIdx++;
          }

          RtfAppend(output, c, ref pos.CharPos);

          if (c == '\n')
          {
            pos.Line++;
            pos.Column = 1;
            RtfAppendLineNo(output, pos.Line, ref pos.CharPos);
          }
          else
          {
            pos.Column++;
          }
        }

        var resStr = output.ToString();
        foreach (var p in positions)
        {
          sourceLocations[p.Name] = new SourceViewState() { Header = p.Name, Location = p.CharPos, RichTextContent = resStr };
        }
      }
    }
    #endregion
  }

  public abstract class NamedState : IState
  {
    protected Model.CapturedState state;
    private LanguageModel langModel; // no point making it protected - they will need VccModel, DafnyModel

    public NamedState(Model.CapturedState s, LanguageModel lm)
    {
      this.state = s;
      this.langModel = lm;
    }

    public Model.CapturedState State
    {
      get { return state; }
    }

    public virtual string Name
    {
      get
      {
        return langModel.ShortenToken(state.Name, 20, true);
      }
    }

    // by overriding this, one state can masqureade another
    public virtual string CapturedStateName
    {
      get { return State.Name; }
    }

    public virtual SourceViewState ShowSource()
    {
      return langModel.GetSourceLocation(CapturedStateName);
    }

    public abstract IEnumerable<IDisplayNode> Nodes { get; }
  }

  public class EdgeName
  {
    ILanguageSpecificModel langModel;
    string format;
    string cachedName;
    Model.Element[] args;

    public EdgeName(ILanguageSpecificModel n, string format, params Model.Element[] args)
    {
      this.langModel = n;
      this.format = format;
      this.args = args.ToArray();
    }

    public EdgeName(string name) : this(null, name)
    {
      Util.Assert(name != null);
    }

    public override string ToString()
    {
      if (cachedName != null)
        return cachedName;
      cachedName = Format();
      return cachedName;
    }

    public override int GetHashCode()
    {
      int res = format.GetHashCode();
      foreach (var c in args)
      {
        res += c.GetHashCode();
        res *= 13;
      }
      return res;
    }

    public override bool Equals(object obj)
    {
      EdgeName e = obj as EdgeName;
      if (e == null) return false;
      if (e == this) return true;
      if (e.format != this.format || e.args.Length != this.args.Length)
        return false;
      for (int i = 0; i < this.args.Length; ++i)
        if (this.args[i] != e.args[i])
          return false;
      return true;
    }

    protected virtual string Format()
    {
      if (args == null || args.Length == 0)
        return format;

      var res = new StringBuilder(format.Length);
      for (int i = 0; i < format.Length; ++i)
      {
        var c = format[i];

        /*
        var canonical = false;
        if (c == '%' && i < format.Length - 1) {
          if (format[i + 1] == 'c') {
            ++i;
            canonical = true;
          }
        }
         */

        if (c == '%' && i < format.Length - 1)
        {
          var j = i + 1;
          while (j < format.Length && char.IsDigit(format[j]))
            j++;
          var len = j - i - 1;
          if (len > 0)
          {
            var idx = int.Parse(format.Substring(i + 1, len));
            res.Append(langModel.CanonicalName(args[idx]));
            i = j - 1;
            continue;
          }
        }

        res.Append(c);
      }

      return res.ToString();
    }

    public virtual IEnumerable<Model.Element> Dependencies
    {
      get { return args; }
    }
  }

}
