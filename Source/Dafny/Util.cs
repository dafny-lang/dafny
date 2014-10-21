using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;

using Microsoft.Boogie;


namespace Microsoft.Dafny {
  class Util
  {
    public static string Comma<T>(IEnumerable<T> l, Func<T, string> f) {
      return Comma(",", l, f);
    }

    public static string Comma<T>(string comma, IEnumerable<T> l, Func<T,string> f) {
      string res = "";
      string c = "";
      foreach(var t in l) {
        res += c + f(t);
        c = comma;
      }
      return res;
    }

    public static List<B> Map<A,B>(IEnumerable<A> xs, Func<A,B> f)
    {
      List<B> ys = new List<B>();
      foreach (A x in xs) {
        ys.Add(f(x));
      }
      return ys;
    }

    public static List<A> Nil<A>() {
      return new List<A>();
    }

    public static List<A> Singleton<A>(A x) {
      return new List<A> { x };
    }

    public static List<A> Cons<A>(A x, List<A> xs) {
      return Concat(Singleton(x), xs);
    }

    public static List<A> Snoc<A>(List<A> xs, A x) {
      return Concat(xs, Singleton(x));
    }

    public static List<A> Concat<A>(List<A> xs, List<A> ys) {
      List<A> cpy = new List<A>(xs);
      cpy.AddRange(ys);
      return cpy;
    }

    public static Dictionary<A,B> Dict<A,B>(IEnumerable<A> xs, IEnumerable<B> ys) {
      return Dict<A,B>(xs.Zip(ys)); 
    }

    public static Dictionary<A,B> Dict<A,B>(IEnumerable<Tuple<A,B>> xys) {
      Dictionary<A,B> res = new Dictionary<A,B>();
      foreach (var p in xys) {
        res[p.Item1] = p.Item2; 
      }
      return res;
    }

    /// <summary>
    /// For "S" returns S and false.
    /// For @"S" return S and true.
    /// Assumes that s has one of these forms.
    /// </summary>
    public static string RemoveParsedStringQuotes(string s, out bool isVerbatimString) {
      Contract.Requires(s != null);
      var len = s.Length;
      if (s[0] == '@') {
        isVerbatimString = true;
        return s.Substring(2, len - 3);
      } else {
        isVerbatimString = false;
        return s.Substring(1, len - 2);
      }
    }
    /// <summary>
    /// Replaced any escaped characters in s by the actual character that the escaping represents.
    /// Assumes s to be a well-parsed string.
    /// </summary>
    public static string RemoveEscaping(string s, bool isVerbatimString) {
      Contract.Requires(s != null);
      var sb = new StringBuilder();
      UnescapedCharacters(s, isVerbatimString).Iter(ch => sb.Append(ch));
      return sb.ToString();
    }
    /// <summary>
    /// Returns the characters of the well-parsed string p, replacing any
    /// escaped characters by the actual characters.
    /// </summary>
    public static IEnumerable<char> UnescapedCharacters(string p, bool isVerbatimString) {
      Contract.Requires(p != null);
      if (isVerbatimString) {
        var skipNext = false;
        foreach (var ch in p) {
          if (skipNext) {
            skipNext = false;
          } else {
            yield return ch;
            if (ch == '"') {
              skipNext = true;
            }
          }
        }
      } else {
        var i = 0;
        while (i < p.Length) {
          char special = ' ';  // ' ' indicates not special
          if (p[i] == '\\') {
            switch (p[i + 1]) {
              case '\'': special = '\''; break;
              case '\"': special = '\"'; break;
              case '\\': special = '\\'; break;
              case '\0': special = '\0'; break;
              case 'n': special = '\n'; break;
              case 'r': special = '\r'; break;
              case 't': special = '\t'; break;
              case 'u':
                int ch = HexValue(p[i + 1]);
                ch = 16 * ch + HexValue(p[i + 2]);
                ch = 16 * ch + HexValue(p[i + 3]);
                ch = 16 * ch + HexValue(p[i + 4]);
                yield return (char)ch;
                i += 5;
                continue;
              default:
                break;
            }
          }
          if (special != ' ') {
            yield return special;
            i += 2;
          } else {
            yield return p[i];
            i++;
          }
        }
      }
    }

    /// <summary>
    /// Converts a hexadecimal digit to an integer.
    /// Assumes ch does represent a hexadecimal digit; alphabetic digits can be in either case.
    /// </summary>
    public static int HexValue(char ch) {
      if ('a' <= ch && ch <= 'f') {
        return ch - 'a' + 10;
      } else if ('A' <= ch && ch <= 'F') {
        return ch - 'A' + 10;
      } else {
        return ch - '0';
      }
    }

  }
}
