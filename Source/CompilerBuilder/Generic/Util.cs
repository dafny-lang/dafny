// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Diagnostics.Contracts;
using System.Text;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny {
  public static class Sets {
    public static ISet<T> Empty<T>() {
      return new HashSet<T>();
    }
  }

  public static class Util {

  
    public static readonly Regex Utf16Escape = new Regex(@"\\u([0-9a-fA-F]{4})");
    public static readonly Regex UnicodeEscape = new Regex(@"\\U\{([0-9a-fA-F_]+)\}");
    private static readonly Regex NullEscape = new Regex(@"\\0");

    private static string ToUtf16Escape(char c, bool addBraces = false) {
      if (addBraces) {
        return $"\\u{{{(int)c:x4}}}";
      } else {
        return $"\\u{(int)c:x4}";
      }
    }

    public static string ReplaceNullEscapesWithCharacterEscapes(string s) {
      return ReplaceTokensWithEscapes(s, NullEscape, match => "\\u0000");
    }
    public static string ExpandUnicodeEscapes(string s, bool lowerCaseU) {
      return ReplaceTokensWithEscapes(s, UnicodeEscape, match => {
        var hexDigits = Util.RemoveUnderscores(match.Groups[1].Value);
        var padChars = 8 - hexDigits.Length;
        return (lowerCaseU ? "\\u" : "\\U") + new string('0', padChars) + hexDigits;
      });
    }

    public static string UnicodeEscapesToLowercase(string s) {
      return ReplaceTokensWithEscapes(s, UnicodeEscape, match =>
        $"\\u{{{RemoveUnderscores(match.Groups[1].Value)}}}");
    }

    public static string UnicodeEscapesToUtf16Escapes(string s) {
      return ReplaceTokensWithEscapes(s, UnicodeEscape, match => {
        var utf16CodeUnits = new char[2];
        var hexDigits = RemoveUnderscores(match.Groups[1].Value);
        var codePoint = new Rune(Convert.ToInt32(hexDigits, 16));
        var codeUnits = codePoint.EncodeToUtf16(utf16CodeUnits);
        if (codeUnits == 2) {
          return ToUtf16Escape(utf16CodeUnits[0]) + ToUtf16Escape(utf16CodeUnits[1]); ;
        } else {
          return ToUtf16Escape(utf16CodeUnits[0]);
        }
      });
    }


    public static string ReplaceTokensWithEscapes(string s, Regex pattern, MatchEvaluator evaluator) {
      return string.Join("",
        TokensWithEscapes(s, false)
          .Select(token => pattern.Replace(token, evaluator)));
    }

    public static bool MightContainNonAsciiCharacters(string s, bool isVerbatimString) {
      // This is conservative since \u and \U escapes could be ASCII characters,
      // but that's fine since this method is just used as a conservative guard.
      return TokensWithEscapes(s, isVerbatimString).Any(e =>
        e.Any(c => !char.IsAscii(c)) || e.StartsWith(@"\u") || e.StartsWith(@"\U"));
    }

    /// <summary>
    /// Enumerates the sequence of regular characters and escape sequences in the given well-parsed string.
    /// For example, "ab\tuv\u12345" may be broken up as ["a", "b", "\t", "u", "v", "\u1234", "5"].
    /// Consecutive non-escaped characters may or may not be enumerated as a single string.
    /// </summary>
    public static IEnumerable<string> TokensWithEscapes(string p, bool isVerbatimString) {
      Contract.Requires(p != null);
      if (isVerbatimString) {
        var skipNext = false;
        foreach (var ch in p) {
          if (skipNext) {
            skipNext = false;
          } else {
            if (ch == '"') {
              skipNext = true;
              yield return "\"";
            } else {
              yield return ch.ToString();
            }
          }
        }
      } else {
        var i = 0;
        while (i < p.Length) {
          if (p[i] == '\\') {
            switch (p[i + 1]) {
              case 'u':
                yield return p[i..(i + 6)];
                i += 6;
                break;
              case 'U':
                var escapeEnd = p.IndexOf('}', i + 2) + 1;
                yield return p[i..escapeEnd];
                i = escapeEnd;
                continue;
              default:
                yield return p[i..(i + 2)];
                i += 2;
                break;
            }
          } else if (char.IsHighSurrogate(p[i])) {
            yield return p[i..(i + 2)];
            i += 2;
          } else {
            yield return p[i].ToString();
            i++;
          }
        }
      }
    }
    

    /// <summary>
    /// Returns the characters of the well-parsed string p, replacing any
    /// escaped characters by the actual characters.
    /// 
    /// It also converts surrogate pairs to their equivalent code points
    /// if --unicode-char is enabled - these are synthesized by the parser when
    /// reading the original UTF-8 source, but don't represent the true character values.
    /// </summary>
    public static IEnumerable<int> UnescapedCharacters(bool unicodeChars, string p, bool isVerbatimString) {
      if (isVerbatimString) {
        foreach (var s in TokensWithEscapes(p, true)) {
          if (s == "\"\"") {
            yield return '"';
          } else {
            foreach (var c in s) {
              yield return c;
            }
          }
        }
      } else {
        foreach (var s in TokensWithEscapes(p, false)) {
          switch (s) {
            case @"\'": yield return '\''; break;
            case @"\""": yield return '"'; break;
            case @"\\": yield return '\\'; break;
            case @"\0": yield return '\0'; break;
            case @"\n": yield return '\n'; break;
            case @"\r": yield return '\r'; break;
            case @"\t": yield return '\t'; break;
            case { } when s.StartsWith(@"\u"):
              yield return Convert.ToInt32(s[2..], 16);
              break;
            case { } when s.StartsWith(@"\U"):
              yield return Convert.ToInt32(Util.RemoveUnderscores(s[3..^1]), 16);
              break;
            case { } when unicodeChars && char.IsHighSurrogate(s[0]):
              yield return char.ConvertToUtf32(s[0], s[1]);
              break;
            default:
              foreach (var c in s) {
                yield return c;
              }
              break;
          }
        }
      }
    }
    
    public static Task WaitForComplete<T>(this IObservable<T> observable) {
      var result = new TaskCompletionSource();
      observable.Subscribe(_ => { }, e => result.SetException(e), () => result.SetResult());
      return result.Task;
    }

    public static string CapitaliseFirstLetter(this string input) {
      if (input.Length > 0) {
        return char.ToUpper(input[0]) + input.Substring(1);
      }

      return input;
    }

    public static bool LessThanOrEquals<T>(this T first, T second)
      where T : IComparable<T> {
      return first.CompareTo(second) != 1;
    }

    public static Task<U> SelectMany<T, U>(this Task<T> task, Func<T, Task<U>> f) {
#pragma warning disable VSTHRD003
      return Select(task, f).Unwrap();
#pragma warning restore VSTHRD003
    }

    public static Task<U> Select<T, U>(this Task<T> task, Func<T, U> f) {
#pragma warning disable VSTHRD105
      return task.ContinueWith(completedTask => f(completedTask.Result), TaskContinuationOptions.OnlyOnRanToCompletion);
#pragma warning restore VSTHRD105
    }

    public static string Comma<T>(this IEnumerable<T> l) {
      return Comma(l, s => s.ToString());
    }

    public static string Comma<T>(this IEnumerable<T> l, Func<T, string> f) {
      return Comma(", ", l, (element, index) => f(element));
    }

    public static string Comma<T>(this IEnumerable<T> l, Func<T, int, string> f) {
      return Comma(", ", l, f);
    }

    public static string Comma<T>(string comma, IEnumerable<T> l, Func<T, string> f) {
      return Comma(comma, l, (element, index) => f(element));
    }

    public static string Comma<T>(string comma, IEnumerable<T> l, Func<T, int, string> f) {
      Contract.Requires(comma != null);
      string res = "";
      string c = "";
      int index = 0;
      foreach (var t in l) {
        res += c + f(t, index);
        c = comma;
        index++;
      }
      return res;
    }

    public static string Comma(int count, Func<int, string> f) {
      Contract.Requires(0 <= count);
      return Comma(", ", count, f);
    }

    public static string Comma(string comma, int count, Func<int, string> f) {
      Contract.Requires(comma != null);
      Contract.Requires(0 <= count);
      string res = "";
      string c = "";
      for (int i = 0; i < count; i++) {
        res += c + f(i);
        c = comma;
      }
      return res;
    }

    public static IEnumerable<(T, int)> Indexed<T>(this IEnumerable<T> enumerable) {
      return enumerable.Select((value, index) => (value, index));
    }

    public static string PrintableNameList(List<string> names, string grammaticalConjunction) {
      Contract.Requires(names != null);
      Contract.Requires(1 <= names.Count);
      Contract.Requires(grammaticalConjunction != null);
      var n = names.Count;
      if (n == 1) {
        return string.Format("'{0}'", names[0]);
      } else if (n == 2) {
        return string.Format("'{0}' {1} '{2}'", names[0], grammaticalConjunction, names[1]);
      } else {
        var s = "";
        for (int i = 0; i < n - 1; i++) {
          s += string.Format("'{0}', ", names[i]);
        }
        return s + string.Format("{0} '{1}'", grammaticalConjunction, names[n - 1]);
      }
    }

    public static string Repeat(int count, string s) {
      Contract.Requires(0 <= count);
      Contract.Requires(s != null);
      // special-case trivial cases
      if (count == 0) {
        return "";
      } else if (count == 1) {
        return s;
      } else {
        return Comma("", count, _ => s);
      }
    }

    public static string Plural(int n) {
      Contract.Requires(0 <= n);
      return n == 1 ? "" : "s";
    }

    public static List<B> Map<A, B>(IEnumerable<A> xs, Func<A, B> f) {
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

    public static List<A> List<A>(params A[] xs) {
      return xs.ToList();
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

    public static Dictionary<A, B> Dict<A, B>(IEnumerable<A> xs, IEnumerable<B> ys) {
      return Dict<A, B>(Enumerable.Zip(xs, ys).Select(x => new Tuple<A, B>(x.First, x.Second)));
    }

    public static Dictionary<A, B> Dict<A, B>(IEnumerable<Tuple<A, B>> xys) {
      Dictionary<A, B> res = new Dictionary<A, B>();
      foreach (var p in xys) {
        res[p.Item1] = p.Item2;
      }
      return res;
    }

    public static void AddToDict<A, B>(Dictionary<A, B> dict, List<A> xs, List<B> ys) {
      Contract.Requires(dict != null);
      Contract.Requires(xs != null);
      Contract.Requires(ys != null);
      Contract.Requires(xs.Count == ys.Count);
      for (var i = 0; i < xs.Count; i++) {
        dict.Add(xs[i], ys[i]);
      }
    }

    /// <summary>
    /// Returns s but with all occurrences of '_' removed.
    /// </summary>
    public static string RemoveUnderscores(string s) {
      Contract.Requires(s != null);
      return s.Replace("_", "");
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



    public static V GetOrDefault<K, V, V2>(this IReadOnlyDictionary<K, V2> dictionary, K key, Func<V> createValue)
      where V2 : V {
      if (dictionary.TryGetValue(key, out var result)) {
        return result;
      }

      return createValue();
    }

    public static Action<T> Concat<T>(Action<T> first, Action<T> second) {
      return v => {
        first(v);
        second(v);
      };
    }

    public static V AddOrUpdate<K, V>(this IDictionary<K, V> dictionary, K key, V newValue, Func<V, V, V> update) {
      if (dictionary.TryGetValue(key, out var existingValue)) {
        var updated = update(existingValue, newValue);
        dictionary[key] = updated;
        return updated;
      }

      dictionary[key] = newValue;
      return newValue;
    }

    public static V GetOrCreate<K, V>(this IDictionary<K, V> dictionary, K key, Func<V> createValue) {
      if (dictionary.TryGetValue(key, out var result)) {
        return result;
      }

      result = createValue();
      dictionary[key] = result;
      return result;
    }

  }

  public class IEnumerableComparer<T> : IEqualityComparer<IEnumerable<T>> {
    public bool Equals(IEnumerable<T> x, IEnumerable<T> y) {
      return x.SequenceEqual(y);
    }

    public int GetHashCode(IEnumerable<T> obj) {
      var hash = new HashCode();
      foreach (T t in obj) {
        hash.Add(t);
      }
      return hash.ToHashCode();
    }
  }

}
