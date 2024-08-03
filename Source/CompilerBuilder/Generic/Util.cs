// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public static class Sets {
    public static ISet<T> Empty<T>() {
      return new HashSet<T>();
    }
  }

  public static class Util {

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


  class IEnumerableComparer<T> : IEqualityComparer<IEnumerable<T>> {
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
