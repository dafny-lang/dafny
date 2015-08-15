#define DEBUG_AUTO_TRIGGERS

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.Triggers {
  class TriggerUtils {
    internal static List<T> CopyAndAdd<T>(List<T> seq, T elem) {
      var copy = new List<T>(seq);
      copy.Add(elem);
      return copy;
    }

    internal static IEnumerable<List<T>> AllSubsets<T>(IList<T> source, Func<List<T>, T, bool> predicate, int offset) {
      if (offset >= source.Count) {
        yield return new List<T>();
        yield break;
      }

      foreach (var subset in AllSubsets<T>(source, predicate, offset + 1)) {
        if (predicate(subset, source[offset])) {
          yield return CopyAndAdd(subset, source[offset]);
        }
        yield return new List<T>(subset);
      }
    }

    internal static IEnumerable<List<T>> AllNonEmptySubsets<T>(IEnumerable<T> source, Func<List<T>, T, bool> predicate) {
      List<T> all = new List<T>(source);
      foreach (var subset in AllSubsets(all, predicate, 0)) {
        if (subset.Count > 0) {
          yield return subset;
        }
      }
    }

    internal static List<T> MergeAlterFirst<T>(List<T> a, List<T> b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      a.AddRange(b);
      return a;
    }

    internal static ISet<T> MergeAlterFirst<T>(ISet<T> a, ISet<T> b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      a.UnionWith(b);
      return a;
    }

    internal static bool SameLists<T>(IEnumerable<T> list1, IEnumerable<T> list2, Func<T, T, bool> comparer) {
      if (ReferenceEquals(list1, list2)) {
        return true;
      } else if ((list1 == null) != (list2 == null)) {
        return false;
      }

      var it1 = list1.GetEnumerator();
      var it2 = list2.GetEnumerator();
      bool it1_has, it2_has;
      bool acc = true;

      do {
        it1_has = it1.MoveNext();
        it2_has = it2.MoveNext();

        if (it1_has == true && it2_has == true) {
          acc = acc && comparer(it1.Current, it2.Current);
        }
      } while (it1_has && it2_has);

      return it1_has == it2_has && acc;
    }

    internal static IEnumerable<T> Filter<T>(IEnumerable<T> elements, Func<T, bool> predicate, Action<T> reject) {
      var positive = new List<T>();
      foreach (var c in elements) {
        if (predicate(c)) {
          yield return c;
        } else {
          reject(c);
        }
      }
    }

    internal static bool SameNullity<T>(T x1, T x2) where T : class {
      return (x1 == null) == (x2 == null);
    }

    internal string JoinStringsWithHeader(string header, IEnumerable<string> lines) {
      return header + String.Join(Environment.NewLine + new String(' ', header.Length), lines);
    }

    [Conditional("DEBUG_AUTO_TRIGGERS")]
    internal static void DebugTriggers(string format, params object[] more) {
      Console.Error.WriteLine(format, more);
    }

    internal static bool NeedsAutoTriggers(QuantifierExpr quantifier) {
      Contract.Requires(quantifier.SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
      return quantifier.Attributes.AsEnumerable().All(aa => aa.Name != "trigger" && aa.Name != "no_trigger");
    }
  }
}
