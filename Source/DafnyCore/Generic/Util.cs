// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.Reactive.Disposables;
using System.Reactive.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public static class Util {

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

    public static string Comma(this IEnumerable<string> l) {
      return Comma(l, s => s);
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
      return Dict<A, B>(LinqExtender.Zip(xs, ys));
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

    public static void ValidateEscaping(DafnyOptions options, IToken t, string s, bool isVerbatimString, Errors errors) {
      if (options.Get(CommonOptionBag.UnicodeCharacters)) {
        foreach (var token in TokensWithEscapes(s, isVerbatimString)) {
          if (token.StartsWith("\\u")) {
            errors.SemErr(t, "\\u escape sequences are not permitted when Unicode chars are enabled");
          }

          if (token.StartsWith("\\U")) {
            var hexDigits = RemoveUnderscores(token[3..^1]);
            if (hexDigits.Length > 6) {
              errors.SemErr(t, "\\U{X..X} escape sequence must have at most six hex digits");
            } else {
              var codePoint = Convert.ToInt32(hexDigits, 16);
              if (codePoint >= 0x11_0000) {
                errors.SemErr(t, "\\U{X..X} escape sequence must be less than 0x110000");
              }
              if (codePoint is >= 0xD800 and < 0xE000) {
                errors.SemErr(t, "\\U{X..X} escape sequence must not be a surrogate");
              }
            }
          }
        }
      } else {
        foreach (var token2 in TokensWithEscapes(s, isVerbatimString)) {
          if (token2.StartsWith("\\U")) {
            errors.SemErr(t, "\\U escape sequences are not permitted when Unicode chars are disabled");
          }
        }
      }
    }

    public static bool MightContainNonAsciiCharacters(string s, bool isVerbatimString) {
      // This is conservative since \u and \U escapes could be ASCII characters,
      // but that's fine since this method is just used as a conservative guard.
      return TokensWithEscapes(s, isVerbatimString).Any(e =>
        e.Any(c => !char.IsAscii(c)) || e.StartsWith(@"\u") || e.StartsWith(@"\U"));
    }

    /// <summary>
    /// Replaced any escaped characters in s by the actual character that the escaping represents.
    /// Assumes s to be a well-parsed string.
    /// </summary>
    public static string RemoveEscaping(DafnyOptions options, string s, bool isVerbatimString) {
      Contract.Requires(s != null);
      var sb = new StringBuilder();
      if (options.Get(CommonOptionBag.UnicodeCharacters)) {
        UnescapedCharacters(options, s, isVerbatimString).Iter(ch => sb.Append(new Rune(ch)));
      } else {
        UnescapedCharacters(options, s, isVerbatimString).Iter(ch => sb.Append((char)ch));
      }
      return sb.ToString();
    }

    public static readonly Regex Utf16Escape = new Regex(@"\\u([0-9a-fA-F]{4})");
    public static readonly Regex UnicodeEscape = new Regex(@"\\U\{([0-9a-fA-F_]+)\}");
    private static readonly Regex NullEscape = new Regex(@"\\0");

    private static string ToUtf16Escape(char c) {
      return $"\\u{(int)c:x4}";
    }

    public static string ReplaceTokensWithEscapes(string s, Regex pattern, MatchEvaluator evaluator) {
      return string.Join("",
        TokensWithEscapes(s, false)
          .Select(token => pattern.Replace(token, evaluator)));
    }

    public static string ExpandUnicodeEscapes(string s, bool lowerCaseU) {
      return ReplaceTokensWithEscapes(s, UnicodeEscape, match => {
        var hexDigits = RemoveUnderscores(match.Groups[1].Value);
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

    public static string ReplaceNullEscapesWithCharacterEscapes(string s) {
      return ReplaceTokensWithEscapes(s, NullEscape, match => "\\u0000");
    }

    /// <summary>
    /// Returns the characters of the well-parsed string p, replacing any
    /// escaped characters by the actual characters.
    /// 
    /// It also converts surrogate pairs to their equivalent code points
    /// if --unicode-char is enabled - these are synthesized by the parser when
    /// reading the original UTF-8 source, but don't represent the true character values.
    /// </summary>
    public static IEnumerable<int> UnescapedCharacters(DafnyOptions options, string p, bool isVerbatimString) {
      var unicodeChars = options.Get(CommonOptionBag.UnicodeCharacters);
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

    /// <summary>
    /// Add "fe" to "mod", if "performThisDeprecationCheck" is "false".
    /// Otherwise, first strip "fe" of certain easy occurrences of "this", and for each one giving a warning about
    /// that "this" is deprecated in modifies clauses of constructors.
    /// This method may modify "fe" and the subexpressions contained within "fe".
    /// </summary>
    public static void AddFrameExpression(List<FrameExpression> mod, FrameExpression fe, bool performThisDeprecationCheck, Errors errors) {
      Contract.Requires(mod != null);
      Contract.Requires(fe != null);
      Contract.Requires(errors != null);
      if (performThisDeprecationCheck) {
        if (fe.E is ThisExpr) {
          errors.Deprecated(fe.E.tok, "constructors no longer need 'this' to be listed in modifies clauses");
          return;
        } else if (fe.E is SetDisplayExpr) {
          var s = (SetDisplayExpr)fe.E;
          var deprecated = s.Elements.FindAll(e => e is ThisExpr);
          if (deprecated.Count != 0) {
            foreach (var e in deprecated) {
              errors.Deprecated(e.tok, "constructors no longer need 'this' to be listed in modifies clauses");
            }
            s.Elements.RemoveAll(e => e is ThisExpr);
            if (s.Elements.Count == 0) {
              return;
            }
          }
        }
      }
      mod.Add(fe);
    }

    /// <summary>
    /// Class dedicated to traversing the function call graph
    /// </summary>
    class FunctionCallFinder : TopDownVisitor<List<Function>> {
      protected override bool VisitOneExpr(Expression expr, ref List<Function> calls) {
        if (expr is FunctionCallExpr) {
          calls.Add(((FunctionCallExpr)expr).Function);
        }
        return true;
      }
    }

    static Graph<Function> BuildFunctionCallGraph(Dafny.Program program) {
      Graph<Function> functionCallGraph = new Graph<Function>();
      FunctionCallFinder callFinder = new FunctionCallFinder();

      foreach (var module in program.Modules()) {
        foreach (var decl in module.TopLevelDecls) {
          if (decl is TopLevelDeclWithMembers c) {
            foreach (var member in c.Members) {
              if (member is Function f) {
                List<Function> calls = new List<Function>();
                foreach (var e in f.Reads) { if (e != null && e.E != null) { callFinder.Visit(e.E, calls); } }
                foreach (var e in f.Req) { if (e != null) { callFinder.Visit(e, calls); } }
                foreach (var e in f.Ens) { if (e != null) { callFinder.Visit(e, calls); } }
                if (f.Body != null) {
                  callFinder.Visit(f.Body, calls);
                }

                foreach (var callee in calls) {
                  functionCallGraph.AddEdge(f, callee);
                }
              }
            }
          }
        }
      }

      return functionCallGraph;
    }

    /// <summary>
    /// Prints the program's function call graph in a format suitable for consumption in other tools
    /// </summary>
    public static void PrintFunctionCallGraph(Dafny.Program program) {
      var functionCallGraph = BuildFunctionCallGraph(program);

      foreach (var vertex in functionCallGraph.GetVertices()) {
        var func = vertex.N;
        Console.Write("{0},{1}=", func.SanitizedName, func.EnclosingClass.EnclosingModuleDefinition.SanitizedName);
        foreach (var callee in vertex.Successors) {
          Console.Write("{0} ", callee.N.SanitizedName);
        }
        Console.Write("\n");
      }
    }

    public static V GetOrDefault<K, V, V2>(this IReadOnlyDictionary<K, V2> dictionary, K key, Func<V> createValue)
      where V2 : V {
      if (dictionary.TryGetValue(key, out var result)) {
        return result;
      }

      return createValue();
    }

    public static V GetOrCreate<K, V>(this IDictionary<K, V> dictionary, K key, Func<V> createValue) {
      if (dictionary.TryGetValue(key, out var result)) {
        return result;
      }

      result = createValue();
      dictionary[key] = result;
      return result;
    }

    /// <summary>
    /// Generic statistic counter
    /// </summary>
    static void IncrementStat(IDictionary<string, ulong> stats, string stat) {
      ulong currentValue;
      if (stats.TryGetValue(stat, out currentValue)) {
        stats[stat] += 1;
      } else {
        stats.Add(stat, 1);
      }
    }

    /// <summary>
    /// Track the maximum value of some statistic
    /// </summary>
    static void UpdateMax(IDictionary<string, ulong> stats, string stat, ulong val) {
      ulong currentValue;
      if (stats.TryGetValue(stat, out currentValue)) {
        if (val > currentValue) {
          stats[stat] = val;
        }
      } else {
        stats.Add(stat, val);
      }
    }

    /// <summary>
    /// Compute various interesting statistics about the Dafny program
    /// </summary>
    public static void PrintStats(Dafny.Program program) {
      SortedDictionary<string, ulong> stats = new SortedDictionary<string, ulong>();

      foreach (var module in program.Modules()) {
        IncrementStat(stats, "Modules");
        UpdateMax(stats, "Module height (max)", (ulong)module.Height);

        ulong num_scc = (ulong)module.CallGraph.TopologicallySortedComponents().Count;
        UpdateMax(stats, "Call graph width (max)", num_scc);

        foreach (var decl in module.TopLevelDecls) {
          if (decl is DatatypeDecl) {
            IncrementStat(stats, "Datatypes");
          } else if (decl is ClassDecl) {
            var c = (ClassDecl)decl;
            if (c.Name != "_default") {
              IncrementStat(stats, "Classes");
            }

            foreach (var member in c.Members) {
              if (member is Function) {
                IncrementStat(stats, "Functions (total)");
                var f = (Function)member;
                if (f.IsRecursive) {
                  IncrementStat(stats, "Functions recursive");
                }
              } else if (member is Method) {
                IncrementStat(stats, "Methods (total)");
                var method = (Method)member;
                if (method.IsRecursive) {
                  IncrementStat(stats, "Methods recursive");
                }
                if (method.IsGhost) {
                  IncrementStat(stats, "Methods ghost");
                }
              }
            }
          }
        }
      }

      // Print out the results, with some nice formatting
      Console.WriteLine("");
      Console.WriteLine("Statistics");
      Console.WriteLine("----------");

      int max_key_length = 0;
      foreach (var key in stats.Keys) {
        if (key.Length > max_key_length) {
          max_key_length = key.Length;
        }
      }

      foreach (var keypair in stats) {
        string keyString = keypair.Key.PadRight(max_key_length + 2);
        Console.WriteLine("{0} {1,4}", keyString, keypair.Value);
      }
    }
  }

  public class DependencyMap {
    private Dictionary<string, SortedSet<string>> dependencies;

    public DependencyMap() {
      dependencies = new Dictionary<string, SortedSet<string>>();
    }

    public void AddInclude(Include include) {
      SortedSet<string> existingDependencies = null;
      string key = include.IncluderFilename.LocalPath ?? "roots";
      bool found = dependencies.TryGetValue(key, out existingDependencies);
      if (found) {
        existingDependencies.Add(include.CanonicalPath);
      } else {
        dependencies[key] = new SortedSet<string>() { include.CanonicalPath };
      }
    }

    public void AddIncludes(IEnumerable<Include> includes) {
      // Reconstruct the dependency map
      Dictionary<string, List<string>> dependencies = new Dictionary<string, List<string>>();
      foreach (Include include in includes) {
        AddInclude(include);
      }
    }

    public void PrintMap() {
      SortedSet<string> leaves = new SortedSet<string>(); // Files that don't themselves include any files
      foreach (string target in dependencies.Keys) {
        System.Console.Write(target);
        foreach (string dependency in dependencies[target]) {
          System.Console.Write(";" + dependency);
          if (!dependencies.ContainsKey(dependency)) {
            leaves.Add(dependency);
          }
        }
        System.Console.WriteLine();
      }
      foreach (string leaf in leaves) {
        System.Console.WriteLine(leaf);
      }
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

  // Class to traverse a program top-down, especially aimed at identifying expressions and statements,
  // and in their context
  // How to use:
  // - Define a subclass of ProgramTraverser
  // - Implement the methods (TopDown|BottomUp)(Enter|Exit), override Traverse if needed.
  // - Call any Traverse() method.
  public class ProgramTraverser {
    public enum ContinuationStatus {
      Ok,    // Continue exploration
      Skip,  // Skip this node and its descendants  (valid only on entering a node)
      Stop,  // Stop the entire traversal here, but traverse ancestors in bottom-up
    }
    protected const ContinuationStatus ok = ContinuationStatus.Ok;
    protected const ContinuationStatus skip = ContinuationStatus.Skip;
    protected const ContinuationStatus stop = ContinuationStatus.Stop;
    // Returns true if statement needs to be traversed
    protected virtual ContinuationStatus OnEnter(Statement stmt, [CanBeNull] string field, [CanBeNull] object parent) {
      return ok;
    }
    // Returns true if expression needs to be traversed
    protected virtual ContinuationStatus OnEnter(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
      return ok;
    }

    // Returns true if need to stop the traversal entirely
    protected virtual bool OnExit(Statement stmt, [CanBeNull] string field, [CanBeNull] object parent) {
      return false;
    }
    // Returns true if need to stop the traversal entirely
    protected virtual bool OnExit(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
      return false;
    }

    protected virtual ContinuationStatus OnEnter(MemberDecl memberDecl, [CanBeNull] string field, [CanBeNull] object parent) {
      return ok;
    }

    // Traverse methods retun true to interrupt.
    public bool Traverse(Program program) {
      if (program == null) {
        return false;
      }

      return program.Modules().Any(Traverse);
    }

    public bool Traverse(ModuleDefinition moduleDefinition) {
      if (moduleDefinition == null) {
        return false;
      }

      return Traverse(moduleDefinition.TopLevelDecls);
    }

    public bool Traverse(List<TopLevelDecl> topLevelDecls) {
      if (topLevelDecls == null) {
        return false;
      }

      foreach (var topLevelDecl in topLevelDecls) {
        if (Traverse(topLevelDecl)) {
          return true;
        }
      }

      return false;
    }

    public bool Traverse(ModuleDecl moduleDecl) {
      if (moduleDecl == null) {
        return false;
      }

      if (moduleDecl is LiteralModuleDecl l) {
        return Traverse(l.ModuleDef);
      } else if (moduleDecl is AbstractModuleDecl a) {
        return Traverse(a.CompileRoot);
      }/* else if (moduleDecl is AliasModuleDecl a) {
        
      } else if (moduleDecl is ModuleExportDecl m) {
        
      }*/

      return false;
    }

    public bool Traverse(Formal formal) {
      if (formal == null) {
        return false;
      }

      if (formal.DefaultValue != null && Traverse(formal.DefaultValue, "DefaultValue", formal)) {
        return true;
      }

      return false;
    }

    public bool Traverse(DatatypeCtor ctor) {
      if (ctor == null) {
        return false;
      }

      if (ctor.Formals.Any(Traverse)) {
        return true;
      }

      return false;
    }

    public bool Traverse(TopLevelDecl topd) {
      if (topd == null) {
        return false;
      }

      var d = topd is ClassDecl classDecl && classDecl.NonNullTypeDecl != null ? classDecl.NonNullTypeDecl : topd;

      if (d is TopLevelDeclWithMembers tdm) {
        // ClassDecl, DatatypeDecl, OpaqueTypeDecl, NewtypeDecl 
        if (tdm.Members.Any(memberDecl => Traverse(memberDecl, "Members", tdm))) {
          return true;
        }

        if (tdm is IteratorDecl iter) {
          // TODO: Import this
          if (Attributes.SubExpressions(iter.Attributes).Any(e => Traverse(e, "Attributes.SubExpressions", iter))) {
            return true;
          }
          if (Attributes.SubExpressions(iter.Reads.Attributes).Any(e => Traverse(e, "Reads.Attributes.SubExpressions", iter))) {
            return true;
          }
          if (iter.Reads.Expressions.Any(e => Traverse(e.E, "Reads.Expressions.E", iter))) {
            return true;
          }
          if (Attributes.SubExpressions(iter.Modifies.Attributes).Any(e => Traverse(e, "Modifies.Attributes.SubExpressions", iter))) {
            return true;
          }
          if (iter.Modifies.Expressions.Any(e => Traverse(e.E, "Modifies.Expressions.E", iter))) {
            return true;
          }
          if (Attributes.SubExpressions(iter.Decreases.Attributes).Any(e => Traverse(e, "Decreases.Attributes.SubExpressions", iter))) {
            return true;
          }
          if (iter.Decreases.Expressions.Any(e => Traverse(e, "Decreases.Expressions.E", iter))) {
            return true;
          }
          if (iter.Requires.Any(e => Traverse(e.E, "Requires.E", iter))) {
            return true;
          }
          if (iter.Ensures.Any(e => Traverse(e.E, "Ensures.E", iter))) {
            return true;
          }
          if (iter.YieldRequires.Any(e => Traverse(e.E, "YieldRequires.E", iter))) {
            return true;
          }
          if (iter.YieldEnsures.Any(e => Traverse(e.E, "YieldEnsures.E", iter))) {
            return true;
          }
          if (Traverse(iter.Body, "Body", iter)) {
            return true;
          }
        }

        if (tdm is DatatypeDecl dtd) {
          if (dtd.Ctors.Any(Traverse)) {
            return true;
          }
        }
      } else if (d is ModuleDecl md) {
        return Traverse(md);
      } else if (d is ValuetypeDecl vd) {
        if (vd.Members.Any(pair => Traverse(pair.Value, "Members.Value", vd))) {
          return true;
        }
      } else if (d is TypeSynonymDecl tsd) {
        // Nothing here.
      }

      return false;
    }

    public bool Traverse(MemberDecl memberDeclaration, [CanBeNull] string field, [CanBeNull] object parent) {
      if (memberDeclaration == null) {
        return false;
      }

      var enterResult = OnEnter(memberDeclaration, field, parent);
      if (enterResult is stop or skip) {
        return enterResult == stop;
      }

      if (memberDeclaration is Field fi) {
        if (fi.SubExpressions.Any(expr => Traverse(expr, "SubExpressions", fi))) {
          return true;
        }
      } else if (memberDeclaration is Function f) {
        if (f.Formals.Any(Traverse)) {
          return true;
        }
        if (f.Result != null && f.Result.DefaultValue != null && Traverse(f.Result.DefaultValue, "Result.DefaultValue", f)) {
          return true;
        }
        if (f.Req.Any(e => Traverse(e.E, "Req.E", f))) {
          return true;
        }
        if (f.Reads.Any(e => Traverse(e.E, "Reads.E", f))) {
          return true;
        }
        if (f.Ens.Any(e => Traverse(e.E, "Ens.E", f))) {
          return true;
        }
        if (f.Decreases.Expressions.Any(e => Traverse(e, "Decreases.Expressions", f))) {
          return true;
        }
        if (Traverse(f.Body, "Body", f)) {
          return true;
        }

        if (f.ByMethodDecl != null && Traverse(f.ByMethodDecl, "ByMethodDecl", f)) {
          return true;
        }

        if (f.ByMethodDecl == null || f.ByMethodDecl.Body != f.ByMethodBody) {
          if (f.ByMethodBody != null && Traverse(f.ByMethodBody, "ByMethodBody", f)) {
            return true;
          }
        }
      } else if (memberDeclaration is Method m) {
        // For example, default value of formals is non-ghost
        if (m.Ins.Any(formal => formal.DefaultValue != null
                                && Traverse(formal.DefaultValue, "Ins.DefaultValue", m))) {
          return true;
        }
        if (m.Req.Any(e => Traverse(e.E, "Req.E", m))) {
          return true;
        }
        if (m.Mod.Expressions.Any(e => Traverse(e.E, "Mod.E", m) == true)) {
          return true;
        }
        if (m.Ens.Any(e => Traverse(e.E, "Ens.E", m))) {
          return true;
        }
        if (m.Decreases.Expressions.Any(e => Traverse(e, "Decreases.Expressions", m))) {
          return true;
        }
        if (Traverse(m.Body, "Body", m)) {
          return true;
        }
      }

      return false;
    }

    public virtual bool Traverse(Statement stmt, [CanBeNull] string field, [CanBeNull] object parent) {
      if (stmt == null) {
        return false;
      }

      var enterResult = OnEnter(stmt, field, parent);
      if (enterResult is stop or skip) {
        return enterResult == stop;
      }

      return stmt.NonSpecificationSubExpressions.Any(subExpr => Traverse(subExpr, "NonSpecificationSubExpressions", stmt)) ||
             stmt.SpecificationSubExpressions.Any(subExpr => Traverse(subExpr, "SpecificationSubExpressions", stmt)) ||
             stmt.SubStatements.Any(subStmt => Traverse(subStmt, "SubStatements", stmt)) ||
             OnExit(stmt, field, parent);
    }

    public virtual bool Traverse(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
      if (expr == null) {
        return false;
      }

      var enterResult = OnEnter(expr, field, parent);
      if (enterResult is stop or skip) {
        return enterResult == stop;
      }

      return expr.SubExpressions.Any(subExpr => Traverse(subExpr, "SubExpression", expr)) ||
             OnExit(expr, field, parent);
    }
  }
}
