using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;

using Microsoft.Boogie;


namespace Microsoft.Dafny {
  public class Util
  {
    public static string Comma(IEnumerable<string> l) {
      return Comma(l, s => s);
    }

    public static string Comma<T>(IEnumerable<T> l, Func<T, string> f) {
      return Comma(",", l, f);
    }

    public static string Comma<T>(string comma, IEnumerable<T> l, Func<T,string> f) {
      Contract.Requires(comma != null);
      string res = "";
      string c = "";
      foreach(var t in l) {
        res += c + f(t);
        c = comma;
      }
      return res;
    }

    public static string Comma(int count, Func<int, string> f) {
      Contract.Requires(0 <= count);
      return Comma(",", count, f);
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

    public static string Repeat(string str, int times) {
      Contract.Requires(times >= 0);
      Contract.Requires(str != null);

      var ans = "";
      for (var i = 0; i < times; i++) {
        ans += str;
      }
      return ans;
    }

    public static List<B> Map<A, B>(IEnumerable<A> xs, Func<A, B> f)
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
              case '0': special = '\0'; break;
              case 'n': special = '\n'; break;
              case 'r': special = '\r'; break;
              case 't': special = '\t'; break;
              case 'u':
                int ch = HexValue(p[i + 2]);
                ch = 16 * ch + HexValue(p[i + 3]);
                ch = 16 * ch + HexValue(p[i + 4]);
                ch = 16 * ch + HexValue(p[i + 5]);
                yield return (char)ch;
                i += 6;
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
          errors.Deprecated(fe.E.tok, "Dafny's constructors no longer need 'this' to be listed in modifies clauses");
          return;
        } else if (fe.E is SetDisplayExpr) {
          var s = (SetDisplayExpr)fe.E;
          var deprecated = s.Elements.FindAll(e => e is ThisExpr);
          if (deprecated.Count != 0) {
            foreach (var e in deprecated) {
              errors.Deprecated(e.tok, "Dafny's constructors no longer need 'this' to be listed in modifies clauses");
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
          if (decl is ClassDecl) {
            var c = (ClassDecl)decl;
            foreach (var member in c.Members) {
              if (member is Function) {
                var f = (Function)member;

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
        Console.Write("{0},{1}=", func.CompileName, func.EnclosingClass.Module.CompileName);
        foreach (var callee in vertex.Successors) {
          Console.Write("{0} ", callee.N.CompileName);
        }
        Console.Write("\n");
      }
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

  public class DependencyMap
  {
    private Dictionary<string, SortedSet<string>> dependencies;

    public DependencyMap() {
      dependencies = new Dictionary<string, SortedSet<string>>();
    }

    public void AddInclude(Include include) {
      SortedSet<string> existingDependencies = null;
      string key = include.includerFilename == null ? "roots" : include.includerFilename;
      bool found = dependencies.TryGetValue(key, out existingDependencies);
      if (found) {
        existingDependencies.Add(include.includedFullPath);
      } else {
        dependencies[key] = new SortedSet<string>() { include.includedFullPath };
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
}
