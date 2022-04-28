// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.ComponentModel.Design.Serialization;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny.Triggers;


namespace Microsoft.Dafny {
  public static class Util {

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
        Console.Write("{0},{1}=", func.SanitizedName, func.EnclosingClass.EnclosingModuleDefinition.SanitizedName);
        foreach (var callee in vertex.Successors) {
          Console.Write("{0} ", callee.N.SanitizedName);
        }
        Console.Write("\n");
      }
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
      string key = include.includerFilename == null ? "roots" : include.includerFilename;
      bool found = dependencies.TryGetValue(key, out existingDependencies);
      if (found) {
        existingDependencies.Add(include.canonicalPath);
      } else {
        dependencies[key] = new SortedSet<string>() { include.canonicalPath };
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

  public class ExpressionTester {
    private bool reportErrors = false;
    private ErrorReporter reporter = null;
    private Resolver resolver = null;

    public ExpressionTester(Resolver resolver = null, bool reportErrors = false) :
      this(resolver, resolver?.Reporter, reportErrors) {
    }

    public ExpressionTester(Resolver resolver, ErrorReporter reporter, bool reportErrors = false) {
      Contract.Requires(reportErrors == false || resolver != null);
      this.resolver = resolver;
      this.reporter = reporter;
      this.reportErrors = reportErrors;
    }

    // Static call to CheckIsCompilable
    public static bool CheckIsCompilable(Resolver resolver, Expression expr, ICodeContext codeContext) {
      return new ExpressionTester(resolver, resolver != null).CheckIsCompilable(expr, codeContext);
    }
    // Static call to CheckIsCompilable
    public static bool CheckIsCompilable(Resolver resolver, ErrorReporter reporter, Expression expr, ICodeContext codeContext) {
      return new ExpressionTester(resolver, reporter, resolver != null).CheckIsCompilable(expr, codeContext);
    }

    /// <summary>
    /// Try to make "expr" compilable (in particular, mark LHSs of a let-expression as ghosts if
    /// the corresponding RHS is ghost), and then report errors for every part that would prevent
    /// compilation.
    /// Requires "expr" to have been successfully resolved.
    /// </summary>
    private bool CheckIsCompilable(Expression expr, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved
      Contract.Requires(codeContext != null || reporter == null);

      var isCompilable = true;

      if (expr is IdentifierExpr expression) {
        if (expression.Var != null && expression.Var.IsGhost) {
          reporter?.Error(MessageSource.Resolver, expression, "ghost variables are allowed only in specification contexts");
          return false;
        }

      } else if (expr is MemberSelectExpr selectExpr) {
        if (selectExpr.Member != null && selectExpr.Member.IsGhost) {
          reporter?.Error(MessageSource.Resolver, selectExpr, "ghost fields are allowed only in specification contexts");
          return false;
        }

      } else if (expr is FunctionCallExpr callExpr) {
        if (callExpr.Function != null) {
          if (callExpr.Function.IsGhost) {
            if (reportErrors == false) {
              return false;
            }

            string msg;
            if (callExpr.Function is TwoStateFunction || callExpr.Function is ExtremePredicate || callExpr.Function is PrefixPredicate) {
              msg = $"a call to a {callExpr.Function.WhatKind} is allowed only in specification contexts";
            } else {
              var what = callExpr.Function.WhatKind;
              string compiledDeclHint;
              if (DafnyOptions.O.FunctionSyntax == DafnyOptions.FunctionSyntaxOptions.Version4) {
                compiledDeclHint = "without the 'ghost' keyword";
              } else {
                compiledDeclHint = $"with '{what} method'";
              }
              msg = $"a call to a ghost {what} is allowed only in specification contexts (consider declaring the {what} {compiledDeclHint})";
            }
            reporter?.Error(MessageSource.Resolver, callExpr, msg);
            return false;
          }
          if (callExpr.Function.ByMethodBody != null) {
            Contract.Assert(callExpr.Function.ByMethodDecl != null); // we expect .ByMethodDecl to have been filled in by now
            // this call will really go to the method part of the function-by-method, so add that edge to the call graph
            resolver?.AddCallGraphEdge(codeContext, callExpr.Function.ByMethodDecl, callExpr, false);
            callExpr.IsByMethodCall = true;
          }
          // function is okay, so check all NON-ghost arguments
          isCompilable = CheckIsCompilable(callExpr.Receiver, codeContext);
          for (var i = 0; i < callExpr.Function.Formals.Count; i++) {
            if (!callExpr.Function.Formals[i].IsGhost) {
              isCompilable = CheckIsCompilable(callExpr.Args[i], codeContext) && isCompilable;
            }
          }
        }

        return isCompilable;

      } else if (expr is DatatypeValue value) {
        // check all NON-ghost arguments
        // note that if resolution is successful, then |e.Arguments| == |e.Ctor.Formals|
        for (int i = 0; i < value.Arguments.Count; i++) {
          if (!value.Ctor.Formals[i].IsGhost) {
            isCompilable = CheckIsCompilable(value.Arguments[i], codeContext) && isCompilable;
          }
        }
        return isCompilable;

      } else if (expr is OldExpr) {
        reporter?.Error(MessageSource.Resolver, expr, "old expressions are allowed only in specification and ghost contexts");
        return false;

      } else if (expr is TypeTestExpr tte) {
        if (!IsTypeTestCompilable(tte)) {
          reporter?.Error(MessageSource.Resolver, tte, $"an expression of type '{tte.E.Type}' is not run-time checkable to be a '{tte.ToType}'");
          return false;
        }

      } else if (expr is FreshExpr) {
        reporter?.Error(MessageSource.Resolver, expr, "fresh expressions are allowed only in specification and ghost contexts");
        return false;

      } else if (expr is UnchangedExpr) {
        reporter?.Error(MessageSource.Resolver, expr, "unchanged expressions are allowed only in specification and ghost contexts");
        return false;

      } else if (expr is StmtExpr stmtExpr) {
        // ignore the statement
        return CheckIsCompilable(stmtExpr.E, codeContext);

      } else if (expr is BinaryExpr binaryExpr) {
        switch (binaryExpr.ResolvedOp_PossiblyStillUndetermined) {
          case BinaryExpr.ResolvedOpcode.RankGt:
          case BinaryExpr.ResolvedOpcode.RankLt:
            reporter?.Error(MessageSource.Resolver, binaryExpr, "rank comparisons are allowed only in specification and ghost contexts");
            return false;
        }
      } else if (expr is TernaryExpr ternaryExpr) {
        switch (ternaryExpr.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            reporter?.Error(MessageSource.Resolver, ternaryExpr, "prefix equalities are allowed only in specification and ghost contexts");
            return false;
        }
      } else if (expr is LetExpr letExpr) {
        if (letExpr.Exact) {
          Contract.Assert(letExpr.LHSs.Count == letExpr.RHSs.Count);
          var i = 0;
          foreach (var ee in letExpr.RHSs) {
            var lhs = letExpr.LHSs[i];
            // Make LHS vars ghost if the RHS is a ghost
            if (UsesSpecFeatures(ee)) {
              foreach (var bv in lhs.Vars) {
                if (!bv.IsGhost) {
                  bv.MakeGhost();
                  isCompilable = false;
                }
              }
            }

            if (!lhs.Vars.All(bv => bv.IsGhost)) {
              isCompilable = CheckIsCompilable(ee, codeContext) && isCompilable;
            }
            i++;
          }
          isCompilable = CheckIsCompilable(letExpr.Body, codeContext) && isCompilable;
        } else {
          Contract.Assert(letExpr.RHSs.Count == 1);
          var lhsVarsAreAllGhost = letExpr.BoundVars.All(bv => bv.IsGhost);
          if (!lhsVarsAreAllGhost) {
            isCompilable = CheckIsCompilable(letExpr.RHSs[0], codeContext) && isCompilable;
          }
          isCompilable = CheckIsCompilable(letExpr.Body, codeContext) && isCompilable;

          // fill in bounds for this to-be-compiled let-such-that expression
          Contract.Assert(letExpr.RHSs.Count == 1);  // if we got this far, the resolver will have checked this condition successfully
          var constraint = letExpr.RHSs[0];
          if (resolver != null) {
            letExpr.Constraint_Bounds = Resolver.DiscoverBestBounds_MultipleVars(letExpr.BoundVars.ToList<IVariable>(),
              constraint, true, ComprehensionExpr.BoundedPool.PoolVirtues.None);
          }
        }
        return isCompilable;
      } else if (expr is LambdaExpr lambdaExpr) {
        return CheckIsCompilable(lambdaExpr.Body, codeContext);
      } else if (expr is ComprehensionExpr comprehensionExpr) {
        var uncompilableBoundVars = comprehensionExpr.UncompilableBoundVars();
        if (uncompilableBoundVars.Count != 0) {
          if (reportErrors == false) {
            return false;
          }

          string what;
          if (comprehensionExpr is SetComprehension comprehension) {
            what = comprehension.Finite ? "set comprehensions" : "iset comprehensions";
          } else if (comprehensionExpr is MapComprehension mapComprehension) {
            what = mapComprehension.Finite ? "map comprehensions" : "imap comprehensions";
          } else {
            Contract.Assume(comprehensionExpr is QuantifierExpr);  // otherwise, unexpected ComprehensionExpr (since LambdaExpr is handled separately above)
            Contract.Assert(((QuantifierExpr)comprehensionExpr).SplitQuantifier == null); // No split quantifiers during resolution
            what = "quantifiers";
          }
          foreach (var bv in uncompilableBoundVars) {
            reporter.Error(MessageSource.Resolver, comprehensionExpr, "{0} in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{1}'", what, bv.Name);
          }
          return false;
        }
        // don't recurse down any attributes
        if (comprehensionExpr.Range != null) {
          isCompilable = CheckIsCompilable(comprehensionExpr.Range, codeContext) && isCompilable;
        }
        isCompilable = CheckIsCompilable(comprehensionExpr.Term, codeContext) && isCompilable;
        return isCompilable;

      } else if (expr is ChainingExpression chainingExpression) {
        // We don't care about the different operators; we only want the operands, so let's get them directly from
        // the chaining expression
        return chainingExpression.Operands.TrueForAll(ee => CheckIsCompilable(ee, codeContext));
      }

      foreach (var ee in expr.SubExpressions) {
        isCompilable = CheckIsCompilable(ee, codeContext) && isCompilable;
      }

      return isCompilable;
    }


    public static bool IsTypeTestCompilable(TypeTestExpr tte) {
      Contract.Requires(tte != null);
      var fromType = tte.E.Type;
      if (fromType.IsSubtypeOf(tte.ToType, false, true)) {
        // this is a no-op, so it can trivially be compiled
        return true;
      }

      // TODO: It would be nice to allow some subset types in test tests in compiled code. But for now, such cases
      // are allowed only in ghost contexts.
      var udtTo = (UserDefinedType)tte.ToType.NormalizeExpandKeepConstraints();
      if (udtTo.ResolvedClass is SubsetTypeDecl && !(udtTo.ResolvedClass is NonNullTypeDecl)) {
        return false;
      }

      // The operation can be performed at run time if the mapping of .ToType's type parameters are injective in fromType's type parameters.
      // For illustration, suppose the "is"-operation is testing whether or not the given expression of type A<X> has type B<Y>, where
      // X and Y are some type expressions. At run time, we can check if the expression has type B<...>, but we can't on all target platforms
      // be certain about the "...". So, if both B<Y> and B<Y'> are possible subtypes of A<X>, we can't perform the type test at run time.
      // In other words, we CAN perform the type test at run time if the type parameters of A uniquely determine the type parameters of B.
      // Let T be a list of type parameters (in particular, we will use the formal TypeParameter's declared in type B). Then, represent
      // B<T> in parent type A, and let's say the result is A<U> for some type expression U. If U contains all type parameters from T,
      // then the mapping from B<T> to A<U> is unique, which means the mapping frmo B<Y> to A<X> is unique, which means we can check if an
      // A<X> value is a B<Y> value by checking if the value is of type B<...>.
      var B = ((UserDefinedType)tte.ToType.NormalizeExpandKeepConstraints()).ResolvedClass; // important to keep constraints here, so no type parameters are lost
      var B_T = UserDefinedType.FromTopLevelDecl(tte.tok, B);
      var tps = new HashSet<TypeParameter>(); // There are going to be the type parameters of fromType (that is, T in the discussion above)
      if (fromType.TypeArgs.Count != 0) {
        // we need this "if" statement, because if "fromType" is "object" or "object?", then it isn't a UserDefinedType
        var A = (UserDefinedType)fromType.NormalizeExpand(); // important to NOT keep constraints here, since they won't be evident at run time
        var A_U = B_T.AsParentType(A.ResolvedClass);
        // the type test can be performed at run time if all the type parameters of "B_T" are free type parameters of "A_U".
        A_U.AddFreeTypeParameters(tps);
      }
      foreach (var tp in B.TypeArgs) {
        if (!tps.Contains(tp)) {
          // type test cannot be performed at run time, so this is a ghost operation
          // TODO: If "tp" is a type parameter for which there is a run-time type descriptor, then we would still be able to perform
          // the type test at run time.
          return false;
        }
      }
      // type test can be performed at run time
      return true;
    }

    /// <summary>
    /// Returns whether or not 'expr' has any subexpression that uses some feature (like a ghost or quantifier)
    /// that is allowed only in specification contexts.
    /// Requires 'expr' to be a successfully resolved expression.
    /// </summary>
    public static bool UsesSpecFeatures(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved

      if (expr is LiteralExpr) {
        return false;
      } else if (expr is ThisExpr) {
        return false;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        return cce.NonNull(e.Var).IsGhost;
      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        // check all NON-ghost arguments
        // note that if resolution is successful, then |e.Arguments| == |e.Ctor.Formals|
        for (int i = 0; i < e.Arguments.Count; i++) {
          if (!e.Ctor.Formals[i].IsGhost && UsesSpecFeatures(e.Arguments[i])) {
            return true;
          }
        }
        return false;
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        return e.Elements.Exists(ee => UsesSpecFeatures(ee));
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        return e.Elements.Exists(p => UsesSpecFeatures(p.A) || UsesSpecFeatures(p.B));
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        if (e.Member != null) {
          return cce.NonNull(e.Member).IsGhost || UsesSpecFeatures(e.Obj);
        } else {
          return false;
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        return UsesSpecFeatures(e.Seq) ||
               (e.E0 != null && UsesSpecFeatures(e.E0)) ||
               (e.E1 != null && UsesSpecFeatures(e.E1));
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        return UsesSpecFeatures(e.Array) || e.Indices.Exists(ee => UsesSpecFeatures(ee));
      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        return UsesSpecFeatures(e.Seq) ||
               UsesSpecFeatures(e.Index) ||
               UsesSpecFeatures(e.Value);
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (e.Function.IsGhost) {
          return true;
        }
        // check all NON-ghost arguments
        if (UsesSpecFeatures(e.Receiver)) {
          return true;
        }
        for (int i = 0; i < e.Function.Formals.Count; i++) {
          if (!e.Function.Formals[i].IsGhost && UsesSpecFeatures(e.Args[i])) {
            return true;
          }
        }
        return false;
      } else if (expr is ApplyExpr) {
        ApplyExpr e = (ApplyExpr)expr;
        return UsesSpecFeatures(e.Function) || e.Args.Exists(UsesSpecFeatures);
      } else if (expr is OldExpr || expr is UnchangedExpr) {
        return true;
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        if (e is UnaryOpExpr unaryOpExpr && (unaryOpExpr.Op == UnaryOpExpr.Opcode.Fresh || unaryOpExpr.Op == UnaryOpExpr.Opcode.Allocated)) {
          return true;
        }
        if (expr is TypeTestExpr tte && !IsTypeTestCompilable(tte)) {
          return true;
        }
        return UsesSpecFeatures(e.E);
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        switch (e.ResolvedOp_PossiblyStillUndetermined) {
          case BinaryExpr.ResolvedOpcode.RankGt:
          case BinaryExpr.ResolvedOpcode.RankLt:
            return true;
          default:
            return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1);
        }
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            return true;
          default:
            break;
        }
        return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1) || UsesSpecFeatures(e.E2);
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          MakeGhostAsNeeded(e.LHSs);
          return UsesSpecFeatures(e.Body);
        } else {
          Contract.Assert(e.RHSs.Count == 1);
          if (UsesSpecFeatures(e.RHSs[0])) {
            foreach (var bv in e.BoundVars) {
              bv.MakeGhost();
            }
          }
          return UsesSpecFeatures(e.Body);
        }
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        return e.UncompilableBoundVars().Count != 0 || UsesSpecFeatures(e.LogicalBody());
      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        return !e.Finite || e.UncompilableBoundVars().Count != 0 || (e.Range != null && UsesSpecFeatures(e.Range)) || (e.Term != null && UsesSpecFeatures(e.Term));
      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        return !e.Finite || e.UncompilableBoundVars().Count != 0 || UsesSpecFeatures(e.Range) || (e.TermLeft != null && UsesSpecFeatures(e.TermLeft)) || UsesSpecFeatures(e.Term);
      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        return UsesSpecFeatures(e.Term);
      } else if (expr is WildcardExpr) {
        return false;
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return UsesSpecFeatures(e.E);
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        return UsesSpecFeatures(e.Test) || UsesSpecFeatures(e.Thn) || UsesSpecFeatures(e.Els);
      } else if (expr is NestedMatchExpr) {
        return UsesSpecFeatures(((NestedMatchExpr)expr).ResolvedExpression);
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        if (UsesSpecFeatures(me.Source)) {
          return true;
        }
        return me.Cases.Exists(mc => UsesSpecFeatures(mc.Body));
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return e.ResolvedExpression != null && UsesSpecFeatures(e.ResolvedExpression);
      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        return UsesSpecFeatures(e.N) || UsesSpecFeatures(e.Initializer);
      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return UsesSpecFeatures(e.E);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }
    static void MakeGhostAsNeeded(List<CasePattern<BoundVar>> lhss) {
      foreach (CasePattern<BoundVar> lhs in lhss) {
        MakeGhostAsNeeded(lhs);
      }
    }

    static void MakeGhostAsNeeded(CasePattern<BoundVar> lhs) {
      if (lhs.Ctor != null && lhs.Arguments != null) {
        for (int i = 0; i < lhs.Arguments.Count && i < lhs.Ctor.Destructors.Count; i++) {
          MakeGhostAsNeeded(lhs.Arguments[i], lhs.Ctor.Destructors[i]);
        }
      }
    }

    static void MakeGhostAsNeeded(CasePattern<BoundVar> arg, DatatypeDestructor d) {
      if (arg.Expr is IdentifierExpr ie && ie.Var is BoundVar bv) {
        if (d.IsGhost) {
          bv.MakeGhost();
        }
      }
      if (arg.Ctor != null) {
        MakeGhostAsNeeded(arg);
      }
    }
  }
}
