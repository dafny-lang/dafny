using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Dafny;

using static Microsoft.Dafny.GenericErrors;

namespace DafnyCore.Generic;

public static class DafnyUtils {

  public static string ExpandUnicodeEscapes(string s, bool lowerCaseU) {
    return ReplaceTokensWithEscapes(s, UnicodeEscape, match => {
      var hexDigits = Util.RemoveUnderscores(match.Groups[1].Value);
      var padChars = 8 - hexDigits.Length;
      return (lowerCaseU ? "\\u" : "\\U") + new string('0', padChars) + hexDigits;
    });
  }

  public static string UnicodeEscapesToLowercase(string s) {
    return ReplaceTokensWithEscapes(s, UnicodeEscape, match =>
      $"\\u{{{Util.RemoveUnderscores(match.Groups[1].Value)}}}");
  }

  public static string UnicodeEscapesToUtf16Escapes(string s) {
    return ReplaceTokensWithEscapes(s, UnicodeEscape, match => {
      var utf16CodeUnits = new char[2];
      var hexDigits = Util.RemoveUnderscores(match.Groups[1].Value);
      var codePoint = new Rune(Convert.ToInt32(hexDigits, 16));
      var codeUnits = codePoint.EncodeToUtf16(utf16CodeUnits);
      if (codeUnits == 2) {
        return ToUtf16Escape(utf16CodeUnits[0]) + ToUtf16Escape(utf16CodeUnits[1]); ;
      } else {
        return ToUtf16Escape(utf16CodeUnits[0]);
      }
    });
  }

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
  /// Replaced any escaped characters in s by the actual character that the escaping represents.
  /// Assumes s to be a well-parsed string.
  /// </summary>
  public static string RemoveEscaping(DafnyOptions options, string s, bool isVerbatimString) {
    Contract.Requires(s != null);
    var sb = new StringBuilder();
    if (options.Get(CommonOptionBag.UnicodeCharacters)) {
      foreach (var ch in UnescapedCharacters(options, s, isVerbatimString)) {
        sb.Append(new Rune(ch));
      }
    } else {
      foreach (var ch in UnescapedCharacters(options, s, isVerbatimString)) {
        sb.Append((char)ch);
      }
    }
    return sb.ToString();
  }
  
    public static IEnumerable<int> UnescapedCharacters(DafnyOptions options, string p, bool isVerbatimString) {
      return UnescapedCharacters(options.Get(CommonOptionBag.UnicodeCharacters), p, isVerbatimString);
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
    
  public static void ValidateEscaping(DafnyOptions options, IToken t, string s, bool isVerbatimString, Errors errors) {
    if (options.Get(CommonOptionBag.UnicodeCharacters)) {
      foreach (var token in TokensWithEscapes(s, isVerbatimString)) {
        if (token.StartsWith("\\u")) {
          errors.SemErr(ErrorId.g_no_old_unicode_char, t, "\\u escape sequences are not permitted when Unicode chars are enabled");
        }

        if (token.StartsWith("\\U")) {
          var hexDigits = Util.RemoveUnderscores(token[3..^1]);
          if (hexDigits.Length > 6) {
            errors.SemErr(ErrorId.g_unicode_escape_must_have_six_digits, t, "\\U{X..X} escape sequence must have at most six hex digits");
          } else {
            var codePoint = Convert.ToInt32(hexDigits, 16);
            if (codePoint >= 0x11_0000) {
              errors.SemErr(ErrorId.g_unicode_escape_is_too_large, t, "\\U{X..X} escape sequence must be less than 0x110000");
            }
            if (codePoint is >= 0xD800 and < 0xE000) {
              errors.SemErr(ErrorId.g_unicode_escape_may_not_be_surrogate, t, "\\U{X..X} escape sequence must not be a surrogate");
            }
          }
        }
      }
    } else {
      foreach (var token2 in TokensWithEscapes(s, isVerbatimString)) {
        if (token2.StartsWith("\\U")) {
          errors.SemErr(ErrorId.g_U_unicode_chars_are_disallowed, t, "\\U escape sequences are not permitted when Unicode chars are disabled");
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
          errors.Deprecated(ErrorId.g_deprecated_this_in_constructor_modifies_clause, fe.E.tok, "constructors no longer need 'this' to be listed in modifies clauses");
          return;
        } else if (fe.E is SetDisplayExpr) {
          var s = (SetDisplayExpr)fe.E;
          var deprecated = s.Elements.FindAll(e => e is ThisExpr);
          if (deprecated.Count != 0) {
            foreach (var e in deprecated) {
              errors.Deprecated(ErrorId.g_deprecated_this_in_constructor_modifies_clause, e.tok, "constructors no longer need 'this' to be listed in modifies clauses");
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
    
    static Graph<Function> BuildFunctionCallGraph(Program program) {
      Graph<Function> functionCallGraph = new Graph<Function>();
      FunctionCallFinder callFinder = new FunctionCallFinder();

      foreach (var module in program.Modules()) {
        foreach (var decl in module.TopLevelDecls) {
          if (decl is TopLevelDeclWithMembers c) {
            foreach (var member in c.Members) {
              if (member is Function f) {
                List<Function> calls = new List<Function>();
                foreach (var e in f.Reads.Expressions) { if (e != null && e.E != null) { callFinder.Visit(e.E, calls); } }
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
    public static void PrintFunctionCallGraph(Program program) {
      var functionCallGraph = BuildFunctionCallGraph(program);

      foreach (var vertex in functionCallGraph.GetVertices()) {
        var func = vertex.N;
        program.Options.OutputWriter.Write("{0},{1}=", func.SanitizedName, func.EnclosingClass.EnclosingModuleDefinition.SanitizedName);
        foreach (var callee in vertex.Successors) {
          program.Options.OutputWriter.Write("{0} ", callee.N.SanitizedName);
        }
        program.Options.OutputWriter.Write("\n");
      }
    }
    
    /// <summary>
    /// Compute various interesting statistics about the Dafny program
    /// </summary>
    public static void PrintStats(Program program) {
      SortedDictionary<string, ulong> stats = new SortedDictionary<string, ulong>();

      foreach (var module in program.Modules()) {
        IncrementStat(stats, "Modules");
        UpdateMax(stats, "Module height (max)", (ulong)module.Height);

        ulong num_scc = (ulong)module.CallGraph.TopologicallySortedComponents().Count;
        UpdateMax(stats, "Call graph width (max)", num_scc);

        foreach (var decl in module.TopLevelDecls) {
          if (decl is DatatypeDecl) {
            IncrementStat(stats, "Datatypes");
          } else if (decl is ClassLikeDecl) {
            var c = (ClassLikeDecl)decl;
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
      program.Options.OutputWriter.WriteLine("");
      program.Options.OutputWriter.WriteLine("Statistics");
      program.Options.OutputWriter.WriteLine("----------");

      int max_key_length = 0;
      foreach (var key in stats.Keys) {
        if (key.Length > max_key_length) {
          max_key_length = key.Length;
        }
      }

      foreach (var keypair in stats) {
        string keyString = keypair.Key.PadRight(max_key_length + 2);
        program.Options.OutputWriter.WriteLine("{0} {1,4}", keyString, keypair.Value);
      }
    }
    /// <summary>
    /// Generic statistic counter
    /// </summary>
    static void IncrementStat(IDictionary<string, ulong> stats, string stat) {
      if (stats.TryGetValue(stat, out var currentValue)) {
        stats[stat] += 1;
      } else {
        stats.Add(stat, 1);
      }
    }

    /// <summary>
    /// Track the maximum value of some statistic
    /// </summary>
    static void UpdateMax(IDictionary<string, ulong> stats, string stat, ulong val) {
      if (stats.TryGetValue(stat, out var currentValue)) {
        if (val > currentValue) {
          stats[stat] = val;
        }
      } else {
        stats.Add(stat, val);
      }
    }

    public static IEnumerable<string> Lines(TextReader reader) {
      return new LinesEnumerable(reader);
    }
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

class LinesEnumerable : IEnumerable<string> {
  private readonly TextReader Reader;

  public LinesEnumerable(TextReader reader) {
    Reader = reader;
  }

  public IEnumerator<string> GetEnumerator() {
    return new LinesEnumerator(Reader);
  }

  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }
}

class LinesEnumerator : IEnumerator<string> {

  private readonly TextReader Reader;

  public LinesEnumerator(TextReader reader) {
    Reader = reader;
  }

  public bool MoveNext() {
    Current = Reader.ReadLine();
    return Current != null;
  }

  public void Reset() {
    throw new NotImplementedException();
  }

  public string Current { get; internal set; }

  object IEnumerator.Current => Current;

  public void Dispose() {
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

  public void PrintMap(DafnyOptions options) {
    SortedSet<string> leaves = new SortedSet<string>(); // Files that don't themselves include any files
    foreach (string target in dependencies.Keys) {
      options.OutputWriter.Write(target);
      foreach (string dependency in dependencies[target]) {
        options.OutputWriter.Write(";" + dependency);
        if (!dependencies.ContainsKey(dependency)) {
          leaves.Add(dependency);
        }
      }
      options.OutputWriter.WriteLine();
    }
    foreach (string leaf in leaves) {
      options.OutputWriter.WriteLine(leaf);
    }
  }
}