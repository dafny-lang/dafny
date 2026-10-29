// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny.Triggers {

  /// <summary>
  /// See section 2.3 of "Trigger Selection Strategies to Stabilize Program Verifiers" to learn
  /// why we split quantifiers
  /// </summary>
  static class QuantifierSplitter {
    private static BinaryExpr.Opcode FlipOpcode(BinaryExpr.Opcode opCode) {
      if (opCode == BinaryExpr.Opcode.And) {
        return BinaryExpr.Opcode.Or;
      } else if (opCode == BinaryExpr.Opcode.Or) {
        return BinaryExpr.Opcode.And;
      } else {
        throw new ArgumentException();
      }
    }

    // NOTE: If we wanted to split quantifiers as far as possible, it would be
    // enough to put the formulas in DNF (for foralls) or CNF (for exists).
    // Unfortunately, this would cause ill-behaved quantifiers to produce
    // exponentially many smaller quantifiers. Thus we only do one step of
    // distributing, which takes care of the usual precondition case:
    //   forall x :: P(x) ==> (Q(x) && R(x))

    private static UnaryOpExpr Not(Expression expr) {
      return new UnaryOpExpr(expr.Origin, UnaryOpExpr.Opcode.Not, expr) { Type = expr.Type };
    }

    // The paths of the conjuncts of a quantifier as written, and of the expressions that they are in
    private record Paths(ISet<BigInteger> Conjuncts) {
      internal ISet<BigInteger> Prefixes { get; } = Conjuncts.SelectMany(Prefix).ToHashSet();

      private static IEnumerable<BigInteger> Prefix(BigInteger path) {
        for (; path >= 1; path /= 2) {
          yield return path;
        }
      }
    }

    /// <summary>
    /// Adds the conjuncts of expr, or disjuncts, to conjuncts, each with its path: path for expr, the same for the
    /// operand of a negation, and twice that of a binary expression for its first operand and one more for its second.
    /// Given the paths of the conjuncts of the quantifier as written, for the quantifier or a copy that a substitution
    /// makes with the same binary expressions and negations, it adds the subexpressions at these paths instead, and
    /// returns false if expr lacks them.
    /// </summary>
    private static bool SplitExpr(Expression expr, BinaryExpr.Opcode separator, BigInteger path,
      List<(Expression Conjunct, BigInteger Path)> conjuncts, Paths asWritten) {
      expr = expr.Resolved;
      if (expr is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } unary) {
        var first = conjuncts.Count;
        var split = SplitExpr(unary.E, FlipOpcode(separator), path, conjuncts, asWritten);
        for (var i = first; i < conjuncts.Count; i++) {
          conjuncts[i] = (Not(conjuncts[i].Conjunct), conjuncts[i].Path);
        }
        return split;
      }
      var binary = expr as BinaryExpr;
      var isSeparator = binary != null && binary.Op == separator;
      var isImplication = binary != null && binary.Op == BinaryExpr.Opcode.Imp && separator == BinaryExpr.Opcode.Or;
      if (asWritten == null ? !isSeparator && !isImplication : asWritten.Conjuncts.Contains(path)) {
        conjuncts.Add((expr, path));
        return true;
      }
      if (!isSeparator && !isImplication) {
        return false;
      }
      var unit = isSeparator && Expression.IsBoolLiteral(binary.E0, out var b) && (separator == BinaryExpr.Opcode.And ? b : !b);
      if (asWritten?.Prefixes.Contains(2 * path) ?? !unit) {
        if (!SplitExpr(isImplication ? Not(binary.E0) : binary.E0, separator, 2 * path, conjuncts, asWritten)) {
          return false;
        }
      } else if (!unit) {
        return false;
      }
      return SplitExpr(binary.E1, separator, 2 * path + 1, conjuncts, asWritten);
    }

    private static bool SplitAndStitch(BinaryExpr pair, BinaryExpr.Opcode separator,
      List<(Expression Conjunct, BigInteger Path)> conjuncts, Paths asWritten) {
      var first = conjuncts.Count;
      var split = SplitExpr(pair.E1, separator, 1, conjuncts, asWritten);
      for (var i = first; i < conjuncts.Count; i++) {
        var (e1, path) = conjuncts[i];
        // Notice the token. This makes triggers/splitting-picks-the-right-tokens.dfy possible
        var nestedToken = new NestedOrigin(pair.Origin, e1.Origin);
        conjuncts[i] = (new BinaryExpr(nestedToken, pair.Op, pair.E0, e1) { ResolvedOp = pair.ResolvedOp, Type = pair.Type }, path);
      }
      return split;
    }

    /// <summary>
    /// The conjuncts of a forall's body, or disjuncts of an exists's, with their paths, or, given the paths of the
    /// conjuncts of the quantifier as written, the subexpressions at these paths, or null if the body lacks them
    /// </summary>
    private static List<(Expression Conjunct, BigInteger Path)> SplitBody(QuantifierExpr quantifier, Paths asWritten) {
      var body = quantifier.Term;
      var binary = body as BinaryExpr;
      var conjuncts = new List<(Expression Conjunct, BigInteger Path)>();
      bool split;
      if (quantifier is ForallExpr) {
        split = binary != null && (binary.Op == BinaryExpr.Opcode.Imp || binary.Op == BinaryExpr.Opcode.Or)
          ? SplitAndStitch(binary, BinaryExpr.Opcode.And, conjuncts, asWritten)
          : SplitExpr(body, BinaryExpr.Opcode.And, 1, conjuncts, asWritten);
      } else {
        split = binary != null && binary.Op == BinaryExpr.Opcode.And
          ? SplitAndStitch(binary, BinaryExpr.Opcode.Or, conjuncts, asWritten)
          : SplitExpr(body, BinaryExpr.Opcode.Or, 1, conjuncts, asWritten);
      }
      return split ? conjuncts : null;
    }

    /// <summary>
    /// A part of the quantifier whose body is the conjunction of the conjuncts, for a forall, or their disjunction
    /// </summary>
    private static QuantifierExpr Part(QuantifierExpr quantifier, IOrigin origin, List<Expression> conjuncts,
      Attributes attributes) {
      var op = quantifier is ForallExpr ? BinaryExpr.ResolvedOpcode.And : BinaryExpr.ResolvedOpcode.Or;
      var term = conjuncts[0];
      for (var i = 1; i < conjuncts.Count; i++) {
        term = new BinaryExpr(origin, op, term, conjuncts[i]);
      }
      QuantifierExpr part = quantifier is ForallExpr
        ? new ForallExpr(origin, quantifier.BoundVars, quantifier.Range, term, attributes)
        : new ExistsExpr(origin, quantifier.BoundVars, quantifier.Range, term, attributes);
      part.Type = quantifier.Type;
      part.Bounds = quantifier.Bounds;
      return part;
    }

    /// <summary>
    /// The quantifier's parts, one for each conjunct of a forall's body or disjunct of an exists's
    /// </summary>
    internal static List<QuantifierExpr> Conjuncts(QuantifierExpr quantifier) {
      return SplitBody(quantifier, null).ConvertAll(conjunct => Part(quantifier, new AutoGeneratedOrigin(quantifier.Origin),
        [conjunct.Conjunct], TriggerUtils.CopyAttributes(quantifier.Attributes)));
    }

    internal static bool AllowsSplitting(ComprehensionExpr quantifier) {
      // allow split if attributes doesn't contains "split" or it is "split: true" and it is not an empty QuantifierExpr (boundvar.count>0)
      bool splitAttr = true;
      return (!Attributes.ContainsBool(quantifier.Attributes, "split", ref splitAttr) || splitAttr) && (quantifier.BoundVars.Count > 0);
    }

    /// <summary>
    /// One quantifier with the parts' range and bound variables whose body is the conjunction, or disjunction, of
    /// theirs
    /// </summary>
    internal static QuantifierExpr Merge(List<ComprehensionExpr> parts) {
      var first = (QuantifierExpr)parts[0];
      var tok = first.Origin is NestedOrigin nestedToken ? nestedToken.Outer : first.Origin;
      return Part(first, tok, parts.ConvertAll(part => part.Term), TriggerUtils.CopyAttributes(first.Attributes));
    }

    /// <summary>
    /// Records on the quantifier, from which the verifier makes its parts again, that its part #index has these
    /// conjuncts, by their paths, and the attributes from the part's to those that it was given
    /// </summary>
    internal static void RecordPart(QuantifierExpr quantifier, int index, List<int> conjuncts, Attributes attributes,
      Attributes given) {
      var paths = SplitBody(quantifier, null);
      quantifier.Attributes = new Attributes("_part",
        conjuncts.Select(i => paths[i].Path).Prepend(index).Select(Literal).ToList(),
        quantifier.Attributes);
      RecordPartAttributes(quantifier, index, attributes, given);
    }

    /// <summary>
    /// Records on the quantifier that its part #index has the attributes from the part's to those that it was given
    /// </summary>
    internal static void RecordPartAttributes(QuantifierExpr quantifier, int index, Attributes attributes,
      Attributes given) {
      var added = new List<Attributes>();
      for (var attribute = attributes; attribute != given && attribute != null; attribute = attribute.Prev) {
        added.Add(attribute);
      }
      added.Reverse();
      foreach (var attribute in added) {
        quantifier.Attributes = new Attributes("_part." + attribute.Name,
          attribute.Args.Prepend(Literal(index)).ToList(), quantifier.Attributes);
      }
    }

    // The literals that record the parts are in no source
    private static Expression Literal(BigInteger value) {
      return new LiteralExpr(Token.NoToken, value) { Type = Type.Int };
    }

    internal static bool HasParts(QuantifierExpr quantifier) {
      return Attributes.Contains(quantifier.Attributes, "_part");
    }

    internal static bool IsPartAttribute(Attributes attribute) {
      return attribute.Name == "_part" || attribute.Name.StartsWith("_part.");
    }

    /// <summary>
    /// The parts that the trigger generator split the quantifier into, each with the quantifier's attributes and its
    /// own, or null if it did not split the quantifier. In order, they are in the order of the quantifier as written,
    /// with a part for each run of consecutive conjuncts of one part. A copy without the conjuncts of the quantifier as
    /// written is one part with the attributes of all.
    /// </summary>
    internal static List<QuantifierExpr> Parts(QuantifierExpr quantifier, bool inOrder = false) {
      var parts = quantifier.Attributes.AsEnumerable().Where(attribute => attribute.Name == "_part")
        .Select(attribute => attribute.Args.ConvertAll(Value)).OrderBy(args => args[0])
        .Select(args => args.Skip(1).ToList()).ToList();
      if (parts.Count == 0) {
        return null;
      }
      var conjuncts = SplitBody(quantifier, new Paths(parts.SelectMany(part => part).ToHashSet()));
      if (conjuncts == null) {
        var whole = Merge([quantifier]);
        whole.Attributes = PartAttributes(quantifier, _ => true);
        return [whole];
      }
      var runs = new List<(int Index, List<Expression> Conjuncts)>();
      if (inOrder) {
        foreach (var (conjunct, path) in conjuncts) {
          var index = parts.FindIndex(part => part.Contains(path));
          if (runs.Count == 0 || runs[^1].Index != index) {
            runs.Add((index, []));
          }
          runs[^1].Conjuncts.Add(conjunct);
        }
      } else {
        var byPath = conjuncts.ToDictionary(conjunct => conjunct.Path, conjunct => conjunct.Conjunct);
        runs = parts.Select((part, index) => (index, part.ConvertAll(path => byPath[path]))).ToList();
      }
      return runs.ConvertAll(run => Part(quantifier, new AutoGeneratedOrigin(quantifier.Origin), run.Conjuncts,
        PartAttributes(quantifier, other => other == run.Index)));
    }

    private static BigInteger Value(Expression literal) {
      return (BigInteger)((LiteralExpr)literal).Value;
    }

    /// <summary>
    /// The quantifier's attributes, without those of its parts if it has several
    /// </summary>
    internal static Attributes WithoutSeveralParts(QuantifierExpr quantifier) {
      var parts = quantifier.Attributes.AsEnumerable().Count(attribute => attribute.Name == "_part");
      return parts > 1 ? PartAttributes(quantifier, _ => false) : quantifier.Attributes;
    }

    /// <summary>
    /// The quantifier's attributes without those of its parts, and then those of the parts whose index it selects
    /// </summary>
    private static Attributes PartAttributes(QuantifierExpr quantifier, Func<BigInteger, bool> selects) {
      Attributes attributes = null;
      foreach (var attribute in quantifier.Attributes.AsEnumerable().Reverse()) {
        if (attribute.Name.StartsWith("_part.")) {
          if (selects(Value(attribute.Args[0]))) {
            attributes = new Attributes(attribute.Name["_part.".Length..], attribute.Args.Skip(1).ToList(), attributes);
          }
        } else if (attribute.Name != "_part") {
          attributes = new Attributes(attribute.Name, attribute.Args, attributes);
        }
      }
      SplitPartTriggerWriter.DisableEmptyTriggers(attributes, "trigger");
      return attributes;
    }
  }
}
