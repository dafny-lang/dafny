using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using ExistsExpr = Microsoft.Boogie.ExistsExpr;
using Expr = Microsoft.Boogie.Expr;
using ForallExpr = Microsoft.Boogie.ForallExpr;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using Type = Microsoft.Boogie.Type;

namespace DafnyTestGeneration {

  public static class EcpEngine {

    /// <summary>
    /// Decomposes a Boogie Expr into Disjunctive Normal Form (DNF) 
    /// Returns a list of conjunctive clauses (each clause is a list of Expr).
    /// </summary>
    public static List<List<Expr>> ExprToDnf(Expr expr) {
      return ExprToDnfInner(expr);
    }

    /// <summary>
    /// Build a left-folded conjunction (And) of multiple expressions.
    /// </summary>
    public static Expr ConjoinExprs(List<Expr> exprs) {
      if (exprs.Count == 0) {
        return Expr.True;
      }
      var result = exprs[0];
      for (int i = 1; i < exprs.Count; i++) {
        result = Expr.And(result, exprs[i]);
      }
      return result;
    }

    /// <summary>
    /// Calculates the safe DNF combination of a List of Expr
    /// </summary>
    public static List<List<Expr>> CalculateSafeCombinations(List<Expr> exprs) {
      var result = new List<List<Expr>> { new() };

      foreach (var expr in exprs) {
        var exprDnf = ExprToDnf(expr);
        var tmpDnfExprs = new List<List<Expr>>();
        var combinations = new List<List<Expr>>();
        var previousNegations = new List<Expr>();

        for (int i = 0; i < exprDnf.Count; i++) {
          var combination = new List<Expr>();
          var currentBranch = exprDnf[i];

          combination.AddRange(previousNegations);
          combination.AddRange(currentBranch);

          if (!FindContradiction(combination, out _)) {
            combinations.Add(combination);
          }

          if (currentBranch.Count == 1) {
            previousNegations.Add(Negate(currentBranch[0]));
          } else if (currentBranch.Count > 1) {
            var conjoined = ConjoinExprs(currentBranch);
            previousNegations.Add(Negate(conjoined));
          }
        }

        foreach (var existingCombination in result) {
          foreach (var comb in combinations) {
            var merged = new List<Expr>(existingCombination);
            merged.AddRange(comb);

            if (!FindContradiction(merged, out _)) {
              tmpDnfExprs.Add(merged);
            }
          }
        }
        result = tmpDnfExprs;
      }

      return result;
    }

    /// <summary>
    /// Calculates the full DNF combination of a List of Expr
    /// </summary>
    public static List<List<Expr>> CalculateAllCombinations(List<Expr> exprs) {
      var result = new List<List<Expr>> { new() };

      foreach (var expr in exprs) {
        var exprDnf = ExprToDnf(expr);
        var tmpDnfExprs = new List<List<Expr>>();

        var knownUnsatMasks = new List<int>();
        int pm = exprDnf.Count;
        int totalComb = (1 << pm) - 1;
        var combinations = new List<List<Expr>>();

        for (int mask = 1; mask <= totalComb; mask++) {
          if (knownUnsatMasks.Any(unsatMask => (mask & unsatMask) == unsatMask)) {
            continue;
          }

          var combination = new List<Expr>();
          for (int bit = 0; bit < pm; bit++) {
            var currentBranch = exprDnf[bit];
            if ((mask & (1 << bit)) != 0) {
              combination.AddRange(currentBranch);
            } else {
              if (currentBranch.Count == 1) {
                combination.Add(Negate(currentBranch[0]));
              } else if (currentBranch.Count > 1) {
                var conjoined = ConjoinExprs(currentBranch);
                combination.Add(Negate(conjoined));
              }
            }
          }

          if (FindContradiction(combination, out _)) {
            knownUnsatMasks.Add(mask);
            continue;
          }
          combinations.Add(combination);
        }

        foreach (var existingCombination in result) {
          foreach (var comb in combinations) {
            var merged = new List<Expr>(existingCombination);
            merged.AddRange(comb);

            if (!FindContradiction(merged, out _)) {
              tmpDnfExprs.Add(merged);
            }
          }
        }
        result = tmpDnfExprs;
      }

      return result;
    }

    /// <summary>
    /// Calculates Boundary Value Analysis (BVA) for each parameter based on extracted constraints.
    /// </summary>
    public static List<Expr> CalculateBva(List<Variable> variables, Dictionary<string, VariableConstraint> constraints, Program program, int bvaValue) {
      var result = new List<Expr>();

      foreach (var variable in variables) {
        var type = variable.TypedIdent.Type;
        var stringType = type.ToString();
        var idExpr = new IdentifierExpr(new Token(), variable);

        if (type.IsBool) {
          result.Add(CreateEqExpr(idExpr, Expr.True));
          result.Add(CreateEqExpr(idExpr, Expr.False));
        } else if (type.IsInt || type.IsReal || type.IsFloat || type.IsBv) {

          constraints.TryGetValue(variable.Name, out var constraint);
          constraint ??= new VariableConstraint();

          if (constraint.ExactValue.HasValue) {
            continue;
          }

          var bounds = constraint.Bounds;
          double offset = (type.IsReal || type.IsFloat) ? 0.0001 : 1.0;

          double fallbackLower = -bvaValue;
          double fallbackUpper = bvaValue;

          if (type.IsBv && type is BvType bvType) {
            fallbackLower = 0;
            fallbackUpper = bvType.Bits < 64 ? ((1UL << bvType.Bits) - 1) : bvaValue;
          }

          if (!double.IsNegativeInfinity(bounds.LowerLimit)) {
            double val = bounds.IncludeLower ? bounds.LowerLimit : bounds.LowerLimit + offset;
            if (!constraint.Exclusions.Contains(val)) {
              result.Add(CreateEqExpr(idExpr, CreateNumericLiteral(val, type, program)));
            }
          } else if (!constraint.Exclusions.Contains(fallbackLower)) {
            result.Add(CreateEqExpr(idExpr, CreateNumericLiteral(fallbackLower, type, program)));
          }

          if (!double.IsPositiveInfinity(bounds.UpperLimit)) {
            double val = bounds.IncludeUpper ? bounds.UpperLimit : bounds.UpperLimit - offset;
            if (!constraint.Exclusions.Contains(val)) {
              result.Add(CreateEqExpr(idExpr, CreateNumericLiteral(val, type, program)));
            }
          } else if (!constraint.Exclusions.Contains(fallbackUpper)) {
            result.Add(CreateEqExpr(idExpr, CreateNumericLiteral(fallbackUpper, type, program)));
          }
        } else if (type.IsSeq || type.IsString || type.IsMap || stringType.Equals("Seq") || stringType.Equals("Map") || stringType.Equals("Set")) {
          var cardinalityName = "|" + variable.Name + "|";

          constraints.TryGetValue(cardinalityName, out var constraint);
          constraint ??= new VariableConstraint();

          if (constraint.ExactValue.HasValue) {
            continue;
          }

          var bounds = constraint.Bounds;
          var exclusions = constraint.Exclusions;

          Expr? cardExpr = CreateCardinalityExpr(variable, program);
          if (cardExpr == null) {
            continue;
          }

          // Length == 0
          if (bounds.IncludesValue(0) && !exclusions.Contains(0)) {
            result.Add(CreateEqExpr(cardExpr, CreateNumericLiteral(0, Type.Int, program)));
          }

          // Length == 1
          if (bounds.IncludesValue(1) && !exclusions.Contains(1)) {
            result.Add(CreateEqExpr(cardExpr, CreateNumericLiteral(1, Type.Int, program)));
          }

          // Length > 1
          if (bounds.UpperLimit > 1) {
            var gtExpr = new NAryExpr(
              new Token(),
              new BinaryOperator(new Token(), BinaryOperator.Opcode.Gt),
              new List<Expr> { cardExpr, CreateNumericLiteral(1, Type.Int, program) }
            ) { Type = Type.Bool };

            result.Add(gtExpr);
          }
        }
      }

      return result;
    }

    /// <summary>
    /// Creates a NAryExpr with the equality operator.
    /// </summary>
    private static Expr CreateEqExpr(Expr left, Expr right) {
      var naryExpr = new NAryExpr(
        new Token(),
        new BinaryOperator(new Token(), BinaryOperator.Opcode.Eq),
        new List<Expr> { left, right }
      );
      naryExpr.Type = Type.Bool;
      return naryExpr;
    }

    /// <summary>
    /// Creates the Boogie AST expression representing the cardinality of a collection.
    /// Maps to Seq#Length, Map#Card, or Set#Card
    /// </summary>
    private static Expr? CreateCardinalityExpr(Variable variable, Program program) {
      var type = variable.TypedIdent.Type;
      var stringType = type.ToString();
      var idExpr = new IdentifierExpr(new Token(), variable);
      string funcName = "";

      if (stringType.Equals("Seq")) {
        funcName = "Seq#Length";
      } else if (stringType.Equals("Map")) {
        funcName = "Map#Card";
      } else if (stringType.Equals("Set")) {
        funcName = "Set#Card";
      } else {
        return null;
      }

      var realFunc = program.TopLevelDeclarations
        .OfType<Function>()
        .FirstOrDefault(f => f.Name == funcName);

      if (realFunc == null) {
        realFunc = new Function(
          Token.NoToken,
          funcName,
          new List<TypeVariable>(),
          new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "coll", type), true) },
          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "len", Type.Int), false)
        );
      }

      var funcCall = new FunctionCall(realFunc);
      return new NAryExpr(Token.NoToken, funcCall, new List<Expr> { idExpr }) {
        Type = Type.Int
      };
    }

    /// <summary>
    /// Safely converts a numeric value into the correct Boogie Expr (Int, Real, or Bitvector)
    /// </summary>
    private static Expr CreateNumericLiteral(double value, Type type, Program program) {

      if (type.IsBv) {
        int bvVal = Math.Max(0, (int)value);
        var rawLiteral = new LiteralExpr(new Token(), BigNum.FromInt(bvVal)) { Type = type };

        var litFunc = program.TopLevelDeclarations.OfType<Function>().FirstOrDefault(f => f.Name == "Lit");

        if (litFunc != null) {
          var funcCall = new FunctionCall(litFunc);
          var naryExpr = new NAryExpr(new Token(), funcCall, new List<Expr> { rawLiteral }) {
            Type = type
          };

          if (litFunc.TypeParameters.Count > 0) {
            naryExpr.TypeParameters = SimpleTypeParamInstantiation.From(litFunc.TypeParameters, new List<Type> { type });
          }
          return naryExpr;
        }
        return rawLiteral;
      }

      if (type.IsReal || type.IsFloat) {
        string strVal = value.ToString("0.0#######");
        return new LiteralExpr(new Token(), BigDec.FromString(strVal)) { Type = type };
      }

      return new LiteralExpr(new Token(), BigNum.FromInt((int)value)) { Type = type };
    }

    /// <summary>
    /// Calculate the cross product of two lists of expressions.
    /// Each clause from A is merged with each clause from B.
    /// </summary>
    private static List<List<Expr>> CrossProduct(List<List<Expr>> a, List<List<Expr>> b) {
      var result = new List<List<Expr>>();
      foreach (var clauseA in a) {
        foreach (var clauseB in b) {
          var merged = new List<Expr>(clauseA);
          merged.AddRange(clauseB);
          result.Add(merged);
        }
      }
      return result;
    }

    /// <summary>
    /// Wraps an expression in a negation: !(expr)
    /// If the expression is already negative, it returns its positive counterpart
    /// </summary>
    private static Expr Negate(Expr expr) {
      if (expr is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } nary) {
        return nary.Args[0];
      }
      return Expr.Not(expr);
    }

    /// <summary>
    /// Inner workings of the DNF decomposition
    /// </summary>
    private static List<List<Expr>> ExprToDnfInner(Expr expr, bool negated = false) {
      if (expr is NAryExpr nary) {
        if (nary.Fun is UnaryOperator { Op: UnaryOperator.Opcode.Not }) {
          return ExprToDnfInner(nary.Args[0], !negated);
        }

        if (nary.Fun is BinaryOperator binOp) {
          var a = nary.Args[0];
          var b = nary.Args[1];

          switch (binOp.Op) {
            case BinaryOperator.Opcode.Imp when !negated: {
                var notA = ExprToDnfInner(a, true);
                var bDnf = ExprToDnfInner(b);
                var result = new List<List<Expr>>(notA);
                result.AddRange(bDnf);
                return result;
              }
            case BinaryOperator.Opcode.Imp: {
                return CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b, true));
              }
            case BinaryOperator.Opcode.And when !negated: {
                return CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b));
              }
            case BinaryOperator.Opcode.And: {
                var notA = ExprToDnfInner(a, true);
                var notB = ExprToDnfInner(b, true);
                var result = new List<List<Expr>>(notA);
                result.AddRange(notB);
                return result;
              }
            case BinaryOperator.Opcode.Or when !negated: {
                var aDnf = ExprToDnfInner(a);
                var bDnf = ExprToDnfInner(b);
                var result = new List<List<Expr>>(aDnf);
                result.AddRange(bDnf);
                return result;
              }
            case BinaryOperator.Opcode.Or: {
                return CrossProduct(ExprToDnfInner(a, true), ExprToDnfInner(b, true));
              }
            case BinaryOperator.Opcode.Iff when !negated: {
                var ab = CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b));
                var notAnotB = CrossProduct(ExprToDnfInner(a, true), ExprToDnfInner(b, true));
                var result = new List<List<Expr>>(ab);
                result.AddRange(notAnotB);
                return result;
              }
            case BinaryOperator.Opcode.Iff: {
                var aNotB = CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b, true));
                var notAb = CrossProduct(ExprToDnfInner(a, true), ExprToDnfInner(b));
                var result = new List<List<Expr>>(aNotB);
                result.AddRange(notAb);
                return result;
              }
          }
        }
      } else if (expr is ExistsExpr exists && !negated) {
        var bodyDnf = ExprToDnfInner(exists.Body);
        var result = new List<List<Expr>>();
        foreach (var branch in bodyDnf) {
          var conjoined = ConjoinExprs(branch);
          result.Add([
            new ExistsExpr(exists.tok, exists.TypeParameters, exists.Dummies, exists.Attributes, exists.Triggers,
              conjoined)
          ]);
        }
        return result;
      } else if (expr is ForallExpr forall && negated) {
        var bodyDnf = ExprToDnfInner(forall.Body, true);
        var result = new List<List<Expr>>();
        foreach (var branch in bodyDnf) {
          var conjoined = ConjoinExprs(branch);
          result.Add([
            new ExistsExpr(forall.tok, forall.TypeParameters, forall.Dummies, forall.Attributes, forall.Triggers,
              conjoined)
          ]);
        }
        return result;
      }

      var atom = negated ? Negate(expr) : expr;
      return [[atom]];
    }

    /// <summary>
    /// Finds contradictions in a DNF combination, making the conjunction trivially UNSAT without needing Z3.
    /// Detects:
    ///   1. Direct complements: L and !(L) both present
    ///   2. Equality contradictions: x == v1 and x == v2 where v1 != v2 (and v1 and v2 are numeric values)
    ///   2. Inequality contradictions: e.g., x lt 0 and x gt 0, or x == 0 and x != 0
    /// x might be the name of a variable, or the cardinality of a collection such as: |x|
    /// Returns true if a contradiction is found, and false otherwise.
    /// </summary>
    public static bool FindContradiction(List<Expr> combination, out Dictionary<string, VariableConstraint> constraints) {
      constraints = new Dictionary<string, VariableConstraint>();
      var positiveBooleans = new HashSet<string>();
      var negativeBooleans = new HashSet<string>();

      foreach (var expr in combination) {
        if (IsInequality(expr, out string? inVarName, out BinaryOperator.Opcode? op, out double? inValue)) {
          if (inVarName == null || op == null || inValue == null) {
            continue;
          }

          if (!constraints.ContainsKey(inVarName)) {
            constraints[inVarName] = new VariableConstraint();
          }

          var constraint = constraints[inVarName];
          double val = (double)inValue;

          bool isValid = op switch {
            BinaryOperator.Opcode.Eq => constraint.AddEquality(val),
            BinaryOperator.Opcode.Neq => constraint.AddInequality(val),
            BinaryOperator.Opcode.Gt => constraint.AddLowerBound(val, false),
            BinaryOperator.Opcode.Ge => constraint.AddLowerBound(val, true),
            BinaryOperator.Opcode.Lt => constraint.AddUpperBound(val, false),
            BinaryOperator.Opcode.Le => constraint.AddUpperBound(val, true),
            _ => true
          };

          if (!isValid) {
            return true;
          }
        } else if (IsNegated(expr, out string innerName)) {
          if (positiveBooleans.Contains(innerName)) {
            return true;
          }
          negativeBooleans.Add(innerName);
        } else if (IsIdentifier(expr, out string posName)) {
          if (negativeBooleans.Contains(posName)) {
            return true;
          }
          positiveBooleans.Add(posName);
        }
      }
      return false;
    }
    /// <summary>
    /// Checks if expr is an Inequality/Equality.
    /// If it is, it returns the variable, the operator, and the value (if it is numeric)
    /// </summary>
    private static bool IsInequality(Expr expr, out string? varName, out BinaryOperator.Opcode? op, out double? value) {
      varName = null; op = null; value = null;
      bool isNegated = false;
      var innerExpr = expr;

      if (expr is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } naryNot) {
        isNegated = true;
        innerExpr = naryNot.Args[0];
      }

      if (innerExpr is NAryExpr { Fun: BinaryOperator binOp } nary) {
        op = GetLogicalOperator(binOp.Op, isNegated);
        if (op == null) {
          return false;
        }

        var a = nary.Args[0];
        var b = nary.Args[1];

        if (TryExtractVariable(a, out string nameA) && TryExtractValue(b, out double valB)) {
          varName = nameA;
          value = valB;
          return true;
        }

        if (TryExtractVariable(b, out string nameB) && TryExtractValue(a, out double valA)) {
          varName = nameB;
          value = valA;
          op = GetLogicalOperator(binOp.Op, isNegated, flipSides: true);
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Checks if an expression is a variable or a collection cardinality (e.g., |s|)
    /// </summary>
    private static bool TryExtractVariable(Expr expr, out string varName) {
      varName = "";

      if (expr is IdentifierExpr id) {
        varName = id.Name;
        return true;
      }

      if (expr is NAryExpr { Fun: FunctionCall fn } nary) {
        string fnName = fn.Func.Name;

        if (fnName.EndsWith("#Length") || fnName.EndsWith("#Card")) {
          if (nary.Args.Count > 0 && nary.Args[0] is IdentifierExpr cardId) {
            varName = "|" + cardId.Name + "|";
            return true;
          }
        }
      }

      return false;
    }

    /// <summary>
    /// Safely unpacks a numeric value from either a Literal or an NAry expression
    /// </summary>
    private static bool TryExtractValue(Expr expr, out double value) {
      value = 0;

      if (expr is NAryExpr nary) {
        var unpacked = UnpackNAry(nary);
        if (unpacked.HasValue) {
          value = unpacked.Value;
          return true;
        }
      } else if (expr is LiteralExpr lit) {
        if (double.TryParse(lit.Val.ToString(), out double val)) {
          value = val;
          return true;
        }
      }

      return false;
    }

    /// <summary>
    /// Unpack NAryExpr and handle possible negations
    /// </summary>
    private static double? UnpackNAry(NAryExpr expr) {
      if (expr.Args[0] is NAryExpr innerExpr) {
        if (expr.Fun is UnaryOperator { Op: UnaryOperator.Opcode.Neg } && innerExpr.Args[0] is LiteralExpr negLit) {
          var stringVal = negLit.Val.ToString();
          if (double.TryParse(stringVal, out double doubleVal)) {
            return doubleVal;
          }
        }
        return UnpackNAry(innerExpr);
      } else if (expr.Args[0] is LiteralExpr literalExpr) {
        var stringVal = literalExpr.Val.ToString();

        if (expr.Fun is UnaryOperator { Op: UnaryOperator.Opcode.Neg }) {
          if (double.TryParse(stringVal, out double negDoubleVal)) {
            return -negDoubleVal;
          }
        }

        if (double.TryParse(stringVal, out double doubleVal)) {
          return doubleVal;
        }
      }

      return null;
    }

    /// <summary>
    /// Returns the logical operator if it is ==, !=, gt, lt, ge, le
    /// If isNegated, switch the operator (e.g., gt -> le)
    /// If flipSides, flip the operator (e.g., gt -> lt)
    /// </summary>
    private static BinaryOperator.Opcode? GetLogicalOperator(BinaryOperator.Opcode op, bool isNegated = false, bool flipSides = false) {
      if (op != BinaryOperator.Opcode.Gt && op != BinaryOperator.Opcode.Ge && op != BinaryOperator.Opcode.Lt &&
          op != BinaryOperator.Opcode.Le && op != BinaryOperator.Opcode.Eq && op != BinaryOperator.Opcode.Neq) {
        return null;
      }
      var resultOp = op;

      if (flipSides) {
        switch (resultOp) {
          case BinaryOperator.Opcode.Gt: resultOp = BinaryOperator.Opcode.Lt; break;
          case BinaryOperator.Opcode.Ge: resultOp = BinaryOperator.Opcode.Le; break;
          case BinaryOperator.Opcode.Lt: resultOp = BinaryOperator.Opcode.Gt; break;
          case BinaryOperator.Opcode.Le: resultOp = BinaryOperator.Opcode.Ge; break;
        }
      }

      if (isNegated) {
        switch (resultOp) {
          case BinaryOperator.Opcode.Gt: resultOp = BinaryOperator.Opcode.Le; break;
          case BinaryOperator.Opcode.Ge: resultOp = BinaryOperator.Opcode.Lt; break;
          case BinaryOperator.Opcode.Lt: resultOp = BinaryOperator.Opcode.Ge; break;
          case BinaryOperator.Opcode.Le: resultOp = BinaryOperator.Opcode.Gt; break;
          case BinaryOperator.Opcode.Eq: resultOp = BinaryOperator.Opcode.Neq; break;
          case BinaryOperator.Opcode.Neq: resultOp = BinaryOperator.Opcode.Eq; break;
        }
      }
      return resultOp;
    }

    /// <summary>
    /// Checks is an IdentifierExpr is negated.
    /// </summary>
    private static bool IsNegated(Expr expr, out string innerName) {
      innerName = "";
      if (expr is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } nary) {
        if (nary.Args[0] is IdentifierExpr id) {
          innerName = id.Name;
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Checks if expr is IdentifierExpr.
    /// </summary>
    private static bool IsIdentifier(Expr expr, out string name) {
      name = "";
      if (expr is IdentifierExpr id) {
        name = id.Name;
        return true;
      }
      return false;
    }

    /// <summary>
    /// Fixes Expr's types, because sometimes they end up being Null, which crashes the pipeline.
    /// </summary>
    public static void FixTypes(Expr expr) {
      if (expr is LiteralExpr { Type: null } lit) {
        lit.Type = lit.Val switch {
          BigNum => Type.Int,
          bool => Type.Bool,
          BigDec => Type.Real,
          BvType bvConst => Type.GetBvType(bvConst.Bits),
          _ => lit.Type
        };
      } else if (expr is QuantifierExpr quant) {
        FixTypes(quant.Body);
        quant.Type ??= Type.Bool;
      } else if (expr is OldExpr oldExpr) {
        FixTypes(oldExpr.Expr);
        oldExpr.Type ??= oldExpr.Expr.Type;
      } else if (expr is NAryExpr nary) {
        foreach (var arg in nary.Args) {
          FixTypes(arg);
        }

        if (nary.Type == null) {
          switch (nary.Fun) {
            case BinaryOperator binOp:
              switch (binOp.Op) {
                case BinaryOperator.Opcode.Eq:
                case BinaryOperator.Opcode.Neq:
                case BinaryOperator.Opcode.Lt:
                case BinaryOperator.Opcode.Le:
                case BinaryOperator.Opcode.Gt:
                case BinaryOperator.Opcode.Ge:
                case BinaryOperator.Opcode.And:
                case BinaryOperator.Opcode.Or:
                case BinaryOperator.Opcode.Imp:
                case BinaryOperator.Opcode.Iff:
                  nary.Type = Type.Bool;
                  break;
                case BinaryOperator.Opcode.Add:
                case BinaryOperator.Opcode.Sub:
                case BinaryOperator.Opcode.Mul:
                case BinaryOperator.Opcode.Div:
                case BinaryOperator.Opcode.Mod:
                case BinaryOperator.Opcode.RealDiv:
                case BinaryOperator.Opcode.FloatDiv:
                case BinaryOperator.Opcode.Pow:
                default:
                  nary.Type = nary.Args[0].Type ?? Type.Int;
                  break;
              }

              break;
            case UnaryOperator unOp:
              nary.Type = unOp.Op == UnaryOperator.Opcode.Not
                ? Type.Bool
                : (nary.Args[0].Type ?? Type.Int);
              break;
            case FunctionCall funcCall:
              nary.Type = funcCall.Func.OutParams[0].TypedIdent.Type;
              break;
            case MapSelect when nary.Args[0].Type is MapType mapType:
              nary.Type = mapType.Result;
              break;
            case MapStore:
              nary.Type = nary.Args[0].Type;
              break;
          }
        }
      }
    }
  }

  public class Range(
    bool includeLower = true,
    double lowerLimit = Double.NegativeInfinity,
    double upperLimit = Double.PositiveInfinity,
    bool includeUpper = true) {
    public bool IncludeLower = includeLower;
    public double LowerLimit = lowerLimit;
    public double UpperLimit = upperLimit;
    public bool IncludeUpper = includeUpper;

    public Range() : this(true, Double.NegativeInfinity, Double.PositiveInfinity, true) {
    }

    public bool IsImpossible() {
      if (UpperLimit < LowerLimit) {
        return true;
      }
      if (LowerLimit.Equals(UpperLimit) && (!IncludeUpper || !IncludeLower)) {
        return true;
      }
      return false;
    }

    public bool HoldsSingleValue(out double? value) {
      if (LowerLimit.Equals(UpperLimit) && IncludeLower && IncludeUpper) {
        value = LowerLimit;
        return true;
      }
      value = null;
      return false;
    }

    public bool IncludesValue(double? value) {
      if (value == null) {
        return false;
      }
      if (value > LowerLimit && value < UpperLimit) {
        return true;
      }
      if (value.Equals(LowerLimit) && IncludeLower) {
        return true;
      }
      if (value.Equals(UpperLimit) && IncludeUpper) {
        return true;
      }
      return false;
    }

  }

  public class VariableConstraint {
    public Range Bounds { get; } = new();
    public double? ExactValue { get; private set; }
    public HashSet<double> Exclusions { get; } = new();

    public bool AddEquality(double value) {
      if (ExactValue.HasValue && !ExactValue.Value.Equals(value)) {
        return false;
      }

      if (Exclusions.Contains(value)) {
        return false;
      }

      if (!Bounds.IncludesValue(value)) {
        return false;
      }

      ExactValue = value;
      return true;
    }

    public bool AddInequality(double value) {
      if (ExactValue.HasValue && ExactValue.Value.Equals(value)) {
        return false;
      }

      if (Bounds.HoldsSingleValue(out var singleValue) && singleValue != null && singleValue.Value.Equals(value)) {
        return false;
      }

      Exclusions.Add(value);
      return true;
    }

    public bool AddUpperBound(double value, bool inclusive) {
      if (value < Bounds.UpperLimit || (value.Equals(Bounds.UpperLimit) && !inclusive)) {
        Bounds.UpperLimit = value;
        Bounds.IncludeUpper = inclusive;
      }
      return ValidateState();
    }

    public bool AddLowerBound(double value, bool inclusive) {
      if (value > Bounds.LowerLimit || (value.Equals(Bounds.LowerLimit) && !inclusive)) {
        Bounds.LowerLimit = value;
        Bounds.IncludeLower = inclusive;
      }
      return ValidateState();
    }

    private bool ValidateState() {
      if (Bounds.IsImpossible()) {
        return false;
      }

      if (Bounds.HoldsSingleValue(out var singleValue)) {
        if (singleValue != null && Exclusions.Contains(singleValue.Value)) {
          return false;
        }

        if (ExactValue.HasValue && singleValue != null && !ExactValue.Value.Equals(singleValue.Value)) {
          return false;
        }
        ExactValue = singleValue;
      }

      if (ExactValue.HasValue && !Bounds.IncludesValue(ExactValue.Value)) {
        return false;
      }

      return true;
    }
  }
}