//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;
using static Microsoft.Dafny.ResolutionErrors;

namespace Microsoft.Dafny {
  class ConstantFolder {
    /// <summary>
    /// Returns the largest value that can be stored in bitvector type "t".
    /// </summary>
    public static BigInteger MaxBv(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(t.IsBitVectorType);
      return MaxBv(t.AsBitVectorType.Width);
    }

    /// <summary>
    /// Returns the largest value that can be stored in bitvector type of "bits" width.
    /// </summary>
    public static BigInteger MaxBv(int bits) {
      Contract.Requires(0 <= bits);
      return BigInteger.Pow(new BigInteger(2), bits) - BigInteger.One;
    }

    /// <summary>
    /// Folds "e" into an integer literal, if possible.
    /// Returns "null" if not possible (or not easy).
    /// </summary>
    public static BigInteger? GetConst(Expression e) {
      var ee = GetAnyConst(e.Resolved ?? e, new Stack<ConstantField>());
      return ee as BigInteger?;
    }

    // Returns null if the argument is a constrained newtype (recursively)
    // Returns the transitive base type if the argument is recursively unconstrained
    static Type AsUnconstrainedType(Type t) {
      while (true) {
        if (t.AsNewtype == null) {
          return t;
        }

        if (t.AsNewtype.Constraint != null) {
          return null;
        }

        t = t.AsNewtype.BaseType;
      }
    }

    static object GetAnyConst(Expression e, Stack<ConstantField> constants) {
      if (e is LiteralExpr l) {
        return l.Value;
      } else if (e is UnaryOpExpr un) {
        if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot && GetAnyConst(un.E, constants) is bool b) {
          return !b;
        }
        if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BVNot && GetAnyConst(un.E, constants) is BigInteger i) {
          return ((BigInteger.One << un.Type.AsBitVectorType.Width) - 1) ^ i;
        }
        // TODO: This only handles strings; generalize to other collections?
        if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.SeqLength && GetAnyConst(un.E, constants) is string ss) {
          return (BigInteger)(ss.Length);
        }
      } else if (e is MemberSelectExpr m) {
        if (m.Member is ConstantField c && c.IsStatic && c.Rhs != null) {
          // This aspect of type resolution happens before the check for cyclic references
          // so we have to do a check here as well. If cyclic, null is silently returned,
          // counting on the later error message to alert the user.
          if (constants.Contains(c)) { return null; }
          constants.Push(c);
          var o = GetAnyConst(c.Rhs, constants);
          constants.Pop();
          return o;
        } else if (m.Member is SpecialField sf) {
          var nm = sf.Name;
          if (nm == "Floor") {
            var ee = GetAnyConst(m.Obj, constants);
            if (ee != null && m.Obj.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
              ((BaseTypes.BigDec)ee).FloorCeiling(out var f, out _);
              return f;
            }
          }
        }
      } else if (e is BinaryExpr bin) {
        var e0 = GetAnyConst(bin.E0, constants);
        if (e0 == null) {
          return null;
        }
        var e1 = GetAnyConst(bin.E1, constants);

        if (bin.E0.Type == Type.Bool && bin.E1.Type == Type.Bool) {
          return FoldBoolean(bin, (bool)e0, (bool?)e1);
        }

        if (e1 == null) {
          return null;
        }

        if (bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Int) && bin.E1.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          return FoldInteger(bin, (BigInteger)e0, (BigInteger)e1);
        } else if (bin.E0.Type.IsBitVectorType && (bin.E1.Type.IsBitVectorType || bin.E1.Type.IsNumericBased(Type.NumericPersuasion.Int))) {
          return FoldBitvector(bin, (BigInteger)e0, (BigInteger)e1);
        } else if (bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Real) && bin.E1.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          return FoldReal(bin, (BaseTypes.BigDec)e0, (BaseTypes.BigDec)e1);
        } else if (e0 is string s0 && e1 is string s1) {
          return FoldCharOrString(bin, s0, s1);
        }

      } else if (e is ConversionExpr ce) {
        var o = GetAnyConst(ce.E, constants);
        if (o == null || ce.E.Type == ce.Type) {
          return o;
        }

        if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) && ce.Type.IsBitVectorType) {
          ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
          if (ff < 0 || ff > MaxBv(ce.Type)) {
            return null; // Out of range
          }
          if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
            return null; // Out of range
          }
          return ff;
        }

        if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) && ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
            return null; // Argument not an integer
          }
          return ff;
        }

        if (ce.E.Type.IsBitVectorType && ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          return o;
        }

        if (ce.E.Type.IsBitVectorType && ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          return BaseTypes.BigDec.FromBigInt((BigInteger)o);
        }

        if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) && ce.Type.IsBitVectorType) {
          var b = (BigInteger)o;
          if (b < 0 || b > MaxBv(ce.Type)) {
            return null; // Argument out of range
          }
          return o;
        }

        if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) && ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          // This case includes int-based newtypes to int-based new types
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          return o;
        }

        if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) && ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          // This case includes real-based newtypes to real-based new types
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          return o;
        }

        if (ce.E.Type.IsBitVectorType && ce.Type.IsBitVectorType) {
          var b = (BigInteger)o;
          if (b < 0 || b > MaxBv(ce.Type)) {
            return null; // Argument out of range
          }
          return o;
        }

        if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) && ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          return BaseTypes.BigDec.FromBigInt((BigInteger)o);
        }

        if (ce.E.Type.IsCharType && ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          var c = ((String)o)[0];
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          return new BigInteger(((string)o)[0]);
        }

        if (ce.E.Type.IsCharType && ce.Type.IsBitVectorType) {
          var c = ((String)o)[0];
          if ((int)c > MaxBv(ce.Type)) {
            return null; // Argument out of range
          }
          return new BigInteger(((string)o)[0]);
        }

        if ((ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || ce.E.Type.IsBitVectorType) && ce.Type.IsCharType) {
          var b = (BigInteger)o;
          if (b < BigInteger.Zero || b > new BigInteger(65535)) {
            return null; // Argument out of range
          }
          return ((char)(int)b).ToString();
        }

        if (ce.E.Type.IsCharType && ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          if (AsUnconstrainedType(ce.Type) == null) {
            return null;
          }
          return BaseTypes.BigDec.FromInt(((string)o)[0]);
        }

        if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) && ce.Type.IsCharType) {
          ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
          if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
            return null; // Argument not an integer
          }
          if (ff < BigInteger.Zero || ff > new BigInteger(65535)) {
            return null; // Argument out of range
          }
          return ((char)(int)ff).ToString();
        }

      } else if (e is SeqSelectExpr sse) {
        var b = GetAnyConst(sse.Seq, constants) as string;
        var index = (BigInteger)GetAnyConst(sse.E0, constants);
        if (b == null) {
          return null;
        }
        if (index < 0 || index >= b.Length || index > Int32.MaxValue) {
          return null; // Index out of range
        }
        return b[(int)index].ToString();
      } else if (e is ITEExpr ite) {
        var b = GetAnyConst(ite.Test, constants);
        if (b == null) {
          return null;
        }
        return ((bool)b) ? GetAnyConst(ite.Thn, constants) : GetAnyConst(ite.Els, constants);
      } else if (e is ConcreteSyntaxExpression n) {
        return GetAnyConst(n.ResolvedExpression, constants);
      } else {
        return null;
      }

      return null;
    }

    private static bool? FoldBoolean(BinaryExpr bin, bool e0, bool? e1) {
      switch (bin.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.And:
          if (e0) {
            return e1;
          } else {
            return false;
          }
        case BinaryExpr.ResolvedOpcode.Or:
          if (e0) {
            return true;
          } else {
            return e1;
          }
        case BinaryExpr.ResolvedOpcode.Imp:
          if (e0) {
            return e1;
          } else {
            return true;
          }
        case BinaryExpr.ResolvedOpcode.Iff:
        case BinaryExpr.ResolvedOpcode.EqCommon:
          if (e1 != null) {
            return e0 == (bool)e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          if (e1 != null) {
            return e0 != (bool)e1;
          }
          break;
        default:
          break;
      }
      return null;
    }

    private static object FoldInteger(BinaryExpr bin, BigInteger e0, BigInteger e1) {
      var isUnconstrained = AsUnconstrainedType(bin.Type) != null;

      switch (bin.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Add:
          if (isUnconstrained) {
            return e0 + e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (isUnconstrained) {
            return e0 - e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          if (isUnconstrained) {
            return e0 * e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (isUnconstrained && e1 != 0) {
            // use Euclidean division
            var d = e0 / e1;
            if (0 <= e0 || e0 == d * e1) {
              return d;
            } else if (0 < e1) {
              return d - 1;
            } else {
              return d + 1;
            }
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (isUnconstrained && e1 != 0) {
            // use Euclidean modulo
            var a = BigInteger.Abs(e1);
            var d = e0 % a;
            return 0 <= e0 ? d : d + a;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
          return e0 > e1;
        case BinaryExpr.ResolvedOpcode.Ge:
          return e0 >= e1;
        case BinaryExpr.ResolvedOpcode.Lt:
          return e0 < e1;
        case BinaryExpr.ResolvedOpcode.Le:
          return e0 <= e1;
        case BinaryExpr.ResolvedOpcode.EqCommon:
          return e0 == e1;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          return e0 != e1;
      }
      return null;
    }

    private static object FoldBitvector(BinaryExpr bin, BigInteger e0, BigInteger e1) {
      Contract.Assert(0 <= e0);

      switch (bin.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Add:
          // modular arithmetic
          return (e0 + e1) & MaxBv(bin.Type);
        case BinaryExpr.ResolvedOpcode.Sub:
          // modular arithmetic
          return (e0 - e1) & MaxBv(bin.Type);
        case BinaryExpr.ResolvedOpcode.Mul:
          // modular arithmetic
          return (e0 * e1) & MaxBv(bin.Type);
        case BinaryExpr.ResolvedOpcode.Div:
          if (e1 != 0) {
            return e0 / e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (e1 != 0) {
            return e0 % e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          return e0 & e1;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          return e0 | e1;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          return e0 ^ e1;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          if (0 <= e1 && e1 <= bin.Type.AsBitVectorType.Width) {
            return (e0 << (int)e1) & MaxBv(bin.E0.Type);
          }
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          if (0 <= e1 && e1 <= bin.Type.AsBitVectorType.Width) {
            return e0 >> (int)e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
          return e0 > e1;
        case BinaryExpr.ResolvedOpcode.Ge:
          return e0 >= e1;
        case BinaryExpr.ResolvedOpcode.Lt:
          return e0 < e1;
        case BinaryExpr.ResolvedOpcode.Le:
          return e0 <= e1;
        case BinaryExpr.ResolvedOpcode.EqCommon:
          return e0 == e1;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          return e0 != e1;
      }
      return null;
    }

    private static object FoldReal(BinaryExpr bin, BaseTypes.BigDec e0, BaseTypes.BigDec e1) {
      var isUnconstrained = AsUnconstrainedType(bin.Type) != null;

      switch (bin.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Add:
          if (isUnconstrained) {
            return e0 + e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (isUnconstrained) {
            return e0 - e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          if (isUnconstrained) {
            return e0 * e1;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
          return e0 > e1;
        case BinaryExpr.ResolvedOpcode.Ge:
          return e0 >= e1;
        case BinaryExpr.ResolvedOpcode.Lt:
          return e0 < e1;
        case BinaryExpr.ResolvedOpcode.Le:
          return e0 <= e1;
        case BinaryExpr.ResolvedOpcode.EqCommon:
          return e0 == e1;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          return e0 != e1;
      }
      return null;
    }

    private static object FoldCharOrString(BinaryExpr bin, string e0, string e1) {
      if (bin.E0.Type.IsCharType) {
        Contract.Assert(bin.E1.Type.IsCharType);
        Contract.Assert(e0.Length == 1);
        Contract.Assert(e1.Length == 1);
      }

      switch (bin.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Concat:
          return e0 + e1;
        case BinaryExpr.ResolvedOpcode.GtChar:
          Contract.Assert(bin.E0.Type.IsCharType);
          return e0[0] > e1[0];
        case BinaryExpr.ResolvedOpcode.GeChar:
          Contract.Assert(bin.E0.Type.IsCharType);
          return e0[0] >= e1[0];
        case BinaryExpr.ResolvedOpcode.LtChar:
          Contract.Assert(bin.E0.Type.IsCharType);
          return e0[0] < e1[0];
        case BinaryExpr.ResolvedOpcode.LeChar:
          Contract.Assert(bin.E0.Type.IsCharType);
          return e0[0] <= e1[0];
        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          return e1.StartsWith(e0) && e0 != e1;;
        case BinaryExpr.ResolvedOpcode.Prefix:
          return e1.StartsWith(e0);
        case BinaryExpr.ResolvedOpcode.EqCommon:
          Contract.Assert(bin.E0.Type.IsCharType); // the string case is handled in SeqEq
          return e0[0] == e1[0];
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          Contract.Assert(bin.E0.Type.IsCharType); // the string case is handled in SeqEq
          return e0[0] != e1[0];
        case BinaryExpr.ResolvedOpcode.SeqEq:
          return e0 == e1;
        case BinaryExpr.ResolvedOpcode.SeqNeq:
          return e0 != e1;
      }
      return null;
    }
  }
}
