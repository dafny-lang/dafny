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
    public static BigInteger MaxBV(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(t.IsBitVectorType);
      return MaxBV(t.AsBitVectorType.Width);
    }

    /// <summary>
    /// Returns the largest value that can be stored in bitvector type of "bits" width.
    /// </summary>
    public static BigInteger MaxBV(int bits) {
      Contract.Requires(0 <= bits);
      return BigInteger.Pow(new BigInteger(2), bits) - BigInteger.One;
    }

    /// <summary>
    /// Folds "e" into an integer literal, if possible.
    /// Returns "null" if not possible (or not easy).
    /// </summary>
    public static BigInteger? GetConst(Expression e) {
      Object ee = GetAnyConst(e.Resolved ?? e, new Stack<ConstantField>());
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

      static object GetAnyConst(Expression e, Stack<ConstantField> consts) {
        if (e is LiteralExpr l) {
          return l.Value;
        } else if (e is UnaryOpExpr un) {
          if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot && GetAnyConst(un.E, consts) is bool b) {
            return !b;
          }
          if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BVNot && GetAnyConst(un.E, consts) is BigInteger i) {
            return ((BigInteger.One << un.Type.AsBitVectorType.Width) - 1) ^ i;
          }
          // TODO: This only handles strings; generalize to other collections?
          if (un.ResolvedOp == UnaryOpExpr.ResolvedOpcode.SeqLength && GetAnyConst(un.E, consts) is string ss) {
            return (BigInteger)(ss.Length);
          }
        } else if (e is MemberSelectExpr m) {
          if (m.Member is ConstantField c && c.IsStatic && c.Rhs != null) {
            // This aspect of type resolution happens before the check for cyclic references
            // so we have to do a check here as well. If cyclic, null is silently returned,
            // counting on the later error message to alert the user.
            if (consts.Contains(c)) { return null; }
            consts.Push(c);
            Object o = GetAnyConst(c.Rhs, consts);
            consts.Pop();
            return o;
          } else if (m.Member is SpecialField sf) {
            string nm = sf.Name;
            if (nm == "Floor") {
              Object ee = GetAnyConst(m.Obj, consts);
              if (ee != null && m.Obj.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
                ((BaseTypes.BigDec)ee).FloorCeiling(out var f, out _);
                return f;
              }
            }
          }
        } else if (e is BinaryExpr bin) {
          Object e0 = GetAnyConst(bin.E0, consts);
          Object e1 = GetAnyConst(bin.E1, consts);
          bool isBool = bin.E0.Type == Type.Bool && bin.E1.Type == Type.Bool;
          bool shortCircuit = isBool && (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And
                                         || bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or
                                         || bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp);

          if (e0 == null || (!shortCircuit && e1 == null)) { return null; }
          bool isAnyReal = bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Real)
                        && bin.E1.Type.IsNumericBased(Type.NumericPersuasion.Real);
          bool isAnyInt = bin.E0.Type.IsNumericBased(Type.NumericPersuasion.Int)
                       && bin.E1.Type.IsNumericBased(Type.NumericPersuasion.Int);
          bool isReal = bin.Type.IsRealType;
          bool isInt = bin.Type.IsIntegerType;
          bool isBV = bin.E0.Type.IsBitVectorType;
          int width = isBV ? bin.E0.Type.AsBitVectorType.Width : 0;
          bool isString = e0 is string && e1 is string;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Add:
              if (isInt) {
                return (BigInteger)e0 + (BigInteger)e1;
              }

              if (isBV) {
                return ((BigInteger)e0 + (BigInteger)e1) & MaxBV(bin.Type);
              }

              if (isReal) {
                return (BaseTypes.BigDec)e0 + (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.Concat:
              if (isString) {
                return (string)e0 + (string)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.Sub:
              if (isInt) {
                return (BigInteger)e0 - (BigInteger)e1;
              }

              if (isBV) {
                return ((BigInteger)e0 - (BigInteger)e1) & MaxBV(bin.Type);
              }

              if (isReal) {
                return (BaseTypes.BigDec)e0 - (BaseTypes.BigDec)e1;
              }
              // Allow a special case: If the result type is a newtype that is integer-based (i.e., isInt && !isInteger)
              // then we generally do not fold the operations, because we do not determine whether the
              // result of the operation satisfies the new type constraint. However, on the occasion that
              // a newtype aliases int without a constraint, it occurs that a value of the newtype is initialized
              // with a negative value, which is represented as "0 - N", that is, it comes to this case. It
              // is a nuisance not to constant-fold the result, as not doing so can alter the determination
              // of the representation type.
              if (isAnyInt && AsUnconstrainedType(bin.Type) != null) {
                return ((BigInteger)e0) - ((BigInteger)e1);
              }
              break;
            case BinaryExpr.ResolvedOpcode.Mul:
              if (isInt) {
                return (BigInteger)e0 * (BigInteger)e1;
              }

              if (isBV) {
                return ((BigInteger)e0 * (BigInteger)e1) & MaxBV(bin.Type);
              }

              if (isReal) {
                return (BaseTypes.BigDec)e0 * (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.BitwiseAnd:
              Contract.Assert(isBV);
              return (BigInteger)e0 & (BigInteger)e1;
            case BinaryExpr.ResolvedOpcode.BitwiseOr:
              Contract.Assert(isBV);
              return (BigInteger)e0 | (BigInteger)e1;
            case BinaryExpr.ResolvedOpcode.BitwiseXor:
              Contract.Assert(isBV);
              return (BigInteger)e0 ^ (BigInteger)e1;
            case BinaryExpr.ResolvedOpcode.Div:
              if (isInt) {
                if ((BigInteger)e1 == 0) {
                  return null; // Divide by zero
                } else {
                  BigInteger a0 = (BigInteger)e0;
                  BigInteger a1 = (BigInteger)e1;
                  BigInteger d = a0 / a1;
                  return a0 >= 0 || a0 == d * a1 ? d : a1 > 0 ? d - 1 : d + 1;
                }
              }
              if (isBV) {
                if ((BigInteger)e1 == 0) {
                  return null; // Divide by zero
                } else {
                  return ((BigInteger)e0) / ((BigInteger)e1);
                }
              }
              if (isReal) {
                if ((BaseTypes.BigDec)e1 == BaseTypes.BigDec.ZERO) {
                  return null; // Divide by zero
                } else {
                  // BigDec does not have divide and is not a representation of rationals, so we don't do constant folding
                  return null;
                }
              }

              break;
            case BinaryExpr.ResolvedOpcode.Mod:
              if (isInt) {
                if ((BigInteger)e1 == 0) {
                  return null; // Mod by zero
                } else {
                  BigInteger a = BigInteger.Abs((BigInteger)e1);
                  BigInteger d = (BigInteger)e0 % a;
                  return (BigInteger)e0 >= 0 ? d : d + a;
                }
              }
              if (isBV) {
                if ((BigInteger)e1 == 0) {
                  return null; // Mod by zero
                } else {
                  return (BigInteger)e0 % (BigInteger)e1;
                }
              }
              break;
            case BinaryExpr.ResolvedOpcode.LeftShift: {
                if ((BigInteger)e1 < 0) {
                  return null; // Negative shift
                }
                if ((BigInteger)e1 > bin.Type.AsBitVectorType.Width) {
                  return null; // Shift is too large
                }
                return ((BigInteger)e0 << (int)(BigInteger)e1) & MaxBV(bin.E0.Type);
              }
            case BinaryExpr.ResolvedOpcode.RightShift: {
                if ((BigInteger)e1 < 0) {
                  return null; // Negative shift
                }
                if ((BigInteger)e1 > bin.Type.AsBitVectorType.Width) {
                  return null; // Shift too large
                }
                return (BigInteger)e0 >> (int)(BigInteger)e1;
              }
            case BinaryExpr.ResolvedOpcode.And: {
                if ((bool)e0 && e1 == null) {
                  return null;
                }

                return (bool)e0 && (bool)e1;
              }
            case BinaryExpr.ResolvedOpcode.Or: {
                if (!(bool)e0 && e1 == null) {
                  return null;
                }

                return (bool)e0 || (bool)e1;
              }
            case BinaryExpr.ResolvedOpcode.Imp: { // ==> and <==
                if ((bool)e0 && e1 == null) {
                  return null;
                }

                return !(bool)e0 || (bool)e1;
              }
            case BinaryExpr.ResolvedOpcode.Iff: return (bool)e0 == (bool)e1; // <==>
            case BinaryExpr.ResolvedOpcode.Gt:
              if (isAnyInt) {
                return (BigInteger)e0 > (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 > (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 > (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.GtChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] > ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.Ge:
              if (isAnyInt) {
                return (BigInteger)e0 >= (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 >= (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 >= (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.GeChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] >= ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.Lt:
              if (isAnyInt) {
                return (BigInteger)e0 < (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 < (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 < (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.LtChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] < ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.ProperPrefix:
              if (isString) {
                return ((string)e1).StartsWith((string)e0) && !((string)e1).Equals((string)e0);
              }

              break;
            case BinaryExpr.ResolvedOpcode.Le:
              if (isAnyInt) {
                return (BigInteger)e0 <= (BigInteger)e1;
              }

              if (isBV) {
                return (BigInteger)e0 <= (BigInteger)e1;
              }

              if (isAnyReal) {
                return (BaseTypes.BigDec)e0 <= (BaseTypes.BigDec)e1;
              }

              break;
            case BinaryExpr.ResolvedOpcode.LeChar:
              if (bin.E0.Type.IsCharType) {
                return ((string)e0)[0] <= ((string)e1)[0];
              }

              break;
            case BinaryExpr.ResolvedOpcode.Prefix:
              if (isString) {
                return ((string)e1).StartsWith((string)e0);
              }

              break;
            case BinaryExpr.ResolvedOpcode.EqCommon: {
                if (isBool) {
                  return (bool)e0 == (bool)e1;
                } else if (isAnyInt || isBV) {
                  return (BigInteger)e0 == (BigInteger)e1;
                } else if (isAnyReal) {
                  return (BaseTypes.BigDec)e0 == (BaseTypes.BigDec)e1;
                } else if (bin.E0.Type.IsCharType) {
                  return ((string)e0)[0] == ((string)e1)[0];
                }
                break;
              }
            case BinaryExpr.ResolvedOpcode.SeqEq:
              if (isString) {
                return (string)e0 == (string)e1;
              }
              break;
            case BinaryExpr.ResolvedOpcode.SeqNeq:
              if (isString) {
                return (string)e0 != (string)e1;
              }
              break;
            case BinaryExpr.ResolvedOpcode.NeqCommon: {
                if (isBool) {
                  return (bool)e0 != (bool)e1;
                } else if (isAnyInt || isBV) {
                  return (BigInteger)e0 != (BigInteger)e1;
                } else if (isAnyReal) {
                  return (BaseTypes.BigDec)e0 != (BaseTypes.BigDec)e1;
                } else if (bin.E0.Type.IsCharType) {
                  return ((string)e0)[0] != ((string)e1)[0];
                } else if (isString) {
                  return (string)e0 != (string)e1;
                }
                break;
              }
          }
        } else if (e is ConversionExpr ce) {
          object o = GetAnyConst(ce.E, consts);
          if (o == null || ce.E.Type == ce.Type) {
            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsBitVectorType) {
            ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
            if (ff < 0 || ff > MaxBV(ce.Type)) {
              return null; // Out of range
            }
            if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
              return null; // Out of range
            }
            return ff;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            ((BaseTypes.BigDec)o).FloorCeiling(out var ff, out _);
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            if (((BaseTypes.BigDec)o) != BaseTypes.BigDec.FromBigInt(ff)) {
              return null; // Argument not an integer
            }
            return ff;
          }

          if (ce.E.Type.IsBitVectorType &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return o;
          }

          if (ce.E.Type.IsBitVectorType &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return BaseTypes.BigDec.FromBigInt((BigInteger)o);
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) &&
                ce.Type.IsBitVectorType) {
            BigInteger b = (BigInteger)o;
            if (b < 0 || b > MaxBV(ce.Type)) {
              return null; // Argument out of range
            }
            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            // This case includes int-based newtypes to int-based new types
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            // This case includes real-based newtypes to real-based new types
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return o;
          }

          if (ce.E.Type.IsBitVectorType && ce.Type.IsBitVectorType) {
            BigInteger b = (BigInteger)o;
            if (b < 0 || b > MaxBV(ce.Type)) {
              return null; // Argument out of range
            }
            return o;
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) &&
                ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return BaseTypes.BigDec.FromBigInt((BigInteger)o);
          }

          if (ce.E.Type.IsCharType && ce.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
            char c = ((String)o)[0];
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return new BigInteger(((string)o)[0]);
          }

          if (ce.E.Type.IsCharType && ce.Type.IsBitVectorType) {
            char c = ((String)o)[0];
            if ((int)c > MaxBV(ce.Type)) {
              return null; // Argument out of range
            }
            return new BigInteger(((string)o)[0]);
          }

          if ((ce.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || ce.E.Type.IsBitVectorType) &&
                ce.Type.IsCharType) {
            BigInteger b = (BigInteger)o;
            if (b < BigInteger.Zero || b > new BigInteger(65535)) {
              return null; // Argument out of range
            }
            return ((char)(int)b).ToString();
          }

          if (ce.E.Type.IsCharType &&
              ce.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            if (AsUnconstrainedType(ce.Type) == null) {
              return null;
            }

            return BaseTypes.BigDec.FromInt(((string)o)[0]);
          }

          if (ce.E.Type.IsNumericBased(Type.NumericPersuasion.Real) &&
                ce.Type.IsCharType) {
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
          var b = GetAnyConst(sse.Seq, consts) as string;
          BigInteger index = (BigInteger)GetAnyConst(sse.E0, consts);
          if (b == null) {
            return null;
          }

          if (index < 0 || index >= b.Length || index > Int32.MaxValue) {
            return null; // Index out of range
          }
          return b[(int)index].ToString();
        } else if (e is ITEExpr ite) {
          Object b = GetAnyConst(ite.Test, consts);
          if (b == null) {
            return null;
          }

          return ((bool)b) ? GetAnyConst(ite.Thn, consts) : GetAnyConst(ite.Els, consts);
        } else if (e is ConcreteSyntaxExpression n) {
          return GetAnyConst(n.ResolvedExpression, consts);
        } else {
          return null;
        }
        return null;
      }
  }
}
