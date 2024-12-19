// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace ExpressionOptimization {

  public partial class __default {
    public static RAST._IMod apply(RAST._IMod mod) {
      return (ExpressionOptimization.__default.ExprSimplifier()).ReplaceMod(mod, (RAST.__default.crate).MSel((mod).dtor_name));
    }
    public static RAST._IRASTBottomUpReplacer ExprSimplifier() {
      return RAST.RASTBottomUpReplacer.create(((System.Func<RAST._IMod, RAST._IPath, RAST._IMod>)((_0_m, _1_SelfPath) => {
  return _0_m;
})), ((System.Func<RAST._IType, RAST._IType>)((_2_t) => {
  return _2_t;
})), ((System.Func<RAST._IExpr, RAST._IExpr>)((_3_e) => {
  return ((System.Func<RAST._IExpr>)(() => {
    RAST._IExpr _source0 = _3_e;
    {
      if (_source0.is_UnaryOp) {
        Dafny.ISequence<Dafny.Rune> op10 = _source0.dtor_op1;
        if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
          RAST._IExpr underlying0 = _source0.dtor_underlying;
          if (underlying0.is_BinaryOp) {
            Dafny.ISequence<Dafny.Rune> _4_op = underlying0.dtor_op2;
            RAST._IExpr _5_left = underlying0.dtor_left;
            RAST._IExpr _6_right = underlying0.dtor_right;
            DAST.Format._IBinaryOpFormat _7_format = underlying0.dtor_format2;
            DAST.Format._IUnaryOpFormat format0 = _source0.dtor_format;
            if (format0.is_CombineFormat) {
              Dafny.ISequence<Dafny.Rune> _source1 = _4_op;
              {
                if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
                  return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="), _5_left, _6_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
              {
                if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
                  if ((_7_format).is_NoFormat) {
                    return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="), _5_left, _6_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  } else if ((_7_format).is_ReverseFormat) {
                    return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _6_right, _5_left, DAST.Format.BinaryOpFormat.create_NoFormat());
                  } else {
                    return _3_e;
                  }
                }
              }
              {
                return _3_e;
              }
            }
          }
        }
      }
    }
    {
      if (_source0.is_Call) {
        RAST._IExpr obj0 = _source0.dtor_obj;
        if (obj0.is_ExprFromPath) {
          RAST._IPath path0 = obj0.dtor_path;
          if (path0.is_PMemberSelect) {
            RAST._IPath _8_r = path0.dtor_base;
            Dafny.ISequence<Dafny.Rune> name0 = path0.dtor_name;
            if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))) {
              Dafny.ISequence<RAST._IExpr> _9_args = _source0.dtor_arguments;
              if (((!object.Equals(_8_r, RAST.__default.dafny__runtime)) && (!object.Equals(_8_r, RAST.__default.@global))) || ((new BigInteger((_9_args).Count)) != (new BigInteger(2)))) {
                return _3_e;
              } else {
                RAST._IExpr _10_expr = (_9_args).Select(BigInteger.Zero);
                RAST._IExpr _11_tpeExpr = (_9_args).Select(BigInteger.One);
                if (!((_11_tpeExpr).is_ExprFromType)) {
                  return _3_e;
                } else {
                  RAST._IType _12_tpe = (_11_tpeExpr).dtor_tpe;
                  if ((_12_tpe).IsAutoSize()) {
                    RAST._IExpr _source2 = _10_expr;
                    {
                      if (_source2.is_Call) {
                        RAST._IExpr obj1 = _source2.dtor_obj;
                        if (obj1.is_ExprFromPath) {
                          RAST._IPath path1 = obj1.dtor_path;
                          if (path1.is_PMemberSelect) {
                            RAST._IPath _13_base = path1.dtor_base;
                            Dafny.ISequence<Dafny.Rune> name1 = path1.dtor_name;
                            if (object.Equals(name1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))) {
                              Dafny.ISequence<RAST._IExpr> _14_args = _source2.dtor_arguments;
                              if (((new BigInteger((_14_args).Count)) == (BigInteger.One)) && ((object.Equals(_13_base, RAST.__default.dafny__runtime)) || (object.Equals(_13_base, RAST.__default.@global)))) {
                                RAST._IExpr _source3 = (_14_args).Select(BigInteger.Zero);
                                {
                                  if (_source3.is_LiteralInt) {
                                    Dafny.ISequence<Dafny.Rune> _15_number = _source3.dtor_value;
                                    return RAST.Expr.create_LiteralInt(_15_number);
                                  }
                                }
                                {
                                  if (_source3.is_LiteralString) {
                                    Dafny.ISequence<Dafny.Rune> _16_number = _source3.dtor_value;
                                    return RAST.Expr.create_LiteralInt(_16_number);
                                  }
                                }
                                {
                                  return _3_e;
                                }
                              } else {
                                return _3_e;
                              }
                            }
                          }
                        }
                      }
                    }
                    {
                      return _3_e;
                    }
                  } else {
                    return _3_e;
                  }
                }
              }
            }
          }
        }
      }
    }
    {
      if (_source0.is_StmtExpr) {
        RAST._IExpr stmt0 = _source0.dtor_stmt;
        if (stmt0.is_DeclareVar) {
          RAST._IDeclareType _17_mod = stmt0.dtor_declareType;
          Dafny.ISequence<Dafny.Rune> _18_name = stmt0.dtor_name;
          Std.Wrappers._IOption<RAST._IType> optType0 = stmt0.dtor_optType;
          if (optType0.is_Some) {
            RAST._IType _19_tpe = optType0.dtor_value;
            Std.Wrappers._IOption<RAST._IExpr> optRhs0 = stmt0.dtor_optRhs;
            if (optRhs0.is_None) {
              RAST._IExpr rhs0 = _source0.dtor_rhs;
              if (rhs0.is_StmtExpr) {
                RAST._IExpr stmt1 = rhs0.dtor_stmt;
                if (stmt1.is_Assign) {
                  Std.Wrappers._IOption<RAST._IAssignLhs> _20_name2 = stmt1.dtor_names;
                  RAST._IExpr _21_rhs = stmt1.dtor_rhs;
                  RAST._IExpr _22_last = rhs0.dtor_rhs;
                  if (object.Equals(_20_name2, Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_LocalVar(_18_name)))) {
                    return RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(_17_mod, _18_name, Std.Wrappers.Option<RAST._IType>.create_Some(_19_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_21_rhs)), _22_last);
                  } else {
                    return _3_e;
                  }
                }
              }
            }
          }
        }
      }
    }
    {
      return _3_e;
    }
  }))();
})));
    }
  }
} // end of namespace ExpressionOptimization